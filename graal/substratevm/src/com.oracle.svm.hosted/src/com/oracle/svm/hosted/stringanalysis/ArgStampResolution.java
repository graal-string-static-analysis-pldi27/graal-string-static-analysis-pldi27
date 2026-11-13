/*
 * Copyright (c) 2026, 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.svm.hosted.stringanalysis;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;

import jdk.graal.compiler.core.common.type.ObjectStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.NewArrayNode;
import jdk.graal.compiler.nodes.java.NewInstanceNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The arg-position receiver-stamp resolution: the pure-IR may-stamp of a virtual invoke's dispatch receiver, collected
 * in the same IR pass that builds the LFGs and used by {@code ForwardFixpoint.filterTargetsByArgStamp} to shrink the
 * arg-position consult's CHA fan to the targets the provable receiver cone can dispatch to.
 *
 * <p><b>May-stamp discipline (the soundness core).</b> A stamp is a set of cone roots: root R means "the runtime
 * receiver type is R or an instantiated subtype of R" (the cone semantics
 * {@code DispatchResolution.computeDeterministicChaTargets} gives the declared receiver; a stamp is only a narrower
 * declared-type cone). A ⊤/empty stamp ({@code null}) keeps the full fan. Roots derive from:
 * <ul>
 * <li>allocations ({@code new X()}, {@code new X[n]}, virtualized): the exact type;</li>
 * <li>pi chains: the pi's {@link ObjectStamp} is an invariant at that point; the pair rule keeps the more specific of
 * pi stamp and original root, and an unresolvable original still yields the pi stamp alone;</li>
 * <li>field loads: the union of every writer store's stored-value cones (below);</li>
 * <li>anything else: the node's own {@link ObjectStamp} type, a sound Graal invariant (the filter also caps every root
 * by the declared receiver cone, so a wider root means no gain, never fan growth).</li>
 * </ul>
 *
 * <p><b>Field-writer completeness.</b> In the closed world, a field slot holds a value written by a store that
 * executed (at image build or run time) or the default null. The field-grain write channels are exactly
 * {@code MethodTypeFlowBuilder.processStoreField}'s input kinds, and {@link #collect} enumerates every one of them from
 * the decoded graphs. Every other write channel (reflective {@code Field.set}, VarHandle, atomic updaters,
 * feature-injected, substitution-target, image-layer fields) is flagged by points-to via
 * {@code registerAsUnsafeAccessed}; a flagged field is ⊤. A field with no enumerated writer is ⊤ (the fully-virtualized
 * corner), and so is a field with any unresolvable writer. A value the field holds in the image heap has no parsed
 * writer: a static field of a class initialized (or simulated) at build time, an instance field of a class with an
 * image-heap instance, and a field with a value transformer or computer are ⊤. Computed/unknown-offset unsafe stores
 * are not field-grain writes (the heap model's {@code unsafeAccessedFields} routing and the offset-registration flag
 * cover their flagged forms; the unflagged residue is the engine-wide closed-world floor, as for the hub join). JNI
 * writes stand outside the closed world, as for the hub join. The stamp is only ever a sound may-set or nothing.
 *
 * <p><b>Determinism.</b> Collected shapes are pure functions of each decoded graph (cross-field references are deferred
 * as {@link AnalysisField} refs); finalize resolves refs serially over the complete index, cycles resolve to ⊤ in every
 * query order and non-cyclic unions are order-free. The flags read ({@code isAnySubtypeInstantiated},
 * unsafe-access) are the settled, structural ones.
 */
final class ArgStampResolution {

    /** The owning builder (field/type resolution). */
    private final SugBuilderV2 builder;

    /** field → every writer store's raw shape (union = the field's may-stamp). */
    private final Map<AnalysisField, List<Shape>> writers = new HashMap<>();
    /** finalize memo: field → resolved cone roots, or null-valued entry = ⊤. */
    private final Map<AnalysisField, Set<AnalysisType>> fieldConeMemo = new HashMap<>();
    private boolean finalized;

    /**
     * Set when collection failed or a store's field was unresolvable: a writer may be missing from the index, and the
     * missing writer's field is unknown, so every query is ⊤.
     */
    private boolean collectPoisoned;

    /**
     * The classes that declare the instance fields of image-heap objects (each heap type and its superclasses); null =
     * unavailable.
     */
    private Set<AnalysisType> heapFieldOwners;
    private boolean heapFieldOwnersLooked;
    private int heapTopStatic;
    private int heapTopInstance;
    private int heapTopIntercepted;
    private int interceptorUnlooked;

    ArgStampResolution(SugBuilderV2 builder) {
        this.builder = builder;
    }

    /**
     * A raw may-stamp shape: cone roots, deferred field references, and deferred pi narrowings ({@code narrowBy},
     * pair-intersected at resolution). Collection never resolves refs: the writer index is partial until the pass
     * completes, so an early resolution would be unsound and order-dependent. {@code top} dominates. Immutable.
     */
    static final class Shape {
        static final Shape TOP = new Shape(null, null, null, true);

        final Set<AnalysisType> coneRoots;
        final Set<AnalysisField> fieldRefs;
        final Set<AnalysisType> narrowBy;
        final boolean top;

        private Shape(Set<AnalysisType> coneRoots, Set<AnalysisField> fieldRefs, Set<AnalysisType> narrowBy, boolean top) {
            this.coneRoots = coneRoots;
            this.fieldRefs = fieldRefs;
            this.narrowBy = narrowBy;
            this.top = top;
        }

        static Shape cone(AnalysisType type) {
            Set<AnalysisType> roots = new LinkedHashSet<>(2);
            roots.add(type);
            return new Shape(roots, Set.of(), Set.of(), false);
        }

        static Shape fieldRef(AnalysisField field) {
            Set<AnalysisField> refs = new LinkedHashSet<>(2);
            refs.add(field);
            return new Shape(Set.of(), refs, Set.of(), false);
        }

        static Shape narrowed(Shape base, AnalysisType piType) {
            if (base.top) {
                return cone(piType); // the pi stamp alone is a sound invariant
            }
            Set<AnalysisType> narrowing = new LinkedHashSet<>(base.narrowBy);
            narrowing.add(piType);
            return new Shape(base.coneRoots, base.fieldRefs, narrowing, false);
        }

        /** The phi/copy union: any ⊤ input is ⊤ (narrowings are per-path — drop on union). */
        static Shape union(Shape a, Shape b) {
            if (a.top || b.top) {
                return TOP;
            }
            Set<AnalysisType> cones = new LinkedHashSet<>(a.coneRoots);
            cones.addAll(b.coneRoots);
            Set<AnalysisField> refs = new LinkedHashSet<>(a.fieldRefs);
            refs.addAll(b.fieldRefs);
            return new Shape(cones, refs, Set.of(), false);
        }

        @Override
        public String toString() {
            if (top) {
                return "TOP";
            }
            StringBuilder sb = new StringBuilder("cone={");
            for (AnalysisType t : coneRoots) {
                sb.append(t.toJavaName(true)).append(' ');
            }
            sb.append("} refs={");
            for (AnalysisField f : fieldRefs) {
                sb.append(f.format("%H.%n")).append(' ');
            }
            sb.append("} narrowBy={");
            for (AnalysisType t : narrowBy) {
                sb.append(t.toJavaName(true)).append(' ');
            }
            return sb.append("}").toString();
        }
    }

    /**
     * The per-method collection (on the LFG pass, graph decoded): every field-grain write channel into the writer
     * index. Each input kind of {@code MethodTypeFlowBuilder.processStoreField} is enumerated by exactly one arm:
     * <ul>
     * <li>{@link StoreFieldNode}: putfield/putstatic, plus every modeled {@code RawStoreNode} that
     * {@code UnsafeAccessNode.canonical → cloneAsFieldAccess} already folded;</li>
     * <li>a surviving {@code RawStoreNode} with a {@link FieldOffsetProvider} offset (the belt for stores that did not
     * fold);</li>
     * <li>{@code AbstractUnsafeCompareAndSwapNode} and {@code AtomicReadAndWriteNode} with a {@link FieldOffsetProvider}
     * offset: modeled by points-to ({@code modelUnsafeWriteOnlyFlow}/{@code modelUnsafeReadAndWriteFlow} →
     * {@code processStoreField}) but not canonicalized (they extend {@code AbstractMemoryCheckpoint}, not
     * {@code UnsafeAccessNode}) and not flagged ({@code needsUnsafeRegistration} exempts modeled usages), so enumerated
     * here with the new value's shape (a CAS is a may-write, which a may-stamp unions anyway);</li>
     * <li>{@code AtomicReadAndAddNode} with a {@link FieldOffsetProvider} offset: primitive deltas only, enumerated as
     * ⊤;</li>
     * <li>{@code CommitAllocationNode}: a field whose only surviving store came from a putfield in a method never parsed
     * standalone (inlined, PEA-virtualized, materialized in the caller's commit) is written here; the walk mirrors
     * {@code processCommitAllocation}'s field/value pairing.</li>
     * </ul>
     * Non-{@link FieldOffsetProvider} offsets are not field-grain writes: the heap model routes them through
     * {@code unsafeAccessedFields}, and an unmodeled offset usage flags the field ({@code needsUnsafeRegistration} →
     * {@code isUnsafeAccessed} → ⊤ here).
     */
    void collect(AnalysisMethod method, StructuredGraph ir) {
        if (ir == null) {
            collectNullIr++; // counted only (census): such a method's stores are not in the index
            return;
        }
        // Recursive tracking's image-wide index (static-field accessors, image-heap constant users), recorded while
        // the graph is decoded; the tables are built lazily from it.
        rtrackIndexScan(method, ir);
        try {
            for (Node n : ir.getNodes()) {
                try {
                    collectStoreChannel(ir, n);
                } catch (Throwable tv) {
                    // A writer may be lost: every query is ⊤ (the remaining nodes are still collected).
                    collectFailures++;
                    collectPoisoned = true;
                }
            }
        } catch (Throwable t) {
            // The remaining nodes are lost: every query is ⊤.
            collectFailures++;
            collectPoisoned = true;
        }
    }

    /** One node's write-channel enumeration (the caller counts a failure and continues). */
    private void collectStoreChannel(StructuredGraph ir, Node n) {
        if (n instanceof StoreFieldNode sfn) {
            AnalysisField f = builder.lfgWalk.resolveAnalysisField(sfn.field());
            if (f == null) {
                collectPoisoned = true; // an unknown field's writer: every query is ⊤
                return;
            }
            addWriter(f, ir, "putfield", sfn.value());
        } else if (n instanceof jdk.graal.compiler.nodes.extended.RawStoreNode rsn) {
            // The belt: a modeled store that survived uncanonicalized.
            AnalysisField f = fieldOffsetTarget(rsn.offset());
            if (f != null) {
                addWriter(f, ir, "rawstore", rsn.value());
            }
        } else if (n instanceof jdk.graal.compiler.nodes.java.AbstractUnsafeCompareAndSwapNode cas) {
            // compareAndSet/compareAndExchange: a may-write of newValue.
            AnalysisField f = fieldOffsetTarget(cas.offset());
            if (f != null) {
                addWriter(f, ir, "cas", cas.newValue());
            }
        } else if (n instanceof jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode arw) {
            // getAndSet.
            AnalysisField f = fieldOffsetTarget(arw.offset());
            if (f != null) {
                addWriter(f, ir, "getandset", arw.newValue());
            }
        } else if (n instanceof jdk.graal.compiler.nodes.java.AtomicReadAndAddNode ara) {
            // Primitive deltas only: ⊤, never shaped.
            AnalysisField f = fieldOffsetTarget(ara.offset());
            if (f != null) {
                writers.computeIfAbsent(f, k -> new ArrayList<>(2)).add(Shape.TOP);
            }
        } else if (n instanceof jdk.graal.compiler.nodes.virtual.CommitAllocationNode commit) {
            // Virtualized-materialization stores, paired as in processCommitAllocation (defensively: type() is
            // nullable).
            List<ValueNode> values = commit.getValues();
            int objectStartIndex = 0;
            for (jdk.graal.compiler.nodes.virtual.VirtualObjectNode virtualObject : commit.getVirtualObjects()) {
                if (virtualObject.type() != null && !virtualObject.type().isArray() &&
                                virtualObject instanceof jdk.graal.compiler.nodes.virtual.VirtualInstanceNode instance) {
                    for (int i = 0; i < instance.entryCount(); i++) {
                        Object field = instance.field(i);
                        if (field instanceof AnalysisField f && objectStartIndex + i < values.size()) {
                            addWriter(f, ir, "commit", values.get(objectStartIndex + i));
                        }
                    }
                }
                objectStartIndex += virtualObject.entryCount();
            }
        }
    }

    /**
     * Adds one writer entry. An always-null stored value contributes no entry: null is never a dispatch receiver (the
     * invoke would NPE before dispatching), so a null write adds nothing to the may-stamp (e.g. a
     * {@code CommitAllocationNode} field entry that is the null constant).
     */
    private void addWriter(AnalysisField f, StructuredGraph ir, String channel, ValueNode value) {
        if (value == null) {
            writers.computeIfAbsent(f, k -> new ArrayList<>(2)).add(Shape.TOP);
            return;
        }
        if (isAlwaysNull(value)) {
            return; // a null write: no receiver type, no entry
        }
        Shape shape = resolveNode(ir, value, MAX_CHAIN_DEPTH, new HashSet<>(), new ArrayDeque<>());
        writers.computeIfAbsent(f, k -> new ArrayList<>(2)).add(shape);
    }

    /** Whether the node's stamp provably carries only null ({@code ConstantNode(null)} or an always-null ObjectStamp). */
    private static boolean isAlwaysNull(ValueNode value) {
        try {
            Stamp stamp = value.stamp(NodeView.DEFAULT);
            if (stamp instanceof ObjectStamp os && os.alwaysNull()) {
                return true;
            }
        } catch (Throwable ignore) {
            return false;
        }
        return false;
    }

    /** The field an unsafe-family write targets via a {@link FieldOffsetProvider} offset; null otherwise (not field-grain). */
    private static AnalysisField fieldOffsetTarget(ValueNode offset) {
        if (offset instanceof jdk.graal.compiler.nodes.extended.FieldOffsetProvider fop &&
                        fop.getField() instanceof AnalysisField f) {
            return f;
        }
        return null;
    }

    private int collectFailures;
    private int collectNullIr;

    /** Knob {@code argstamp.depth} (default 8): the SSA-chain resolution bound; a deeper chain is ⊤. */
    private static final int MAX_CHAIN_DEPTH = Integer.getInteger("svm.stringanalysis.argstamp.depth", 8);

    /** The in-frame receiver/stored-value resolution: cycle-guarded, depth-bounded; anything unresolvable is ⊤. */
    private Shape resolveNode(StructuredGraph ir, ValueNode node, int depth, Set<Node> seen, Deque<AnalysisField> chain) {
        if (node == null || depth <= 0 || !seen.add(node)) {
            return Shape.TOP;
        }
        try {
            if (node instanceof NewInstanceNode nin) {
                AnalysisType t = builder.resolveAnalysisType(nin.instanceClass());
                return t != null ? Shape.cone(t) : Shape.TOP;
            }
            if (node instanceof NewArrayNode nan) {
                ResolvedJavaType et = nan.elementType();
                if (et != null) {
                    AnalysisType t = builder.resolveAnalysisType(et);
                    if (t != null) {
                        try {
                            Object arr = t.getArrayClass();
                            if (arr instanceof AnalysisType at) {
                                return Shape.cone(at);
                            }
                        } catch (Throwable ignore) {
                            // fall through to ⊤
                        }
                    }
                }
                return Shape.TOP;
            }
            if (node instanceof AllocatedObjectNode aon && aon.getVirtualObject() != null &&
                            aon.getVirtualObject().type() != null) {
                AnalysisType t = builder.resolveAnalysisType(aon.getVirtualObject().type());
                return t != null ? Shape.cone(t) : Shape.TOP;
            }
            if (node instanceof PiNode pi) {
                Shape inner = resolveNode(ir, pi.getOriginalNode(), depth - 1, seen, chain);
                AnalysisType piType = objectStampType(pi);
                if (piType == null) {
                    return inner;
                }
                if (inner.top || (inner.coneRoots.isEmpty() && inner.fieldRefs.isEmpty())) {
                    // The pi stamp alone is an invariant, even when the original is unresolvable.
                    return Shape.cone(piType);
                }
                // Defer the narrowing: refs resolve only over the complete writer index.
                return Shape.narrowed(inner, piType);
            }
            if (node instanceof PhiNode phi) {
                Shape acc = null;
                for (ValueNode in : phi.values()) {
                    Shape inShape = resolveNode(ir, in, depth - 1, seen, chain);
                    acc = acc == null ? inShape : Shape.union(acc, inShape);
                    if (acc.top) {
                        return Shape.TOP;
                    }
                }
                return acc == null ? Shape.TOP : acc;
            }
            if (node instanceof LoadFieldNode lfn) {
                AnalysisField f = builder.lfgWalk.resolveAnalysisField(lfn.field());
                return f != null ? Shape.fieldRef(f) : Shape.TOP;
            }
            if (node instanceof jdk.graal.compiler.replacements.nodes.ObjectClone oc) {
                // clone() preserves the source's runtime type exactly.
                return resolveNode(ir, oc.getObject(), depth - 1, seen, chain);
            }
            // Fallback (params, invoke results, array loads, ...): the node's own ObjectStamp type.
            AnalysisType t = objectStampType(node);
            return t != null ? Shape.cone(t) : Shape.TOP;
        } catch (Throwable tv) {
            return Shape.TOP;
        } finally {
            seen.remove(node);
        }
    }

    /** The node's {@link ObjectStamp} type as an {@link AnalysisType}, or null. */
    private AnalysisType objectStampType(ValueNode node) {
        try {
            Stamp stamp = node.stamp(NodeView.DEFAULT);
            if (stamp instanceof ObjectStamp os && os.type() != null) {
                return builder.resolveAnalysisType(os.type());
            }
        } catch (Throwable ignore) {
            // fall through
        }
        return null;
    }

    /**
     * The pair rule: cone(a) ∩ cone(b) at the root grain, the more specific root when the cones nest, null when
     * disjoint (the caller drops the pair; an all-dead resolution is ⊤, never an empty fan).
     */
    private static AnalysisType moreSpecific(AnalysisType a, AnalysisType b) {
        if (a.equals(b) || a.isAssignableFrom(b)) {
            return b; // b ⊆ a
        }
        if (b.isAssignableFrom(a)) {
            return a; // a ⊆ b
        }
        return null; // disjoint
    }

    /**
     * The finalize pass (serial, after all collection): resolves every written field's cone over the complete writer
     * index, in canonical order, into the memo {@link #stampOfUnregisteredInvoke} reads.
     */
    void finalizeIndex() {
        if (finalized) {
            return;
        }
        finalized = true;
        List<AnalysisField> fields = new ArrayList<>(writers.keySet());
        fields.sort((x, y) -> Long.compare(x.getId(), y.getId()));
        for (AnalysisField f : fields) {
            fieldWriterCone(f, new ArrayDeque<>());
        }
        writers.clear();
        // Census (print-only): heapTop = fields the image-heap rule made ⊤ so far (Intercepted: by the interceptor alone).
        String owners = !heapFieldOwnersLooked ? "unlooked" : heapFieldOwners == null ? "unavailable" : String.valueOf(heapFieldOwners.size());
        System.out.println("[argstamp] heapTopStatic=" + heapTopStatic + " heapTopInstance=" + heapTopInstance + " heapTopIntercepted=" +
                        heapTopIntercepted + " interceptorUnlooked=" + interceptorUnlooked + " heapOwners=" + owners + " poisoned=" + collectPoisoned +
                        " collectFailures=" + collectFailures + " nullIr=" + collectNullIr);
    }

    /**
     * The arg-position receiver stamp of an invoke ({@code RecursiveTracking.callVertexOf}): the in-frame receiver
     * shape with its field refs resolved through the writer cones. Evaluated after finalize, so it is a pure function
     * of the IR and the closed-world writer index. ⊤ = null (keep the fan). Leaf lock.
     */
    synchronized Set<AnalysisType> stampOfUnregisteredInvoke(Invoke inv) {
        if (!finalized || inv == null || collectPoisoned) {
            return null;
        }
        try {
            ValueNode receiver = inv.callTarget() instanceof MethodCallTargetNode mctn ? mctn.receiver() : null;
            StructuredGraph ir = inv.asNode().graph();
            if (receiver == null || ir == null) {
                return null;
            }
            Shape shape = resolveNode(ir, receiver, MAX_CHAIN_DEPTH, new HashSet<>(), new ArrayDeque<>());
            Set<AnalysisType> roots = resolveShapeRoots(shape, new ArrayDeque<>());
            return roots == null || roots.isEmpty() ? null : roots;
        } catch (Throwable t) {
            return null; // ⊤
        }
    }

    /**
     * A shape's cone roots: direct roots plus every field ref's writer cone, then the deferred pi narrowings (pair
     * rule). A ⊤ anywhere, an all-dead narrowing or an empty result is null (⊤).
     */
    private Set<AnalysisType> resolveShapeRoots(Shape shape, Deque<AnalysisField> chain) {
        if (shape.top) {
            return null;
        }
        Set<AnalysisType> acc = new LinkedHashSet<>(shape.coneRoots);
        for (AnalysisField ref : shape.fieldRefs) {
            Set<AnalysisType> cone = fieldWriterCone(ref, chain);
            if (cone == null) {
                return null;
            }
            acc.addAll(cone);
        }
        if (acc.isEmpty()) {
            return null;
        }
        for (AnalysisType piType : shape.narrowBy) {
            Set<AnalysisType> narrowed = new LinkedHashSet<>(acc.size());
            for (AnalysisType root : acc) {
                AnalysisType kept = moreSpecific(root, piType);
                if (kept != null) {
                    narrowed.add(kept);
                }
            }
            if (narrowed.isEmpty()) {
                return null; // all-dead narrowing: ⊤, never an empty fan
            }
            acc = narrowed;
        }
        return acc;
    }

    /**
     * The field's writer-cone may-stamp: the union of every writer's stored-value roots; ⊤ when
     * {@code isUnsafeAccessed} (a non-putfield write channel), when the field can hold an image-heap value
     * ({@link #holdsImageHeapValue}), with no writer, with any ⊤ writer, and on reference cycles. Results are memoized
     * (cycles poison to ⊤ in every query order, so a memoized value does not depend on the computing context); a cycle
     * hit itself returns ⊤ without memoizing.
     */
    private Set<AnalysisType> fieldWriterCone(AnalysisField field, Deque<AnalysisField> chain) {
        if (fieldConeMemo.containsKey(field)) {
            return fieldConeMemo.get(field);
        }
        if (chain.contains(field)) {
            return null; // cycle — ⊤ for this query (not memoized)
        }
        boolean pushed = false;
        Set<AnalysisType> result = null;
        try {
            if (field.isUnsafeAccessed()) {
                return null; // a non-putfield write channel exists
            }
            if (holdsImageHeapValue(field)) {
                return null; // a build-time value has no parsed writer
            }
            List<Shape> ws = writers.get(field);
            if (ws == null || ws.isEmpty()) {
                return null; // never written in parsed code (image-heap corner)
            }
            chain.push(field);
            pushed = true;
            Set<AnalysisType> acc = new LinkedHashSet<>();
            for (Shape w : ws) {
                Set<AnalysisType> cone = resolveShapeRoots(w, chain);
                if (cone == null) {
                    return null; // any ⊤ writer → the field is ⊤
                }
                acc.addAll(cone);
            }
            result = acc.isEmpty() ? null : acc;
            return result;
        } catch (Throwable tv) {
            return null;
        } finally {
            if (pushed) {
                chain.pop();
            }
            fieldConeMemo.put(field, result);
        }
    }

    /**
     * Whether the field can hold a value from the image heap (a value no parsed store wrote). Static: the declaring
     * class is initialized or simulated at build time (its statics are snapshot values; a run-time initialized class's
     * statics start at the default and every later value comes from a parsed store, {@code <clinit>} included).
     * Instance: some image-heap object is an instance of the declaring class (the heap type or a superclass of it
     * declares the field). Any field with a value interceptor (a transformer or computer supplies a build-time value,
     * also for a run-time initialized class). Over-approximate by design (no value inspection); any failure, or an
     * unavailable heap snapshot, answers true. Called only from the serial finalize pass and under the leaf lock.
     */
    private boolean holdsImageHeapValue(AnalysisField field) {
        try {
            AnalysisType owner = field.getDeclaringClass();
            boolean isStatic = field.isStatic();
            boolean buildTime = isStatic && (owner.isInitialized() ||
                            com.oracle.svm.hosted.classinitialization.SimulateClassInitializerSupport.singleton().isClassInitializerSimulated(owner));
            boolean top = imageHeapRule(isStatic, buildTime, isStatic ? null : heapFieldOwners(), owner);
            if (top && isStatic) {
                heapTopStatic++;
            } else if (top) {
                heapTopInstance++;
            } else if (hasValueInterceptor(field)) {
                heapTopIntercepted++; // only the interceptor makes it ⊤
                return true;
            }
            return top;
        } catch (Throwable t) {
            return true;
        }
    }

    /**
     * The image-heap rule as a pure function: a static field is ⊤ iff its class is initialized or simulated at build
     * time; an instance field is ⊤ iff its declaring class is among {@code heapOwners} (or the owner set is unknown).
     */
    static <T> boolean imageHeapRule(boolean isStatic, boolean buildTimeInitialized, Set<T> heapOwners, T owner) {
        if (isStatic) {
            return buildTimeInitialized;
        }
        return heapOwners == null || heapOwners.contains(owner);
    }

    /**
     * Whether a field value transformer or computer is registered for the field, without side effects: the per-field
     * interceptor cache, or (never looked up) the registered-transformer map and the computer annotations. Not seen
     * for a never-looked-up field: an automatic unsafe substitution not yet registered (it is registered lazily); it
     * recomputes an offset or a static-field base, a value the parsed {@code Unsafe} call it replaces also writes.
     */
    private boolean hasValueInterceptor(AnalysisField field) {
        if (com.oracle.svm.hosted.ameta.FieldValueInterceptionSupport.hasFieldValueInterceptor(field)) {
            return true;
        }
        if (field.getFieldValueInterceptor() == null) {
            interceptorUnlooked++;
            if (field.isAnnotationPresent(com.oracle.svm.core.heap.UnknownObjectField.class) ||
                            field.isAnnotationPresent(com.oracle.svm.core.heap.UnknownPrimitiveField.class)) {
                return true;
            }
            jdk.vm.ci.meta.ResolvedJavaField oField = com.oracle.graal.pointsto.infrastructure.OriginalFieldProvider.getOriginalField(field);
            return oField != null && com.oracle.svm.hosted.ameta.FieldValueInterceptionSupport.singleton().lookupAlreadyRegisteredTransformer(oField) != null;
        }
        return false;
    }

    /** Every given type and all of its superclasses ({@code superclass} returns null at the root). */
    static <T> Set<T> withSuperclasses(Iterable<T> types, java.util.function.UnaryOperator<T> superclass) {
        Set<T> owners = new HashSet<>();
        for (T t : types) {
            for (T cur = t; cur != null && owners.add(cur); cur = superclass.apply(cur)) {
                // walk up until a class already recorded (its superclasses are recorded too)
            }
        }
        return owners;
    }

    /** Every image-heap object's type and its superclasses (the classes whose instance fields a heap object has). */
    private Set<AnalysisType> heapFieldOwners() {
        if (!heapFieldOwnersLooked) {
            heapFieldOwnersLooked = true;
            try {
                Object scanner = builder.bb.getUniverse().getHeapScanner();
                if (scanner instanceof com.oracle.svm.hosted.heap.SVMImageHeapScanner svm && svm.getImageHeap() != null) {
                    heapFieldOwners = withSuperclasses(svm.getImageHeap().getReachableObjects().keySet(), AnalysisType::getSuperclass);
                }
            } catch (Throwable t) {
                heapFieldOwners = null; // unavailable: every instance field is ⊤
            }
        }
        return heapFieldOwners;
    }

    // Recursive tracking's image-wide index: written during collect, read lazily when a static table or constant
    // atom is first consulted.
    private final Map<AnalysisField, Set<AnalysisMethod>> rtrackStaticAccess = new java.util.IdentityHashMap<>();
    private final Map<Object, Set<AnalysisMethod>> rtrackConstantUse = new java.util.IdentityHashMap<>();

    /** Thread-local model: the methods whose IR has a VM thread-local access, a current-thread read, or a Thread-typed allocation. */
    private final Set<AnalysisMethod> rtrackThreadLocalMethods = new java.util.LinkedHashSet<>();
    private com.oracle.graal.pointsto.meta.AnalysisType rtrackThreadType;
    private boolean rtrackThreadTypeLooked;

    private com.oracle.graal.pointsto.meta.AnalysisType rtrackThreadType() {
        if (!rtrackThreadTypeLooked) {
            rtrackThreadTypeLooked = true;
            try {
                rtrackThreadType = builder.bb.getMetaAccess().lookupJavaType(Thread.class);
            } catch (Throwable t) {
                rtrackThreadType = null;
            }
        }
        return rtrackThreadType;
    }

    private void rtrackIndexScan(AnalysisMethod method, StructuredGraph ir) {
        try {
            for (jdk.graal.compiler.graph.Node n : ir.getNodes()) {
                boolean tl;
                try {
                    tl = ThreadLocalModel.isThreadLocalIndexNode(n, rtrackThreadType());
                } catch (Throwable t) {
                    tl = true; // over-inclusive: the lazy rescan applies the precise predicates
                }
                if (tl) {
                    synchronized (rtrackThreadLocalMethods) {
                        rtrackThreadLocalMethods.add(method);
                    }
                }
                if (n instanceof jdk.graal.compiler.nodes.java.StoreFieldNode sfn && sfn.field().isStatic()) {
                    AnalysisField f = resolveAnalysisFieldSafe(sfn.field());
                    if (f != null) {
                        rtrackStaticAccess.computeIfAbsent(f, k -> new java.util.LinkedHashSet<>(4)).add(method);
                    }
                } else if (n instanceof jdk.graal.compiler.nodes.java.LoadFieldNode lfn && lfn.field().isStatic()) {
                    AnalysisField f = resolveAnalysisFieldSafe(lfn.field());
                    if (f != null) {
                        rtrackStaticAccess.computeIfAbsent(f, k -> new java.util.LinkedHashSet<>(4)).add(method);
                    }
                } else if (n instanceof jdk.graal.compiler.nodes.ConstantNode cn &&
                                cn.getValue() instanceof com.oracle.graal.pointsto.heap.ImageHeapConstant ihc) {
                    // Key by ConstantData: compressed and uncompressed wrappers of one heap object are one constant.
                    rtrackConstantUse.computeIfAbsent(ihc.getConstantData(), k -> new java.util.LinkedHashSet<>(4))
                                    .add(method);
                }
            }
        } catch (Throwable t) {
            // One malformed graph must not kill the index.
        }
    }

    private AnalysisField resolveAnalysisFieldSafe(jdk.vm.ci.meta.ResolvedJavaField rjf) {
        if (rjf instanceof AnalysisField af) {
            return af;
        }
        try {
            return builder.bb.getUniverse().getField(rjf);
        } catch (Throwable t) {
            return null;
        }
    }

    /** The methods whose IR accesses the static field (stores and loads). */
    public List<AnalysisMethod> rtrackStaticAccessMethods(AnalysisField field) {
        synchronized (rtrackStaticAccess) {
            Set<AnalysisMethod> s = rtrackStaticAccess.get(field);
            return s != null ? List.copyOf(s) : List.of();
        }
    }

    /** The thread-local model's image-wide index (see {@link #rtrackThreadLocalMethods}). */
    public List<AnalysisMethod> rtrackThreadLocalMethods() {
        synchronized (rtrackThreadLocalMethods) {
            return List.copyOf(rtrackThreadLocalMethods);
        }
    }

    /** The methods whose IR uses a constant of this ConstantData identity. */
    public List<AnalysisMethod> rtrackConstantMethods(Object constantData) {
        synchronized (rtrackConstantUse) {
            Set<AnalysisMethod> s = rtrackConstantUse.get(constantData);
            return s != null ? List.copyOf(s) : List.of();
        }
    }
}
