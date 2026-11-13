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

import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.DUMP;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.bump;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.focused;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.markStored;
import static com.oracle.svm.hosted.stringanalysis.RecursiveTracking.memberName;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.AbstractUnsafeCompareAndSwapNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.nodes.virtual.VirtualInstanceNode;
import jdk.graal.compiler.nodes.virtual.VirtualObjectNode;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Listener;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Sink;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscRec;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.Counter;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.RAtom;
import com.oracle.svm.hosted.stringanalysis.RecursiveTracking.SinkRoot;

/**
 * The closed-field escape of {@link RecursiveTracking} and its store-side dual, the field-held receivers.
 */
final class ClosedFieldEscape {
    private final RecursiveTracking rt;

    ClosedFieldEscape(RecursiveTracking rt) {
        this.rt = rt;
    }

    // ------------------------------------------------------------------
    // Closed-field escape.
    // ------------------------------------------------------------------

    /** An IR read of a closed field: the walk continues at {@code node} in {@code frame}. */
    record FieldLoadSite(LocalFlowGraph frame, LoadFieldNode node) {
    }

    /**
     * Why an instance field is not closed (the identity route stays, with refusal inheritance). Each exclusion names a
     * class of reads that are not an IR {@code LoadField} the scan can see.
     */
    enum FieldOpen {
        /** Reference-free (primitive): never holds a string (and never asked). */
        PRIMITIVE,
        /** Public: kept on the identity route (a precision choice; not needed by the soundness argument). */
        PUBLIC,
        /**
         * Flagged Unsafe-accessed by SVM: Unsafe ({@code objectFieldOffset}, folded offsets), VarHandles
         * ({@code VarHandleFeature}), atomic field updaters ({@code AtomicFieldUpdaterFeature}), every field registered
         * for reflective access ({@code Field.get}, MethodHandle getters through {@code MethodHandleFeature}'s
         * registration of heap MemberNames, serialization's {@code RuntimeReflection.register(fields)}), recomputed
         * values. The same flag SVM's own points-to analysis relies on for its unsafe loads.
         */
        UNSAFE_ACCESSED,
        /** Registered for JNI (native code reads it behind the IR; JNI registration does not set the Unsafe flag). */
        JNI_REGISTERED,
        /**
         * SVM rewrites its metadata (an {@code @Alias}/{@code @Inject}/{@code @RecomputeFieldValue}/annotated field, or
         * a field of a {@code @Substitute}d or field-injected type; not the name-only wrappers of hidden classes): SVM
         * code may access it by layout rather than through the declared field.
         */
        SUBSTITUTED,
        /**
         * A reachable method without an IR frame (or graph) the walk can see has a {@code getfield} of a field with this
         * name and type (owner-insensitive), or has no bytecode at all (a synthetic method whose reads are unknown).
         */
        UNFRAMED_READER,
        /**
         * An IR load of an unresolvable field with this name exists, the metadata is unreadable, the read index failed,
         * or the build mode breaks the closed-world premise (a layered, open-world or run-time-class-loading build). Fail
         * closed.
         */
        UNREADABLE,
        /**
         * Registered as accessed ({@code AnalysisField.getAccessedReason() != null}: {@code Feature.registerAsAccessed},
         * JNI, root-class fields, image layers, Truffle's node fields, ...): by that API's definition the field is "used
         * even if there are no explicit reads or writes in the bytecodes", e.g. read by layout without the Unsafe flag
         * (Truffle's node fields). It subsumes UNSAFE_ACCESSED and JNI_REGISTERED; checked after them so its census count
         * is the fields only this exclusion opens. The same check as the JDK-model premise ({@code JdkModelEngine}).
         */
        REGISTERED_ACCESSED,
        /**
         * The field's offset is taken in a framed graph, so
         * it may be read or written by offset, not by an IR {@code LoadField}/{@code StoreField}. Any node that carries the
         * field's offset or location counts: a {@code FieldOffsetProvider} (SVM's {@code FieldOffsetNode}: a folded
         * {@code Unsafe.objectFieldOffset}, a VarHandle's or a recomputation's folded offset, the bootstrap-object CAS),
         * and an Unsafe access ({@code RawLoad}, {@code RawStore}, {@code AtomicReadAndWrite}, CAS / CAE) whose location
         * is the field's {@code FieldLocationIdentity} or whose constant offset names the field on its receiver's type. SVM
         * registers a folded offset's field for Unsafe access only "if the node remains in the graph" with a non-Unsafe
         * usage ({@code MethodTypeFlowBuilder.needsUnsafeRegistration}), so such a field can carry no flag (UNSAFE_ACCESSED
         * does not cover it). The rule is use-blind (reads, writes, an offset passed on as a value); checked last.
         */
        OFFSET_TAKEN
    }

    /**
     * The closed-field rule, pure over the field's properties (the JUnit pins its decision table): a non-static instance
     * field is closed, i.e. every read of it in the image is an IR {@code LoadField} in a frame the walk sees, iff none
     * of the exclusions holds; the first that holds is the answer (null = closed). Needing no exclusion: {@code clone()}
     * (the clone's reads are again {@code LoadField(f)}), inlined copies (the scan covers every framed graph),
     * PEA-forwarded reads (the use is on the value itself), subclass receivers ({@code e.f} resolves to the declaring
     * field), shadowing fields (a different field), records' ObjectMethods (inlined loads or registered MemberNames =
     * UNSAFE_ACCESSED), build-time image heap reads (no run-time string is in the snapshot).
     *
     * <p>The escape of a STRING atom into a
     * closed instance field (one this rule classifies as closed) takes the identity route first (the receiver's atoms, then the
     * waiters on {@code T(X).loads(f)}); the first refusal from that route is not inherited but switches this escape to
     * the field-based continuation: the walk continues at every IR load site of {@code f} in the image (path-less, context
     * UNKNOWN). Continuations already delivered stay (the union). Sound because every read of a closed field in the closed
     * world is one of those load sites, whatever the holder, its owners or its aliases, so no holder refusal can hide a
     * read.
     */
    static FieldOpen closedFieldRule(boolean reference, boolean isPublic, boolean unsafeAccessed, boolean jniRegistered, boolean substituted,
                    boolean unframedReader, boolean unreadable, boolean registeredAccessed, boolean offsetTaken) {
        if (!reference) {
            return FieldOpen.PRIMITIVE;
        }
        if (unreadable) {
            return FieldOpen.UNREADABLE;
        }
        if (isPublic) {
            return FieldOpen.PUBLIC;
        }
        if (unsafeAccessed) {
            return FieldOpen.UNSAFE_ACCESSED;
        }
        if (jniRegistered) {
            return FieldOpen.JNI_REGISTERED;
        }
        if (substituted) {
            return FieldOpen.SUBSTITUTED;
        }
        if (unframedReader) {
            return FieldOpen.UNFRAMED_READER;
        }
        if (registeredAccessed) {
            return FieldOpen.REGISTERED_ACCESSED;
        }
        if (offsetTaken) {
            return FieldOpen.OFFSET_TAKEN;
        }
        return null;
    }

    /** The load sites of {@code f} when it is closed, else null (the identity route with refusal inheritance). */
    @SuppressWarnings("unchecked")
    List<FieldLoadSite> closedFieldLoads(AnalysisField f) {
        FieldReadIndex idx = fieldReadIndex(); // built once, outside the memo's bin lock
        Object r = rt.closedFieldMemo.computeIfAbsent(f, k -> computeClosedField(k, idx));
        if (r instanceof List<?> l) {
            rt.closedFieldEscapes.incrementAndGet();
            return (List<FieldLoadSite>) l;
        }
        return null;
    }

    private Object computeClosedField(AnalysisField f, FieldReadIndex idx) {
        FieldOpen open;
        try {
            boolean reference = f.getJavaKind() == JavaKind.Object;
            open = closedFieldRule(reference, f.isPublic(), f.isUnsafeAccessed(), rt.jniRegistered(f), substituted(f),
                            idx.unframedReads.contains(nameAndType(f)) || idx.opaqueUnframed > 0,
                            idx.unresolvedNames.contains(f.getName()) || idx.failReason != null, f.getAccessedReason() != null,
                            idx.offsetFields.contains(f));
        } catch (Throwable t) {
            open = FieldOpen.UNREADABLE;
        }
        if (open != null) {
            bump(rt.closedFieldOpenBy, open.name());
            if (DUMP) {
                System.out.println("[rtrack-dump] CLOSED-FIELD open " + f.format("%H.%n") + " " + open);
            }
            return open;
        }
        List<FieldLoadSite> sites = idx.loads.getOrDefault(f, List.of());
        bump(rt.closedFieldOpenBy, "closed");
        if (DUMP) {
            System.out.println("[rtrack-dump] CLOSED-FIELD closed " + f.format("%H.%n") + " loads=" + sites.size());
        }
        return sites;
    }

    /**
     * SVM's annotation substitutions rewrite the field's metadata: the field is an alias / injected / recomputed
     * substitution field, or its declaring type is a {@code @Substitute} class or field-injected type. The name-only
     * wrappers of hidden classes ({@code CustomSubstitutionType}) are not a rewrite: they delegate every field to the
     * original, whose accesses stay ordinary IR loads.
     */
    static boolean substituted(AnalysisField f) {
        Object dt = f.getDeclaringClass().getWrapped();
        return f.getWrapped() instanceof com.oracle.graal.pointsto.infrastructure.OriginalFieldProvider ||
                        dt instanceof com.oracle.svm.hosted.substitute.SubstitutionType || dt instanceof com.oracle.svm.hosted.substitute.InjectedFieldsType;
    }

    static String nameAndType(jdk.vm.ci.meta.JavaField f) {
        return f.getName() + ":" + f.getType().getName();
    }

    /**
     * The closed-field escape's listener: the identity route ({@link RecursiveTracking#escapeListener}, its own key tag {@code "esc-cf"}),
     * with a one-shot field-based fallback instead of refusal inheritance.
     */
    Listener closedFieldEscapeListener(RAtom atom, LocalFlowGraph frame, Object storeNode, AnalysisField f, List<FieldLoadSite> loads, CallPath path, EscRec rec) {
        AtomicBoolean fell = new AtomicBoolean();
        Consumer<RTrackRefusal> fallback = r -> {
            if (fell.compareAndSet(false, true)) {
                if (rec != null) {
                    rec.fell.set(true); // holder-end rule: every load site walked, the escape is holder-free
                }
                rt.closedFieldFallbacks.incrementAndGet();
                rt.closedFieldFallbackSites.computeIfAbsent(f.format("%H.%n") + " loads=" + loads.size(), k -> new Counter()).incrementAndGet(); // census
                if (DUMP && focused(String.valueOf(atom.key))) {
                    System.out.println("[rtrack-dump] CLOSED-FIELD fallback atom=" + atom.key + " field=" + f.format("%H.%n") + " on " + r + " loads=" + loads.size());
                }
                for (FieldLoadSite l : loads) {
                    rt.enqueueWalk(atom, l.frame(), l.node(), null, MethodContext.UNKNOWN);
                }
            }
        };
        return rt.escapeListener("esc-cf", atom, frame, storeNode, f, path, fallback, rec);
    }

    /**
     * The image-wide read index of the closed-field rule: every IR {@code LoadField} of a reference instance field in a
     * framed graph, plus the {@code getfield}s (name:type) of the reachable methods without a frame or graph.
     */
    static final class FieldReadIndex {
        final Map<AnalysisField, List<FieldLoadSite>> loads = new IdentityHashMap<>();
        /** The fields whose offset or location a framed graph's node carries (OFFSET_TAKEN). */
        final Set<AnalysisField> offsetFields = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        /** Census: the offset-carrying nodes met (FieldOffsetProvider; Unsafe accesses that name a field). */
        long offsetNodes;
        long unsafeFieldNodes;
        /** Census: objectFieldOffset calls in reachable methods without a frame (SVM substitution bodies), and unreadable call targets there. */
        long unframedOffsetCalls;
        long unframedUnreadableInvokes;
        final List<String> unframedOffsetExamples = new ArrayList<>();
        final Set<String> unframedReads = new java.util.HashSet<>();
        final Set<String> unresolvedNames = new java.util.HashSet<>();
        long framed;
        long sites;
        long unframed;
        long opaqueUnframed;
        /** Universe methods with a frame (any reachability), checked against the bridge's frame count. */
        long frameMethods;
        long frameCount = -1;
        long universe;
        long ms;
        /** Non-null = the index failed or the build mode breaks the premise: fail closed, no field is closed. */
        String failReason;
        final List<String> opaqueExamples = new ArrayList<>();
    }

    private FieldReadIndex fieldReadIndex() {
        FieldReadIndex x = rt.fieldReadIndex;
        if (x == null) {
            synchronized (rt.closedFieldIndexLock) {
                x = rt.fieldReadIndex;
                if (x == null) {
                    x = buildFieldReadIndex();
                    rt.fieldReadIndex = x;
                }
            }
        }
        return x;
    }

    private FieldReadIndex buildFieldReadIndex() {
        long t0 = System.nanoTime();
        FieldReadIndex x = new FieldReadIndex();
        try {
            // A build mode that breaks "every read of f is an IR LoadField of this analysis" (an extension
            // layer's code, an open type world, run-time loaded classes) closes no field
            String mode = closedWorldGuard();
            if (mode != null) {
                x.failReason = "build-mode:" + mode;
            }
            x.frameCount = rt.bridge.frameCount();
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                x.universe++;
                LocalFlowGraph fr = rt.bridge.frameOf(m);
                if (fr != null) {
                    x.frameMethods++;
                }
                if (!m.isReachable() && !m.isImplementationInvoked()) {
                    continue;
                }
                StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
                if (g == null) {
                    x.unframed++;
                    unframedReads(m, x);
                    continue;
                }
                x.framed++;
                LocalFlowGraph frame = fr;
                // The same one walk over the graph's nodes also collects the fields whose offset is taken
                scanFieldAccesses(g, rt.bridge::resolveField, (af, lfn) -> {
                    x.loads.computeIfAbsent(af, k -> new ArrayList<>()).add(new FieldLoadSite(frame, lfn));
                    x.sites++;
                }, x.unresolvedNames::add, (af, viaUnsafe) -> {
                    x.offsetFields.add(af);
                    if (viaUnsafe) {
                        x.unsafeFieldNodes++;
                    } else {
                        x.offsetNodes++;
                    }
                });
            }
            // The enumeration must have seen every frame (universeMethods() swallows its own failure and
            // may return a partial or empty list): any mismatch, or an unknown frame count, fails closed
            if (x.failReason == null) {
                x.failReason = indexFailure(x.universe, x.frameMethods, x.frameCount);
            }
        } catch (Throwable t) {
            x.failReason = "index:" + t.getClass().getSimpleName(); // fail closed: no field is closed
        }
        x.ms = (System.nanoTime() - t0) / 1_000_000;
        if (x.failReason != null) {
            System.out.println("[sug-fwd-rtrack-closedfield] index FAILED CLOSED (no field is closed): " + x.failReason);
        }
        return x;
    }

    /**
     * Pure; pinned by the JUnit: the read index's sanity check. The universe enumeration must be non-empty
     * and must have met every frame ({@code frameMethods} = the universe methods with a frame = the bridge's frame
     * count; -1 = unknown); otherwise the reason (fail closed), else null.
     */
    static String indexFailure(long universe, long frameMethods, long frameCount) {
        if (universe > 0 && frameCount >= 0 && frameMethods == frameCount) {
            return null;
        }
        return "index:universe=" + universe + ",frames=" + frameMethods + "/" + frameCount;
    }

    /**
     * The build modes in which an IR {@code LoadField} of this analysis is not every read of a field: the
     * reflection bridge's guard ({@link ReflectionBridge#buildModeGuard}: a layered build, {@code -H:Preserve}, the base-layer inclusion
     * policy), an open type world ({@code -H:-ClosedTypeWorld}) and run-time class loading (a run-time class can read a
     * non-private field). Null = a standard closed-world build; an unreadable check fails closed.
     */
    static String closedWorldGuard() {
        String why = ReflectionBridge.buildModeGuard();
        StringBuilder sb = new StringBuilder(why == null ? "" : why);
        try {
            if (!com.oracle.svm.core.SubstrateOptions.useClosedTypeWorld()) {
                sb.append("open-world;");
            }
            if (com.oracle.svm.core.hub.RuntimeClassLoading.isSupported()) {
                sb.append("runtime-class-loading;");
            }
        } catch (Throwable t) {
            sb.append("guard-unreadable:").append(t.getClass().getSimpleName()).append(';');
        }
        return sb.length() == 0 ? null : sb.toString();
    }

    /**
     * Every IR load of a reference instance field in {@code g}, keyed by {@code resolve} (the declaring field); an
     * unresolvable one reports its name (the fields of that name are then not closed).
     */
    static <K> void collectLoads(StructuredGraph g, java.util.function.Function<ResolvedJavaField, K> resolve, java.util.function.BiConsumer<K, LoadFieldNode> sink,
                    Consumer<String> unresolvedName) {
        scanFieldAccesses(g, resolve, sink, unresolvedName, (k, viaUnsafe) -> {
        });
    }

    /**
     * One walk over {@code g}'s nodes: the IR loads ({@link #collectLoads}) and the OFFSET_TAKEN fields
     * ({@code offsetTaken.accept(field, viaUnsafe)}): every instance field named by a {@code FieldOffsetProvider}
     * (viaUnsafe = false) or by an Unsafe access node ({@link #unsafeAccessField}; viaUnsafe = true). An unresolvable
     * field reports its name (the fields of that name are then not closed: UNREADABLE).
     */
    static <K> void scanFieldAccesses(StructuredGraph g, java.util.function.Function<ResolvedJavaField, K> resolve, java.util.function.BiConsumer<K, LoadFieldNode> sink,
                    Consumer<String> unresolvedName, java.util.function.BiConsumer<K, Boolean> offsetTaken) {
        for (Node n : g.getNodes()) {
            if (n instanceof LoadFieldNode lfn) {
                if (!lfn.field().isStatic() && lfn.field().getJavaKind() == JavaKind.Object) {
                    K k = resolve.apply(lfn.field());
                    if (k == null) {
                        unresolvedName.accept(lfn.field().getName());
                    } else {
                        sink.accept(k, lfn);
                    }
                }
            } else if (n instanceof jdk.graal.compiler.nodes.extended.FieldOffsetProvider fop) {
                offsetTakenField(fop.getField(), false, resolve, unresolvedName, offsetTaken);
            } else if (n instanceof jdk.graal.compiler.nodes.spi.TrackedUnsafeAccess) {
                ResolvedJavaField rf = unsafeAccessField(n);
                if (rf != null) {
                    offsetTakenField(rf, true, resolve, unresolvedName, offsetTaken);
                }
            }
        }
    }

    private static <K> void offsetTakenField(ResolvedJavaField rf, boolean viaUnsafe, java.util.function.Function<ResolvedJavaField, K> resolve, Consumer<String> unresolvedName,
                    java.util.function.BiConsumer<K, Boolean> offsetTaken) {
        if (rf == null || rf.isStatic()) {
            return; // static fields are never closed (instance fields only)
        }
        K k = resolve.apply(rf);
        if (k == null) {
            unresolvedName.accept(rf.getName());
        } else {
            offsetTaken.accept(k, viaUnsafe);
        }
    }

    /**
     * The field an Unsafe access node names, else null: its location is a {@code FieldLocationIdentity}, or its offset
     * is a constant naming an instance field of its receiver's (non-array) stamp type
     * ({@code AnalysisType.findInstanceFieldWithOffset}). A {@code FieldOffsetProvider} offset is its own node (met by the
     * scan); a non-constant, non-provider offset is computed from a registered (UNSAFE_ACCESSED) {@code objectFieldOffset}
     * or from a folded offset that is itself in a framed graph.
     *
     * <p>Known residual: this covers the offset's provenance, not its arithmetic target. {@code U.getReference(o, off1 + k)}
     * with {@code off1 = U.objectFieldOffset(H.class, "s1")} yields a RawLoad with offset
     * {@code Add(FieldOffsetNode(H.s1), k)}, so this method returns null and the scan opens only s1, while the access
     * reads the sibling field at off(s1)+k (no Unsafe flag, no offset-carrying node: a constructible false ADMIT). Not
     * observed so far; SVM's own points-to shares this field-level blindness (non-provider object loads route to the
     * opaque UnsafeLoadTypeFlow). Raw-address accesses ({@code UnsafeMemoryLoad/Store}) have no object.
     */
    static ResolvedJavaField unsafeAccessField(Node n) {
        ValueNode obj;
        ValueNode off;
        org.graalvm.word.LocationIdentity loc;
        JavaKind kind;
        if (n instanceof jdk.graal.compiler.nodes.extended.UnsafeAccessNode u) {
            obj = u.object();
            off = u.offset();
            loc = u.getLocationIdentity();
            kind = u.accessKind();
        } else if (n instanceof AtomicReadAndWriteNode a) {
            obj = a.object();
            off = a.offset();
            loc = a.getKilledLocationIdentity();
            kind = a.getValueKind();
        } else if (n instanceof AbstractUnsafeCompareAndSwapNode c) {
            obj = c.object();
            off = c.offset();
            loc = c.getKilledLocationIdentity();
            kind = c.getValueKind();
        } else {
            // AtomicReadAndAddNode (getAndAdd*) names no field here, deliberately: getAndAdd is registered only for
            // numeric-integer kinds (StandardGraphBuilderPlugins), so a reference field can never be its target, and a
            // FieldOffsetProvider offset feeding one is caught by the provider case of the same scan.
            return null;
        }
        if (loc instanceof jdk.graal.compiler.nodes.FieldLocationIdentity fli) {
            return fli.getField();
        }
        if (off != null && obj != null && off.isJavaConstant() && off.asJavaConstant().getJavaKind().isNumericInteger()) {
            jdk.vm.ci.meta.ResolvedJavaType t = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(obj);
            if (t != null && !t.isArray()) {
                return t.findInstanceFieldWithOffset(off.asJavaConstant().asLong(), kind);
            }
        }
        return null;
    }

    /** The {@code getfield}s of a reachable method the walk has no IR for (abstract and native methods read nothing here). */
    private static void unframedReads(AnalysisMethod m, FieldReadIndex x) {
        long before = x.unframedOffsetCalls;
        if (!getfieldsOf(m.getWrapped(), x.unframedReads, x)) {
            x.opaqueUnframed++;
            if (x.opaqueExamples.size() < 20) {
                x.opaqueExamples.add(m.format("%H.%n(%p)") + " [" + m.getWrapped().getClass().getSimpleName() + "]");
            }
        }
        if (x.unframedOffsetCalls != before && x.unframedOffsetExamples.size() < 10) {
            x.unframedOffsetExamples.add(m.format("%H.%n(%p)") + " [" + m.getWrapped().getClass().getSimpleName() + "]");
        }
    }

    /**
     * Adds the name:type of every {@code getfield} in {@code w}'s bytecode to {@code out} (owner-insensitive: an
     * over-approximation); false when {@code w} has a body whose reads cannot be read (no bytecode, or an unreadable
     * field reference): fail closed. Abstract and native methods have no Java body (native code reads through JNI only).
     */
    static boolean getfieldsOf(ResolvedJavaMethod w, Set<String> out) {
        return getfieldsOf(w, out, null);
    }

    /**
     * As {@link #getfieldsOf(ResolvedJavaMethod, Set)}; with {@code x}, also counts (census only) the calls of a
     * method named {@code objectFieldOffset}: the unframed methods are SVM's substitution bodies, whose folded offsets
     * the OFFSET_TAKEN rule (framed graphs) does not see; an unreadable call target is not counted.
     */
    static boolean getfieldsOf(ResolvedJavaMethod w, Set<String> out, FieldReadIndex x) {
        if (w.isAbstract() || w.isNative()) {
            return true;
        }
        byte[] code;
        try {
            code = w.getCode();
        } catch (Throwable t) {
            code = null;
        }
        if (code == null) {
            return false;
        }
        boolean ok = true;
        jdk.graal.compiler.bytecode.BytecodeStream s = new jdk.graal.compiler.bytecode.BytecodeStream(code);
        jdk.vm.ci.meta.ConstantPool cp = w.getConstantPool();
        while (s.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.END) {
            int bc = s.currentBC();
            if (bc == jdk.graal.compiler.bytecode.Bytecodes.GETFIELD) {
                try {
                    out.add(nameAndType(cp.lookupField(s.readCPI(), w, jdk.graal.compiler.bytecode.Bytecodes.GETFIELD)));
                } catch (Throwable t) {
                    ok = false;
                }
            } else if (x != null && (bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEVIRTUAL || bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKESTATIC ||
                            bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKESPECIAL || bc == jdk.graal.compiler.bytecode.Bytecodes.INVOKEINTERFACE)) {
                try {
                    if ("objectFieldOffset".equals(cp.lookupMethod(s.readCPI(), bc, null).getName())) {
                        x.unframedOffsetCalls++;
                    }
                } catch (Throwable t) {
                    x.unframedUnreadableInvokes++;
                }
            }
            s.next();
        }
        return ok;
    }

    /** The closed-field census (print-only). */
    String closedFieldCensus() {
        FieldReadIndex x = rt.fieldReadIndex;
        StringBuilder sb = new StringBuilder("[sug-fwd-rtrack-closedfield] escapes=").append(rt.closedFieldEscapes.get())
                        .append(" fallbacks=").append(rt.closedFieldFallbacks.get()).append(" fields{");
        new TreeMap<>(rt.closedFieldOpenBy).forEach((k, v) -> sb.append(k).append('=').append(v.get()).append(' '));
        sb.append('}');
        if (x != null) {
            sb.append(" index{framed=").append(x.framed).append(" loadSites=").append(x.sites).append(" fields=").append(x.loads.size())
                            .append(" unframed=").append(x.unframed).append(" unframedGetfields=").append(x.unframedReads.size())
                            .append(" opaqueUnframed=").append(x.opaqueUnframed).append(" unresolvedNames=").append(x.unresolvedNames.size())
                            .append(" offsetFields=").append(x.offsetFields.size()).append(" offsetNodes=").append(x.offsetNodes).append(" unsafeFieldNodes=").append(x.unsafeFieldNodes).append(
                                            " unframedOffsetCalls=").append(x.unframedOffsetCalls).append(" unframedUnreadableInvokes=").append(x.unframedUnreadableInvokes)
                            .append(" frames=").append(x.frameMethods).append('/').append(x.frameCount).append(" universe=").append(x.universe)
                            .append(" failed=").append(x.failReason != null).append(x.failReason != null ? " failReason=" + x.failReason : "").append(" ms=").append(x.ms).append('}');
            // the fallback fans: the fallen-back fields by load-site count (the field-based route's widest fans)
            List<Map.Entry<String, Counter>> fb = new ArrayList<>(rt.closedFieldFallbackSites.entrySet());
            fb.sort((a, b) -> {
                int la = Integer.parseInt(a.getKey().substring(a.getKey().lastIndexOf('=') + 1));
                int lb = Integer.parseInt(b.getKey().substring(b.getKey().lastIndexOf('=') + 1));
                return la != lb ? Integer.compare(lb, la) : a.getKey().compareTo(b.getKey());
            });
            long totalSites = 0;
            for (Map.Entry<String, Counter> e : fb) {
                totalSites += Long.parseLong(e.getKey().substring(e.getKey().lastIndexOf('=') + 1));
            }
            sb.append(" fallbackFields=").append(fb.size()).append(" fallbackFieldLoadSites=").append(totalSites);
            for (int i = 0; i < Math.min(12, fb.size()); i++) {
                sb.append("\n[sug-fwd-rtrack-closedfield] fan ").append(fb.get(i).getKey()).append(" fallbacks=").append(fb.get(i).getValue().get());
            }
            for (String e : x.opaqueExamples) {
                sb.append("\n[sug-fwd-rtrack-closedfield] opaque-unframed ").append(e);
            }
            for (String e : x.unframedOffsetExamples) {
                sb.append("\n[sug-fwd-rtrack-closedfield] unframed-offset-call ").append(e);
            }
        }
        return sb.toString();
    }

    // ------------------------------------------------------------------
    // Field-held receivers (the store-side dual of the closed-field rule; used by ForwardFixpoint's field-held receivers)
    // ------------------------------------------------------------------
    /** An IR write of an instance field: {@code value} is the written value in {@code frame}; null = unresolvable (fail closed). */
    record FieldStoreSite(LocalFlowGraph frame, Node store, ValueNode value) {
    }

    /**
     * The image-wide write index (built once, lazily): every IR write of a reference instance field in a framed graph (a
     * {@code StoreField}; a committed virtual instance's slot = its initial store), keyed by the declaring field, plus
     * the {@code putfield}s (name:type) of the reachable methods without a frame or graph. The same enumeration and
     * fail-closed checks as {@link FieldReadIndex}.
     */
    static final class FieldWriteIndex {
        final Map<AnalysisField, List<FieldStoreSite>> stores = new IdentityHashMap<>();
        final Set<String> unframedWrites = new java.util.HashSet<>();
        final Set<String> unresolvedNames = new java.util.HashSet<>();
        long framed;
        long sites;
        long unframed;
        long opaqueUnframed;
        long frameMethods;
        long frameCount = -1;
        long universe;
        long ms;
        /** Non-null = the index failed or the build mode breaks the premise: no field-held receiver resolves. */
        String failReason;
    }

    /**
     * Pure; pinned by {@code FieldHeldReceiverTest}: whether the stores of an instance field enumerate every value the field
     * can hold at run time, else the reason. {@code writeOpen} is {@link #closedFieldRule} evaluated with the write-side
     * inputs (an unframed {@code putfield} of the name:type; an unresolvable IR write or a failed index; the metadata
     * exclusions as for reads); a holder instance in the image heap carries a build-time value no IR store wrote.
     */
    static String fieldStoreRule(boolean isStatic, FieldOpen writeOpen, boolean heapHolder) {
        if (isStatic) {
            return "STATIC";
        }
        if (writeOpen != null) {
            return writeOpen.name();
        }
        if (heapHolder) {
            return "IMAGE_HEAP_HOLDER";
        }
        return null;
    }

    /** The store sites of {@code f} when every run-time value of {@code f} is written by one of them (or is null), else the reason (a String). */
    Object fieldStoreSites(AnalysisField f) {
        FieldReadIndex rx = fieldReadIndex(); // built once (offsets, the read-side failure)
        FieldWriteIndex wx = fieldWriteIndex();
        return rt.fieldStoreMemo.computeIfAbsent(f, k -> computeFieldStores(k, rx, wx));
    }

    private Object computeFieldStores(AnalysisField f, FieldReadIndex rx, FieldWriteIndex wx) {
        String why;
        try {
            boolean reference = f.getJavaKind() == JavaKind.Object;
            FieldOpen open = closedFieldRule(reference, f.isPublic(), f.isUnsafeAccessed(), rt.jniRegistered(f), substituted(f),
                            wx.unframedWrites.contains(nameAndType(f)) || wx.opaqueUnframed > 0,
                            wx.unresolvedNames.contains(f.getName()) || wx.failReason != null || rx.failReason != null, f.getAccessedReason() != null,
                            rx.offsetFields.contains(f));
            why = fieldStoreRule(f.isStatic(), open, f.isStatic() || open != null ? false : heapHolder(f));
        } catch (Throwable t) {
            why = "UNREADABLE";
        }
        if (DUMP) {
            System.out.println("[rtrack-dump] FIELD-STORES " + f.format("%H.%n") + " " + (why != null ? "open " + why : "closed stores=" + wx.stores.getOrDefault(f, List.of()).size()));
        }
        return why != null ? why : wx.stores.getOrDefault(f, List.of());
    }

    /** Whether the image heap holds an instance of a type that has {@code f} (fail closed: an unreadable heap counts). */
    private boolean heapHolder(AnalysisField f) {
        Map<AnalysisType, Set<ImageHeapConstant>> heap = rt.bridge.heapObjects();
        if (heap == null) {
            return true;
        }
        jdk.vm.ci.meta.ResolvedJavaType d = f.getDeclaringClass();
        for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> e : heap.entrySet()) {
            if (e.getValue() != null && !e.getValue().isEmpty() && d.isAssignableFrom(e.getKey())) {
                return true;
            }
        }
        return false;
    }

    private FieldWriteIndex fieldWriteIndex() {
        FieldWriteIndex x = rt.fieldWriteIndex;
        if (x == null) {
            synchronized (rt.fieldWriteIndexLock) {
                x = rt.fieldWriteIndex;
                if (x == null) {
                    x = buildFieldWriteIndex();
                    rt.fieldWriteIndex = x;
                }
            }
        }
        return x;
    }

    private FieldWriteIndex buildFieldWriteIndex() {
        long t0 = System.nanoTime();
        FieldWriteIndex x = new FieldWriteIndex();
        try {
            String mode = closedWorldGuard();
            if (mode != null) {
                x.failReason = "build-mode:" + mode;
            }
            x.frameCount = rt.bridge.frameCount();
            for (AnalysisMethod m : rt.bridge.universeMethods()) {
                x.universe++;
                LocalFlowGraph fr = rt.bridge.frameOf(m);
                if (fr != null) {
                    x.frameMethods++;
                }
                if (!m.isReachable() && !m.isImplementationInvoked()) {
                    continue;
                }
                StructuredGraph g = fr != null ? rt.graphOf(fr) : null;
                if (g == null) {
                    x.unframed++;
                    if (!putfieldsOf(m.getWrapped(), x.unframedWrites)) {
                        x.opaqueUnframed++;
                    }
                    continue;
                }
                x.framed++;
                LocalFlowGraph frame = fr;
                collectStores(g, rt.bridge::resolveField, (af, store, value) -> {
                    x.stores.computeIfAbsent(af, k -> new ArrayList<>()).add(new FieldStoreSite(frame, store, value));
                    x.sites++;
                }, x.unresolvedNames::add);
            }
            if (x.failReason == null) {
                x.failReason = indexFailure(x.universe, x.frameMethods, x.frameCount);
            }
        } catch (Throwable t) {
            x.failReason = "index:" + t.getClass().getSimpleName();
        }
        x.ms = (System.nanoTime() - t0) / 1_000_000;
        System.out.println("[sug-acc-fieldrecv-index] framed=" + x.framed + " storeSites=" + x.sites + " fields=" + x.stores.size() + " unframed=" + x.unframed +
                        " unframedPutfields=" + x.unframedWrites.size() + " opaqueUnframed=" + x.opaqueUnframed + " unresolvedNames=" + x.unresolvedNames.size() +
                        " frames=" + x.frameMethods + "/" + x.frameCount + " failed=" + (x.failReason != null) + (x.failReason != null ? " failReason=" + x.failReason : "") + " ms=" + x.ms);
        return x;
    }

    /** A write of a reference instance field: the declaring field (resolved), the store node, the written value (null = unresolvable). */
    interface StoreSink<K> {
        void accept(K field, Node store, ValueNode value);
    }

    /**
     * Every IR write of a reference instance field in {@code g}, keyed by {@code resolve} (the declaring field): a
     * {@code StoreField} (its value), and each Object slot of a committed virtual instance (the initial store; a slot
     * holding another virtual object is that object's materialization in the graph, null when it has none; a missing
     * slot value is null). An unresolvable field reports its name. Writes by offset are not listed: the read index's
     * OFFSET_TAKEN opens such fields.
     */
    static <K> void collectStores(StructuredGraph g, java.util.function.Function<ResolvedJavaField, K> resolve, StoreSink<K> sink, Consumer<String> unresolvedName) {
        for (Node n : g.getNodes()) {
            if (n instanceof StoreFieldNode sfn) {
                if (!sfn.field().isStatic() && sfn.field().getJavaKind() == JavaKind.Object) {
                    K k = resolve.apply(sfn.field());
                    if (k == null) {
                        unresolvedName.accept(sfn.field().getName());
                    } else {
                        sink.accept(k, sfn, sfn.value());
                    }
                }
            } else if (n instanceof CommitAllocationNode can) {
                List<ValueNode> values = can.getValues();
                int pos = 0;
                for (VirtualObjectNode vo : can.getVirtualObjects()) {
                    if (vo instanceof VirtualInstanceNode vin) {
                        for (int i = 0; i < vin.entryCount(); i++) {
                            ResolvedJavaField rf = vin.field(i);
                            if (rf == null || rf.isStatic() || rf.getJavaKind() != JavaKind.Object) {
                                continue;
                            }
                            K k = resolve.apply(rf);
                            if (k == null) {
                                unresolvedName.accept(rf.getName());
                                continue;
                            }
                            ValueNode v = pos + i < values.size() ? values.get(pos + i) : null;
                            if (v instanceof VirtualObjectNode inner) {
                                boolean any = false;
                                for (Node u : inner.usages()) {
                                    if (u instanceof AllocatedObjectNode aon && aon.getVirtualObject() == inner) {
                                        sink.accept(k, can, aon);
                                        any = true;
                                    }
                                }
                                if (!any) {
                                    sink.accept(k, can, null);
                                }
                            } else {
                                sink.accept(k, can, v);
                            }
                        }
                    }
                    pos += vo.entryCount();
                }
            }
        }
    }

    /**
     * Adds the name:type of every {@code putfield} in {@code w}'s bytecode to {@code out} (owner-insensitive); false when
     * {@code w} has a body whose writes cannot be read (no bytecode, an unreadable field reference): fail closed. Abstract
     * and native methods have no Java body.
     */
    static boolean putfieldsOf(ResolvedJavaMethod w, Set<String> out) {
        if (w.isAbstract() || w.isNative()) {
            return true;
        }
        byte[] code;
        try {
            code = w.getCode();
        } catch (Throwable t) {
            code = null;
        }
        if (code == null) {
            return false;
        }
        boolean ok = true;
        jdk.graal.compiler.bytecode.BytecodeStream s = new jdk.graal.compiler.bytecode.BytecodeStream(code);
        jdk.vm.ci.meta.ConstantPool cp = w.getConstantPool();
        while (s.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.END) {
            if (s.currentBC() == jdk.graal.compiler.bytecode.Bytecodes.PUTFIELD) {
                try {
                    out.add(nameAndType(cp.lookupField(s.readCPI(), w, jdk.graal.compiler.bytecode.Bytecodes.PUTFIELD)));
                } catch (Throwable t) {
                    ok = false;
                }
            }
            s.next();
        }
        return ok;
    }

    /** The escape into {@code receiverKey.member} where the receiver is a model operand (a chain or a temp: its interned sink). */
    void escapeIntoKey(RAtom atom, LocalFlowGraph frame, Object storeNode, Object receiverKey, Consumer<Sink> rootTask, Object member, CallPath path,
                    MethodContext mctx) {
        markStored(atom); // the model stores with an operand receiver
        if (DUMP && rt.models.abstracted(member)) {
            System.out.println("[rtrack-dump] JDKMODEL-FIELD field-escape-key " + memberName(member) + " at " + rt.frameName(frame) + " node=" + storeNode + " atom=" + atom.key);
        }
        if (rt.models.fieldRule(atom.table, member, "field-escape")) {
            return;
        }
        MethodContext m = mctx != null ? mctx : MethodContext.UNKNOWN;
        rt.internSink("escape", new SinkRoot(frame, receiverKey, m, path), rootTask, rt.escapeListener(atom, frame, storeNode, member, path));
    }
}
