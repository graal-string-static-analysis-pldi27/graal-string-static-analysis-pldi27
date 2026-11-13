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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;

import jdk.graal.compiler.graph.Node;

/**
 * The per-method local flow graph (LFG), built in Phase A by {@code LfgWalk} on each method's decoded IR graph: the
 * decoded graph instance ({@link #irGraph}), the node registry ({@link #vertexForNode}), the INVOKE_CALLSITE vertices
 * the value-driven walk reaches (the LFG half of {@code ForwardFixpoint.index}'s {@code callersOf}), the vertices and
 * scan records the Phase-A SUG vertex creation reads, and the type-guard inventory ({@link #guardsForValue}) with its
 * reachability proof ({@link #anchorsUnreachableBehind}). An undecodable method aborts the construction.
 */
final class LocalFlowGraph {

    enum VertexKind {
        PARAM_ENTRY,
        RETURN_EXIT,
        INVOKE_CALLSITE,
        LOAD,
        ARRAY_LOAD,
        /**
         * A strict class check on the traced value (an intrinsified {@code GetClassNode} or a canonicalized exact
         * {@code InstanceOfNode}), or a raw String-field read. Its only product is its Phase-A SUG usage site
         * ({@code LfgWalk.wireClassCheckSites}); the walk does not continue through it.
         */
        CLASS_CHECK,
        INTERNAL
    }

    /**
     * One LFG vertex. The engine's detached call descriptors and site identities
     * ({@code RecursiveTracking.callVertexOf}/{@code siteOf}) are {@code LocalVertex} objects too (id -1, never
     * registered).
     */
    static final class LocalVertex {
        final int id;
        final VertexKind kind;
        /** PARAM_ENTRY: the parameter index (the SUG VARIABLE vertices). */
        int paramIndex = -1;
        /** INVOKE_CALLSITE / CLASS_CHECK: the bci (the caller index; the SUG site position). */
        int bci = -1;
        /** INVOKE_CALLSITE: the declared target (the caller index's CHA resolution; descriptors: the IR callee). */
        AnalysisMethod calleeMethod;
        /** The IR node: the invoke, load, check node, seed allocation or passthrough commit/Pi/Phi. */
        Object irNode;
        /** The seed/passthrough label ({@code "invoke-return"}, {@code "new-array"}, ...; the own-identity block test). */
        String label;
        TypeFlow<?> typeFlow;
        /**
         * The declared (for constants/allocations: exact) type of the IR value, set for seed vertices that carry no
         * {@code typeFlow} or whose typeFlow may be absent (virtualized allocations). Read by
         * {@code ForwardFixpoint.vertexIdentityType}; IR-derived, never points-to state.
         */
        AnalysisType declaredType;
        /** LOAD: the loaded field (the SUG load vertex's type). */
        AnalysisField field;
        /**
         * The dispatch receiver's provable may-stamp, set only on the engine's detached call descriptors (from
         * {@code ArgStampResolution.stampOfUnregisteredInvoke}); read by {@code ForwardFixpoint.filterTargetsByArgStamp}.
         * {@code null} = ⊤ (the full CHA fan).
         */
        Set<AnalysisType> argStamp;
        /** ARRAY_LOAD: the element type (the SUG load vertex's type). */
        AnalysisType arrayType;
        /** CLASS_CHECK: the position node of its SUG site (the check node, or the raw-read load). */
        Node armAnchor;
        /**
         * Non-null on a CLASS_CHECK vertex that is a raw read of a String representation field ({@code value} /
         * {@code coder}): the field name. The usage site then carries {@link SugNameTables#RAW_VALUE_USAGE} /
         * {@link SugNameTables#RAW_CODER_USAGE} instead of {@code getClass}.
         */
        String rawStringField;
        /**
         * The vertex's creator and only in-edge (the call vertex for an {@code invoke-return}); {@code null} for
         * parameters, seeds and fixtures. Read by the passthrough branch of {@code ForwardFixpoint.localBlock}.
         */
        LocalVertex from;
        /** INVOKE_CALLSITE: its {@code invoke-return} result vertex, or {@code null} (at most one per call vertex). */
        LocalVertex result;
        /** The owning graph (one graph per vertex), so frame resolution never needs the method-keyed map. */
        final LocalFlowGraph owner;

        LocalVertex(LocalFlowGraph owner, int id, VertexKind kind) {
            this.owner = owner;
            this.id = id;
            this.kind = kind;
        }

        @Override
        public String toString() {
            return "LV" + id + "[" + kind + "]" + (label != null ? " " + label : "");
        }
    }

    private final AnalysisMethod method;
    /**
     * The IR graph instance this LFG was built from. Recursive tracking must walk the same node identities as the
     * registry (the decoded-IR LRU may otherwise hand out a fresh re-decode). No extra retention: every vertex's
     * {@code irNode} already pins the graph.
     */
    Object irGraph;
    private final List<LocalVertex> vertices = new ArrayList<>();
    private final List<LocalVertex> paramVertices = new ArrayList<>();
    private final List<LocalVertex> returnVertices = new ArrayList<>();
    private final List<LocalVertex> invokeVertices = new ArrayList<>();
    /**
     * The node registry: IR node (SSA value) → the first vertex the walk made for it. Read by the engine's atom keys
     * ({@code RecursiveTracking.siteOf}) and call descriptors ({@code callVertexOf}).
     */
    private final java.util.Map<Object, LocalVertex> vertexByNode = new java.util.IdentityHashMap<>();

    LocalFlowGraph(AnalysisMethod method) {
        this.method = method;
    }

    /** Record that the given IR node (SSA value) maps to the given LFG vertex (the first registration wins). */
    void registerNodeVertex(Object node, LocalVertex vertex) {
        if (node != null && vertex != null) {
            vertexByNode.putIfAbsent(node, vertex);
        }
    }

    /** The LFG vertex registered for the given IR node, or {@code null} when the walk never reached it. */
    LocalVertex vertexForNode(Object node) {
        return node != null ? vertexByNode.get(node) : null;
    }

    /** The number of registered nodes (census, print-only). */
    int registrySize() {
        return vertexByNode.size();
    }

    LocalVertex newVertex(VertexKind kind) {
        // All structural mutation and the full-list scans share this monitor.
        synchronized (vertexLock) {
            LocalVertex v = new LocalVertex(this, vertices.size(), kind);
            vertices.add(v);
            if (kind == VertexKind.PARAM_ENTRY) {
                paramVertices.add(v);
            } else if (kind == VertexKind.RETURN_EXIT) {
                returnVertices.add(v);
            } else if (kind == VertexKind.INVOKE_CALLSITE) {
                invokeVertices.add(v);
            }
            return v;
        }
    }

    /** The frame's structural-mutation monitor (mint/scan safety under fwd.threads>1). */
    final Object vertexLock = new Object();

    /** The structural-mutation monitor (mid-solve vertex scans hold it). */
    Object vertexLock() {
        return vertexLock;
    }

    /**
     * One rep-transparent type guard: an {@code instanceof T} IfNode test (or its negation) on a value V. If every type
     * B in V's population satisfies {@code T.isAssignableFrom(B)}, the test always succeeds, at runtime and for every
     * custom representation (reps are subclasses of the traced String type, the same rule the InstanceOfNode lift
     * uses). This requires a real type test, not a lowered class-mirror compare, on the same SSA value the rooting node
     * observes. For such a population the dead arm's subtree is provably unexecuted.
     */
    static final class TypeGuard {
        /** The {@code instanceof} node (its {@link #testedValue} is the tested value). */
        final Node instanceOfNode;
        /** The tested value node (after Pi/proxy skipping). */
        final Node testedValue;
        /** The instanceof's target type. */
        final AnalysisType targetType;
        /**
         * The instanceof is exact (the canonicalized {@code x.getClass() == T.class}, or a leaf-type fold of
         * {@code instanceof FinalT}). An exact guard is usable only in the never direction: exact-pass is a subset of
         * target-assignability, so a population with no target-assignable member passes it for no member (and no
         * substituted rep, as reps are String subtypes inside the assumption keys). But "every member assignable" does
         * not imply "every member passes" (an assignable strict subclass fails the exact test), so the covered direction
         * is non-exact only ({@code wireClassCheckSites} filters exact guards out of the vacuous list).
         */
        final boolean exact;
        /** Whether the IfNode condition is the NEGATION of the instanceof. */
        final boolean negated;
        final Node trueSuccessor;
        final Node falseSuccessor;

        TypeGuard(Node instanceOfNode, Node testedValue, AnalysisType targetType, boolean exact,
                        boolean negated, Node trueSuccessor, Node falseSuccessor) {
            this.instanceOfNode = instanceOfNode;
            this.testedValue = testedValue;
            this.targetType = targetType;
            this.exact = exact;
            this.negated = negated;
            this.trueSuccessor = trueSuccessor;
            this.falseSuccessor = falseSuccessor;
        }

        /** The arm always taken for a fully-covered value population (true arm; negated: false). */
        Node coveredArm() {
            return negated ? falseSuccessor : trueSuccessor;
        }

        /** The arm never taken for a fully-covered value population (the provably dead arm). */
        Node deadArm() {
            return negated ? trueSuccessor : falseSuccessor;
        }
    }

    /**
     * One IR-node scan record collected during the walk, in {@code ir.getNodes()} order, so the SUG vertex-creation
     * pass runs over the same node sequence without re-decoding the method. {@link #node} is from the walk's own graph
     * instance, the same one the vertices' {@code irNode} fields carry, so identity links match by construction.
     */
    static final class SugScanRecord {
        static final byte NEW_INSTANCE = 0;
        static final byte CONST_STRING = 1;
        static final byte CONST_PRIMITIVE = 2;
        static final byte INVOKE = 3;
        static final byte LOAD_FIELD = 4;
        static final byte LOAD_INDEXED = 5;

        final byte kind;
        /** The walk-graph node reference (identity key). */
        final Object node;
        /** The precomputed source-location key ({@code class#method@bci} or the unknown sentinel). */
        final String sourceLocation;
        /** The source key ({@code null} when the node carried no position). */
        final String sourceKey;
        /** NEW_INSTANCE: the instance class name. */
        final String typeName;
        /** NEW_INSTANCE: the resolved instance type. */
        final AnalysisType type;
        /** CONST_STRING: the literal text. */
        final String constText;
        /** CONST_PRIMITIVE: the primitive value (boolean/byte/short/char/int/long narrowed). */
        final long constValue;
        /** INVOKE: the invoke's bci. */
        final int bci;

        SugScanRecord(byte kind, Object node, String sourceLocation, String sourceKey, String typeName,
                        AnalysisType type, String constText, long constValue, int bci) {
            this.kind = kind;
            this.node = node;
            this.sourceLocation = sourceLocation;
            this.sourceKey = sourceKey;
            this.typeName = typeName;
            this.type = type;
            this.constText = constText;
            this.constValue = constValue;
            this.bci = bci;
        }
    }

    /** The per-method scan records (IR order; empty until the walk collects them). */
    final List<SugScanRecord> sugScanRecords = new ArrayList<>();
    /**
     * The walk-graph {@code ParameterNode} stamp types by parameter index (the param-type fallback); {@code null} when
     * the graph has no parameter position information.
     */
    AnalysisType[] paramStampTypes;

    /**
     * All {@code instanceof} IfNodes in the decoded graph (exact ones too, used in the never direction only), built
     * once from the IR in IR iteration order.
     */
    final List<TypeGuard> typeGuards = new ArrayList<>();
    /** Tested-value node -> the guards on that value (identity map — IR nodes). */
    final java.util.Map<Object, List<TypeGuard>> guardsByValue = new java.util.IdentityHashMap<>();

    void addTypeGuard(TypeGuard guard) {
        typeGuards.add(guard);
        guardsByValue.computeIfAbsent(guard.testedValue, k -> new ArrayList<>()).add(guard);
    }

    List<TypeGuard> guardsForValue(Object valueNode) {
        return valueNode != null ? guardsByValue.getOrDefault(valueNode, List.of()) : List.of();
    }

    /** Census: successor reads that threw ({@link #anchorsUnreachableBehind} then answers false). */
    static final java.util.concurrent.atomic.LongAdder SUCC_READ_FAILURES = new java.util.concurrent.atomic.LongAdder();

    /**
     * The blocked-reachability proof: are all of {@code anchors} unreachable from {@code start} when {@code blocked} is
     * removed from the control walk? A deterministic fixpoint over control successors. An unreadable successor
     * structure answers false (fail closed: an anchor may lie behind it).
     */
    static boolean anchorsUnreachableBehind(Node start, java.util.List<Node> anchors, Node blocked) {
        if (start == null || anchors == null || anchors.isEmpty() || blocked == null) {
            return false;
        }
        java.util.Set<Node> anchorSet = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        anchorSet.addAll(anchors);
        java.util.Set<Node> visited = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        java.util.ArrayDeque<Node> work = new java.util.ArrayDeque<>();
        work.add(start);
        while (!work.isEmpty()) {
            Node cur = work.poll();
            if (cur == blocked) {
                continue; // the blocked node's subtree is unreachable through it
            }
            if (!visited.add(cur)) {
                continue;
            }
            if (anchorSet.contains(cur)) {
                continue; // a witness was reached — the final check reports it
            }
            List<Object> succs = controlSuccessors(cur);
            if (succs == null) {
                SUCC_READ_FAILURES.increment();
                return false; // unreadable successors: an anchor may lie behind this node (fail closed)
            }
            for (Object succ : succs) {
                if (succ instanceof Node s) {
                    work.add(s);
                }
            }
        }
        return visited.stream().noneMatch(anchorSet::contains);
    }

    /**
     * The fixed execution witnesses of a rooting node: a FixedNode root is its own anchor; a floating root
     * (GetClassNode) anchors at the first fixed nodes found by BFS over its usages (an over-approximation of "this value
     * was computed here"). FrameState usages are not execution and are skipped.
     */
    static java.util.List<Node> fixedAnchorsOfRoot(Node root) {
        if (root instanceof jdk.graal.compiler.nodes.FixedNode) {
            return List.of(root);
        }
        java.util.List<Node> anchors = new ArrayList<>(2);
        java.util.Set<Node> visited = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        java.util.ArrayDeque<Node> work = new java.util.ArrayDeque<>();
        work.add(root);
        while (!work.isEmpty()) {
            Node cur = work.poll();
            if (!visited.add(cur)) {
                continue;
            }
            if (cur instanceof jdk.graal.compiler.nodes.FixedNode) {
                anchors.add(cur);
                continue; // do not expand past a fixed consumer
            }
            if (cur instanceof jdk.graal.compiler.nodes.FrameState) {
                continue; // debug metadata — not an execution witness
            }
            for (Node use : cur.usages()) {
                work.add(use);
            }
        }
        return anchors;
    }

    /**
     * The IR control successors of a node: next(), successors(), exception edges. The generic arm uses
     * {@link Node#cfgSuccessors()}, not plain {@code successors()}: an {@code EndNode} has no declared successor fields,
     * so a plain walk dies at every merge and any anchor past a merge looks spuriously unreachable when either arm is
     * blocked, so a live arm (e.g. a live-arm {@code toString}) would be wrongly skipped. {@code cfgSuccessors()}
     * crosses the EndNode→MergeNode edge (reaching the merge via one forward end is enough for may-reachability).
     */
    private static List<Object> controlSuccessors(Node node) {
        List<Object> out = new ArrayList<>(4);
        try {
            if (node instanceof jdk.graal.compiler.nodes.FixedWithNextNode fwn) {
                addIf(out, fwn.next());
            } else if (node instanceof jdk.graal.compiler.nodes.Invoke inv) {
                addIf(out, inv.next());
                addIf(out, inv.asNode().successors());
            } else {
                addIf(out, node.cfgSuccessors());
            }
        } catch (Throwable t) {
            return null; // unreadable successor structure: the caller fails closed
        }
        return out;
    }

    private static void addIf(List<Object> out, Object succ) {
        if (succ != null) {
            out.add(succ);
        }
    }

    private static void addIf(List<Object> out, Iterable<? extends Object> succs) {
        if (succs != null) {
            for (Object s : succs) {
                addIf(out, s);
            }
        }
    }

    AnalysisMethod getMethod() {
        return method;
    }

    List<LocalVertex> getVertices() {
        return Collections.unmodifiableList(vertices);
    }

    List<LocalVertex> getParamVertices() {
        return Collections.unmodifiableList(paramVertices);
    }

    List<LocalVertex> getReturnVertices() {
        return Collections.unmodifiableList(returnVertices);
    }

    List<LocalVertex> getInvokeVertices() {
        return Collections.unmodifiableList(invokeVertices);
    }

    LocalVertex getParamVertex(int paramIdx) {
        for (LocalVertex v : paramVertices) {
            if (v.paramIndex == paramIdx) {
                return v;
            }
        }
        return null;
    }
}
