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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.BitSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.LoadFieldTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.MethodTypeFlow;
import com.oracle.graal.pointsto.flow.NewInstanceTypeFlow;
import com.oracle.graal.pointsto.flow.OffsetLoadTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;

import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.core.common.type.ObjectStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeInputList;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode;
import jdk.graal.compiler.nodes.java.AccessIndexedNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.LoadIndexedNode;
import jdk.graal.compiler.nodes.java.NewArrayNode;
import jdk.graal.compiler.nodes.java.NewInstanceNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.java.StoreIndexedNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.VirtualObjectNode;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The LFG (local flow graph) construction: the per-method IR walks and seed creation, split out of
 * {@link SugBuilderV2} (whose indices and helpers it reads). It builds only the products with a live reader (see
 * {@link LocalFlowGraph}); the value-driven walk ({@link #walkSSAFromParam}) and its seeds define the traversal.
 */
final class LfgWalk {
    /** The owning builder. */
    private final SugBuilderV2 builder;

    /**
     * The raw-memory use classes in {@code com.oracle.svm.core.genscavenge}, which this module does not depend on:
     * matched by exact class name (never by package or suffix).
     */
    static final Set<String> RAW_MEMORY_EXACT_CLASS_NAMES = Set.of(
                    "com.oracle.svm.core.genscavenge.graal.nodes.FormatObjectNode",
                    "com.oracle.svm.core.genscavenge.graal.nodes.FormatArrayNode",
                    "com.oracle.svm.core.genscavenge.graal.nodes.FormatPodNode",
                    "com.oracle.svm.core.genscavenge.graal.nodes.FormatStoredContinuationNode",
                    "com.oracle.svm.core.genscavenge.graal.ForcedSerialPostWriteBarrier");

    /** The class half of {@link #isRawMemoryUse}. */
    static boolean isRawMemoryClass(Node u) {
        return u instanceof jdk.graal.compiler.nodes.extended.JavaWriteNode ||
                        u instanceof jdk.graal.compiler.nodes.extended.JavaReadNode ||
                        u instanceof com.oracle.svm.core.graal.nodes.CInterfaceWriteNode ||
                        u instanceof com.oracle.svm.core.graal.nodes.CInterfaceReadNode ||
                        u instanceof jdk.graal.compiler.nodes.memory.ReadNode ||
                        u instanceof jdk.graal.compiler.nodes.memory.WriteNode ||
                        u instanceof jdk.graal.compiler.nodes.memory.address.OffsetAddressNode ||
                        u instanceof jdk.graal.compiler.nodes.memory.address.IndexAddressNode ||
                        u instanceof jdk.graal.compiler.nodes.ComputeObjectAddressNode ||
                        u instanceof jdk.graal.compiler.word.WordCastNode ||
                        u instanceof jdk.graal.compiler.nodes.java.LogicCompareAndSwapNode ||
                        u instanceof jdk.graal.compiler.nodes.java.ValueCompareAndSwapNode ||
                        u instanceof jdk.graal.compiler.nodes.java.AtomicReadAndAddNode ||
                        u instanceof jdk.graal.compiler.nodes.extended.PublishWritesNode ||
                        u instanceof com.oracle.svm.core.graal.nodes.WriteHeapBaseNode ||
                        u instanceof com.oracle.svm.core.graal.nodes.SubstrateCompressionNode ||
                        u instanceof com.oracle.svm.core.graal.nodes.NewPodInstanceNode ||
                        u instanceof com.oracle.svm.core.nodes.foreign.MemoryArenaValidInScopeNode ||
                        RAW_MEMORY_EXACT_CLASS_NAMES.contains(u.getClass().getName());
    }

    /**
     * Is {@code use} a raw-memory use of {@code walked}? Every input role counts, except for {@code AtomicReadAndAdd},
     * restricted to the reference base ({@code object}); its delta is numeric.
     *
     * <p>A raw/Unsafe/CAS/{@code AtomicReadAndWrite}-class use of a walked value is the named refusal
     * {@code UNSAFE_ACCESS}, never the generic passthrough, which would silently drop the value's store into unmodelled
     * memory.
     *
     * <p>A lowered raw-memory / word / address use of a walked value ({@code JavaWrite}, {@code WordCast}, {@code ComputeObjectAddress}, ...: the value
     * leaves typed memory) is the same named refusal {@code UNSAFE_ACCESS}.
     */
    static boolean isRawMemoryUse(Node use, Node walked) {
        if (use instanceof jdk.graal.compiler.nodes.java.AtomicReadAndAddNode rra) {
            return rra.object() == walked;
        }
        return isRawMemoryClass(use);
    }

    /** The stringy types of {@link #isNonStringyReference} (String + the builder family); set once per analysis. */
    static volatile jdk.vm.ci.meta.ResolvedJavaType[] stringyRawMemTypes;

    static final String[] STRINGY_RAW_MEM_TYPE_NAMES = new String[]{"java.lang.String", "java.lang.AbstractStringBuilder", "java.lang.StringBuilder",
                    "java.lang.StringBuffer", "java.io.StringWriter", AccumulatorWhitelist.JOINER};

    static void initStringyRawMemTypes(SugBuilderV2 b) {
        if (b == null || b.bb == null) {
            return;
        }
        List<jdk.vm.ci.meta.ResolvedJavaType> ts = new java.util.ArrayList<>();
        for (String n : STRINGY_RAW_MEM_TYPE_NAMES) {
            jdk.vm.ci.meta.ResolvedJavaType t = b.resolveAnalysisTypeByName(n);
            if (t == null) {
                stringyRawMemTypes = null; // an unresolvable stringy type: the exemption exempts nothing (strict)
                return;
            }
            ts.add(t);
        }
        stringyRawMemTypes = ts.toArray(new jdk.vm.ci.meta.ResolvedJavaType[0]);
    }

    /**
     * Is {@code walked} a reference that can never be a stringy object (a String, a representation, a builder)? True
     * only for an {@code ObjectStamp} with a known type that is neither a supertype nor a subtype of any stringy type
     * (arrays by the same test). Anything else answers false (strict).
     */
    static boolean isNonStringyReference(Node walked, jdk.vm.ci.meta.ResolvedJavaType[] stringy) {
        if (stringy == null || !(walked instanceof ValueNode wv) || !(wv.stamp(NodeView.DEFAULT) instanceof ObjectStamp os)) {
            return false;
        }
        jdk.vm.ci.meta.ResolvedJavaType t = os.type();
        if (t == null) {
            return false;
        }
        try {
            for (jdk.vm.ci.meta.ResolvedJavaType s : stringy) {
                if (t.isAssignableFrom(s) || s.isAssignableFrom(t)) {
                    return false;
                }
            }
        } catch (Throwable ex) {
            return false; // a type-universe mismatch: strict
        }
        return true;
    }

    /**
     * The raw-memory refusal's exemptions.
     * <ul>
     * <li>A primitive walked value: content derived from the string (e.g. {@code (byte) charAt(i)} written to a C
     * buffer) is rep-invariant; a primitive can carry the string's address only after a reference-to-word conversion,
     * which is refused where the reference is walked.</li>
     * <li>A walked value that is only the address input of a memory access: its reference base was classified where
     * the address was formed.</li>
     * <li>A non-stringy reference ({@link #isNonStringyReference}, e.g. a String's {@code byte[] value}). A
     * representation differs from a String only in identity, class, {@code value == null} and its overridden methods,
     * so a raw access of an object that is not the string observes nothing of the representation; the one
     * representation-dependent step, reading the String's {@code value}, is the raw-read usage at the load
     * (the raw-read usage) or the method usage {@code value()}. Builder types stay strict: they are not
     * representations, but an accumulator candidate's buffer is shared zero-copy by {@code ACCUMULATOR_VIEW}
     * ({@code StringView.create(StringBuilder)}), so a raw write into it after the extraction would be visible.</li>
     * </ul>
     * The Unsafe-family and raw-memory checks are also re-checked for a use the walk already visited.
     */
    static boolean rawMemExempt(Node use, Node walked) {
        if (walked instanceof ValueNode wv && wv.stamp(NodeView.DEFAULT) instanceof jdk.graal.compiler.core.common.type.PrimitiveStamp) {
            return true;
        }
        if (isNonStringyReference(walked, stringyRawMemTypes)) {
            return true;
        }
        if (use instanceof jdk.graal.compiler.nodes.memory.AddressableMemoryAccess ama && ama.getAddress() == walked) {
            int positions = 0;
            for (Node in : use.inputs()) {
                if (in == walked) {
                    positions++;
                }
            }
            return positions == 1; // the address is its only role in the access
        }
        return false;
    }

    /**
     * The raw-read usage vertex: the CLASS_CHECK vertex shape (arm anchor = the load) marked with the field name, so its
     * SUG site ({@code wireClassCheckSites}) carries the raw-read usage name. No walk continuation.
     *
     * <p>The raw-read usage: a raw read of a {@code java.lang.String}
     * representation field ({@code value}, {@code coder}; {@link SugNameTables#rawStringFieldUsageName}) on the walked
     * value is a usage of the value anywhere, inside String bodies and outside (SVM {@code UninterruptibleUtils$String}
     * reads {@code value} through an {@code @Alias}). This is the field usage kind; a call {@code x.value()} is the
     * method usage ({@code ForwardFixpoint.targetUsageSite}). The heuristics' per-rep whitelist decides. The LOAD
     * vertex and the walk of the loaded value are unaffected.
     */
    static void mintRawStringFieldReadUsage(LocalFlowGraph lfg, LocalFlowGraph.LocalVertex curVertex, LoadFieldNode lfn, Node cur) {
        LocalFlowGraph.LocalVertex rv = lfg.newVertex(LocalFlowGraph.VertexKind.CLASS_CHECK);
        rv.rawStringField = lfn.field().getName();
        rv.label = "String." + SugNameTables.rawStringFieldUsageName(rv.rawStringField);
        // irNode stays null: the LOAD vertex owns the node (findLoadVertexByNode matches on irNode).
        rv.armAnchor = lfn;
        NodeSourcePosition pos = lfn.getNodeSourcePosition();
        if (pos != null) {
            rv.bci = pos.getBCI();
        }
        rv.from = curVertex;
    }

    /** Is {@code use} (a ValueNode) an Unsafe-family use or a non-exempt raw-memory use of {@code walked}? */
    static boolean isRefusedMemoryUse(Node use, Node walked) {
        if (!(use instanceof ValueNode)) {
            return false;
        }
        if (RecursiveTracking.isUnsafeFamily(use)) {
            return true;
        }
        if (use instanceof com.oracle.svm.core.graal.thread.VMThreadLocalAccess &&
                        !(walked instanceof ValueNode wv && wv.stamp(NodeView.DEFAULT) instanceof jdk.graal.compiler.core.common.type.PrimitiveStamp)) {
            return true; // a reference stored into an SVM VM thread-local: a named refusal
        }
        return isRawMemoryUse(use, walked) && !rawMemExempt(use, walked);
    }

    LfgWalk(SugBuilderV2 builder) {
        this.builder = builder;
    }

    /** The owning builder (graph decode + field/method resolution). */
    SugBuilderV2 builder() {
        return builder;
    }

    /**
     * Builds the LFG of every reachable non-stub method with a flows graph. A non-stub method whose IR is undecodable
     * makes {@code buildLocalFlowForMethod} throw, aborting the analysis (no profile).
     */
    Map<AnalysisMethod, LocalFlowGraph> buildLocalFlowGraphs(AnalysisUniverse universe) {
        Map<AnalysisMethod, LocalFlowGraph> localFlows = new LinkedHashMap<>();
        if (builder.pta == null) {
            return localFlows;
        }
        long annT0 = System.nanoTime();
        for (AnalysisMethod am : universe.getMethods()) {
            if (!am.isReachable() || !(am instanceof PointsToAnalysisMethod ptm)) {
                continue;
            }
            MethodTypeFlow mtf = ptm.getTypeFlow();
            if (mtf == null || !mtf.flowsGraphCreated()) {
                continue;
            }
            MethodFlowsGraph mfg = mtf.getMethodFlowsGraph();
            if (mfg.isStub()) {
                continue;
            }
            LocalFlowGraph lfg = buildLocalFlowForMethod(am, mfg);
            localFlows.put(am, lfg);
            // Arg-stamp collection on the same decoded graph (no extra decode); refs resolve at finalize below.
            builder.argStampResolution.collect(am, builder.decodeIrGraph(am));
        }
        builder.argStampResolution.finalizeIndex();
        System.out.println("[sug-summary] lfgWalkTotalMs=" + ((System.nanoTime() - annT0) / 1_000_000));
        printCensus(localFlows);
        return localFlows;
    }

    /** Print-only (no verdict reads it): the construction's size, per vertex kind. */
    private static void printCensus(Map<AnalysisMethod, LocalFlowGraph> localFlows) {
        long vertices = 0;
        long edges = 0;
        long registry = 0;
        long guards = 0;
        long[] byKind = new long[LocalFlowGraph.VertexKind.values().length];
        for (LocalFlowGraph lfg : localFlows.values()) {
            for (LocalFlowGraph.LocalVertex v : lfg.getVertices()) {
                vertices++;
                byKind[v.kind.ordinal()]++;
            }
            for (LocalFlowGraph.LocalVertex v : lfg.getVertices()) {
                if (v.from != null) {
                    edges++; // the creator links (one in-edge per vertex, from its creator)
                }
            }
            registry += lfg.registrySize();
            guards += lfg.guardsByValue.size();
        }
        StringBuilder sb = new StringBuilder("[lfg-census] methods=").append(localFlows.size()).append(" vertices=").append(vertices)
                        .append(" edges=").append(edges).append(" registry=").append(registry)
                        .append(" guardedValues=").append(guards).append(" byKind={");
        for (LocalFlowGraph.VertexKind k : LocalFlowGraph.VertexKind.values()) {
            sb.append(k.ordinal() == 0 ? "" : ", ").append(k).append('=').append(byKind[k.ordinal()]);
        }
        System.out.println(sb.append('}'));
    }

    /** Build a local flow graph for a single method by walking its IR. */
    private LocalFlowGraph buildLocalFlowForMethod(AnalysisMethod method, MethodFlowsGraph mfg) {
        StructuredGraph ir = builder.decodeIrGraph(method);
        if (ir == null) {
            // Undecodable IR is a hard error: it propagates to StringAnalysisFeature.buildSugAndRunHeuristics, where the
            // child catches it, dumps no profile and exits 0. The parent then builds without optimization (sound).
            throw new RuntimeException("[string-analysis] Undecodable IR for method " + method +
                            " — cannot build local flow graph. Aborting analysis (no profile will be produced).");
        }
        return buildLocalFlowFromGraph(method, mfg, ir);
    }

    /**
     * The pre-warm entry, IR leg: parse a no-IR dispatch target so an LFG can be force-built for it. The IR is
     * force-parsed when points-to never decoded it ({@code SugBuilderV2.forceParseIrGraph}) and the same walk runs over
     * it with {@code mfg == null}: PARAM_ENTRY vertices come from the IR's {@link ParameterNode}s and invokes inside
     * are unresolvable-invoke corners, which keep their conservative evidence under another reason. Strictly
     * information-adding versus the MISSING_IR fact it replaces. Returns {@code null} at every failure corner (no code,
     * stub, parse failure): the MISSING_IR fact stays.
     * <p>
     * This leg is independent per target (parallelizable); {@link #finish}, the walk leg, is composed serially in the
     * sorted insert order.
     */
    public StructuredGraph preparse(AnalysisMethod method) {
        if (method == null || builder.pta == null || !(method instanceof PointsToAnalysisMethod ptm)) {
            return null;
        }
        if (method.getCode() == null) {
            return null; // native/abstract: no body to parse (the NO_CODE class)
        }
        MethodTypeFlow mtf = ptm.getTypeFlow();
        if (mtf != null && mtf.flowsGraphCreated() && mtf.getMethodFlowsGraph().isStub()) {
            return null; // undecodable by design: the MISSING_IR fact stays
        }
        try {
            return method.getAnalyzedGraph() != null
                            ? builder.decodeIrGraph(method)
                            : builder.forceParseIrGraph(method);
        } catch (Throwable t) {
            return null; // the honest corner: MISSING_IR stays for this target
        }
    }

    /**
     * The walk leg of the pre-warm entry ({@link #preparse}): the shared LFG construction with the re-derived
     * {@code mfg} (nothing between the legs mutates method-flow state). Returns {@code null} at every failure corner.
     */
    public LocalFlowGraph finish(AnalysisMethod method, StructuredGraph ir) {
        if (method == null || ir == null || builder.pta == null || !(method instanceof PointsToAnalysisMethod ptm)) {
            return null;
        }
        MethodTypeFlow mtf = ptm.getTypeFlow();
        MethodFlowsGraph mfg = null;
        if (mtf != null && mtf.flowsGraphCreated()) {
            mfg = mtf.getMethodFlowsGraph();
            if (mfg.isStub()) {
                return null;
            }
        }
        try {
            return buildLocalFlowFromGraph(method, mfg, ir);
        } catch (Throwable t) {
            return null; // the honest corner: MISSING_IR stays for this target
        }
    }

    /**
     * The shared post-decode LFG construction: param vertices (from the flows graph, or from the IR's
     * {@link ParameterNode}s when {@code mfg} is null), the param walks, the stringy-seed walks and the post passes.
     * Package-private for tests.
     */
    LocalFlowGraph buildLocalFlowFromGraph(AnalysisMethod method, MethodFlowsGraph mfg, StructuredGraph ir) {
        LocalFlowGraph lfg = new LocalFlowGraph(method);
        lfg.irGraph = ir;
        TypeFlow<?>[] paramFlows = mfg != null ? mfg.getParameters() : null;
        int paramCount = paramFlows != null ? paramFlows.length : 0;
        if (paramFlows != null) {
            for (int i = 0; i < paramCount; i++) {
                LocalFlowGraph.LocalVertex pv = lfg.newVertex(LocalFlowGraph.VertexKind.PARAM_ENTRY);
                pv.paramIndex = i;
                pv.typeFlow = paramFlows[i];
            }
        } else {
            // Pre-built form: no points-to flows; declaredType from the IR stamp (the dispatch identity seeds use).
            for (Node n : ir.getNodes()) {
                if (n instanceof ParameterNode pn) {
                    LocalFlowGraph.LocalVertex pv = lfg.newVertex(LocalFlowGraph.VertexKind.PARAM_ENTRY);
                    pv.paramIndex = pn.index();
                    Stamp stamp = pn.stamp(NodeView.DEFAULT);
                    if (stamp instanceof ObjectStamp os && os.type() != null) {
                        pv.declaredType = builder.resolveAnalysisType(os.type());
                    }
                }
            }
        }
        // One visited set per param, so a multi-param invoke is captured for every param.
        for (Node n : ir.getNodes()) {
            if (!(n instanceof ParameterNode pn)) {
                continue;
            }
            int paramIdx = pn.index();
            LocalFlowGraph.LocalVertex paramVertex = lfg.getParamVertex(paramIdx);
            if (paramVertex == null) {
                continue;
            }
            lfg.registerNodeVertex(pn, paramVertex);
            walkSSAFromParam(lfg, pn, paramVertex, method, new HashSet<>());
        }
        // Walk from all string-typed value sources too (see walkFromAllStringySeeds).
        walkFromAllStringySeeds(lfg, ir, method);
        // The rep-transparent type-guard inventory, read by the arm skip (ForwardFixpoint.StrackSites.armDead).
        collectTypeGuards(lfg, ir, method);
        // The Phase-A usage sites of node-shaped class checks and raw String-field reads, on this graph (same identity).
        wireClassCheckSites(lfg, ir, method);
        // The SUG scan records, so SUG vertex creation never re-decodes the method.
        collectSugScanRecords(lfg, ir, method);
        // Link RETURN_EXIT vertices to the FormalReturnTypeFlow so the summary transfer's passthrough saturation gate
        // can act as the tag barrier; without it, false cross-caller tag associations arise. (Pre-built form: the
        // gate stays off.)
        TypeFlow<?> formalReturn = mfg != null ? mfg.getReturnFlow() : null;
        if (formalReturn != null) {
            for (LocalFlowGraph.LocalVertex rv : lfg.getReturnVertices()) {
                rv.typeFlow = formalReturn;
            }
        }
        return lfg;
    }

    /**
     * The value-driven walk: follow the SSA usages of a node (a ParameterNode or a stringy seed), minting the vertices
     * with a live reader: the node registry (every walked node maps to its first vertex, the atom keys), one
     * INVOKE_CALLSITE vertex per resolvable call plus its {@code invoke-return} vertex, one RETURN_EXIT per return, the
     * LOAD/ARRAY_LOAD carriers, the CLASS_CHECK vertices and the passthrough INTERNAL vertices. Each vertex records its
     * creator ({@code from}). No depth limit; one visited set per walk. The walk continues through invoke results,
     * loads and passthroughs; it stops at stores, returns, refused memory uses and every other use.
     * <p>
     * IfNode conditions are not classified: the walk mints nothing for an IfNode (arm invariance under the substitution
     * contract, below). The rep-transparent {@code instanceof} guards live only in the guard inventory
     * ({@link #collectTypeGuards}), which the record-time arm skip consults. Package-private for tests.
     */
    void walkSSAFromParam(LocalFlowGraph lfg, Node startNode, LocalFlowGraph.LocalVertex startVertex,
                    AnalysisMethod method, Set<Node> visited) {
        Deque<Node> worklist = new ArrayDeque<>();
        Deque<LocalFlowGraph.LocalVertex> vertexWorklist = new ArrayDeque<>();
        worklist.add(startNode);
        vertexWorklist.add(startVertex);
        visited.add(startNode);
        while (!worklist.isEmpty()) {
            Node cur = worklist.pollFirst();
            LocalFlowGraph.LocalVertex curVertex = vertexWorklist.pollFirst();
            lfg.registerNodeVertex(cur, curVertex);
            for (Node use : cur.usages()) {
                // cur is the store's object/array, not its value: skip without marking visited, so the value side can
                // still process the store.
                if (use instanceof StoreFieldNode sfn && sfn.object() == cur) {
                    continue;
                }
                if (use instanceof StoreIndexedNode sin && sin.array() == cur) {
                    continue;
                }
                if (!visited.add(use)) {
                    // A revisit mints nothing.
                    continue;
                }
                if (use instanceof Invoke inv) {
                    InvokeTypeFlow invFlow = builder.invokeFlowOf(method, inv);
                    if (invFlow == null) {
                        // No type flow (unresolvable, or a never-executed direct target): no vertex, no continuation.
                        continue;
                    }
                    LocalFlowGraph.LocalVertex invokeVertex = newCallVertex(lfg, curVertex, invFlow, inv);
                    TypeFlow<?> ret = invFlow.getActualReturn();
                    if (ret != null) {
                        LocalFlowGraph.LocalVertex retVertex = newResultVertex(lfg, invokeVertex, ret);
                        lfg.registerNodeVertex(use, retVertex);
                        // Continue at the result (e.g. toString() -> value() on the result)
                        worklist.add(use);
                        vertexWorklist.add(retVertex);
                    }
                    continue;
                }
                if (use instanceof ReturnNode) {
                    lfg.newVertex(LocalFlowGraph.VertexKind.RETURN_EXIT).from = curVertex;
                    continue;
                }
                if (use instanceof StoreFieldNode || use instanceof StoreIndexedNode) {
                    // The walked value is the STORED value: no vertex, no continuation.
                    continue;
                }
                if (use instanceof LoadFieldNode lfn) {
                    LocalFlowGraph.LocalVertex loadVertex = lfg.newVertex(LocalFlowGraph.VertexKind.LOAD);
                    loadVertex.irNode = lfn;
                    loadVertex.label = "load:" + lfn.field().getName();
                    ResolvedJavaField rjf = lfn.field();
                    if (rjf != null) {
                        AnalysisField af = resolveAnalysisField(rjf);
                        loadVertex.field = af;
                    }
                    ResolvedJavaType fieldDeclType = lfn.field().getDeclaringClass();
                    String fieldDeclName = fieldDeclType != null ? fieldDeclType.toJavaName(true) : null;
                    if (fieldDeclName != null && SugNameTables.STRINGY_INVOKE_RECEIVERS.contains(fieldDeclName)) {
                        String fieldTypeName = lfn.field().getType() != null ? lfn.field().getType().toJavaName(true) : null;
                        if (fieldTypeName != null && fieldTypeName.contains("[")) {
                            loadVertex.label = "field-unsafe:" + lfn.field().getName();
                        }
                    }
                    // The load site's type flow (by bci), so the SUG vertex of the loaded value maps to this LOAD vertex.
                    NodeSourcePosition lfnPos = lfn.getNodeSourcePosition();
                    if (lfnPos != null) {
                        LoadFieldTypeFlow.LoadInstanceFieldTypeFlow loadFlow = resolveLoadFieldByBci(method, lfnPos.getBCI());
                        if (loadFlow != null) {
                            loadVertex.typeFlow = loadFlow;
                        }
                    }
                    loadVertex.from = curVertex;
                    lfg.registerNodeVertex(use, loadVertex);
                    if (fieldDeclName != null && fieldDeclName.equals("java.lang.String") && !lfn.isStatic() &&
                                    lfn.object() == cur && SugNameTables.rawStringFieldUsageName(lfn.field().getName()) != null) {
                        mintRawStringFieldReadUsage(lfg, curVertex, lfn, cur);
                    }
                    // Continue at the loaded value (e.g. this.input.substring(...)), so its invokes get call vertices.
                    worklist.add(use);
                    vertexWorklist.add(loadVertex);
                    continue;
                }
                if (use instanceof LoadIndexedNode lin) {
                    LocalFlowGraph.LocalVertex loadVertex = lfg.newVertex(LocalFlowGraph.VertexKind.ARRAY_LOAD);
                    loadVertex.irNode = lin;
                    loadVertex.label = "loadIndexed";
                    AnalysisType elementType = resolveArrayElementType(lin, method);
                    loadVertex.arrayType = elementType;
                    NodeSourcePosition linPos = lin.getNodeSourcePosition();
                    if (linPos != null) {
                        OffsetLoadTypeFlow.LoadIndexedTypeFlow loadFlow = resolveLoadIndexedByBci(method, linPos.getBCI());
                        if (loadFlow != null) {
                            loadVertex.typeFlow = loadFlow;
                            if (elementType == null) {
                                loadVertex.arrayType = loadFlow.getDeclaredType();
                            }
                        }
                    }
                    loadVertex.from = curVertex;
                    lfg.registerNodeVertex(use, loadVertex);
                    // Continue at the loaded element (e.g. array[i].substring(...)).
                    worklist.add(use);
                    vertexWorklist.add(loadVertex);
                    continue;
                }
                // Exception bookkeeping and compiler metadata do not observe String identity.
                if (use instanceof BytecodeExceptionNode) {
                    continue;
                }
                String useClassName = use.getClass().getSimpleName();
                /*
                 * The unified usage model ("record usages + determine arms"). The substitution contract: all
                 * invocation behaviour is identical regardless of the representation decision; the only exception is
                 * strict class checks (getClass-shaped; not instanceof, which is rep-invariant because reps are
                 * Strings). This holds for non-whitelisted usages too, which never execute under substitution because
                 * a present non-whitelisted usage rejects the candidate. So any branch fed by invoke results on the
                 * traced value is arm-invariant under admission; the whitelist verdict is the only filter; a
                 * non-whitelisted call that is never recorded is the one soundness leak (silent admit).
                 *
                 * getClass is a usage, not an effect: a GetClassNode on the walked value records a CLASS_CHECK vertex
                 * (the unintrinsified getClass invoke and the reflective Class.isInstance/Class.cast shapes are
                 * recorded at their call vertices). getClass is not whitelisted for any rep, so a live-arm class check
                 * rejects through the ordinary verdict. Usages from a provably dead arm are never recorded: the arm
                 * skip (blockFlow.classCheckUsageSkipped) decides liveness per origin block, which keeps a dead-arm
                 * getClass from rejecting everything. The Class result is a different value: no walk continuation.
                 */
                if (useClassName.equals("GetClassNode")) {
                    LocalFlowGraph.LocalVertex classCheck = lfg.newVertex(LocalFlowGraph.VertexKind.CLASS_CHECK);
                    classCheck.label = "getClass";
                    classCheck.irNode = use;
                    classCheck.armAnchor = use;
                    NodeSourcePosition ccPos = ((ValueNode) use).getNodeSourcePosition();
                    if (ccPos != null) {
                        classCheck.bci = ccPos.getBCI();
                    }
                    classCheck.from = curVertex;
                    lfg.registerNodeVertex(use, classCheck);
                    continue;
                }
                if (useClassName.equals("UnwindNode")) {
                    // A thrown walked value: no vertex, no continuation.
                    continue;
                }
                if (useClassName.equals("IfNode")) {
                    // The walk mints nothing for an IfNode. Guard-shaped conditions (IsNull: nullness is rep-invariant;
                    // InstanceOf: the tested type is a supertype of every rep) feed the guard inventory
                    // (collectTypeGuards) for the arm skip; every other condition, including ones fed by invoke results
                    // on the traced value (str.coder()-fed branches), is arm-invariant under admission by the contract:
                    // both arms' usages are recorded and judged by the whitelist alone.
                    continue;
                }
                if (useClassName.equals("BlackholeNode")) {
                    continue;
                }
                if (useClassName.equals("FrameState")) {
                    continue;
                }
                // Virtualization metadata (MaterializedObjectState, VirtualObjectState): deoptimization bookkeeping
                // like FrameState (VirtualState, State inputs only, never scheduled or lowered, removed before code
                // gen), so no runtime instruction observes the walked value through them. A walk from a virtualized
                // allocation seed hits them as uses; treating them as unhandled would mint INCOMPLETE_TRAVERSAL with no
                // runtime counterpart.
                if (use instanceof jdk.graal.compiler.nodes.virtual.EscapeObjectState) {
                    continue;
                }
                // A call target: process its Invoke directly (not as a passthrough) when cur is an argument.
                if (use instanceof MethodCallTargetNode mctn) {
                    int argIdx = -1;
                    NodeInputList<ValueNode> args = mctn.arguments();
                    for (int ai = 0; ai < args.size(); ai++) {
                        if (args.get(ai) == cur) {
                            argIdx = ai;
                            break;
                        }
                    }
                    if (argIdx < 0) {
                        continue; // not an argument of this call target: no vertex, no continuation
                    }
                    Invoke invoke = null;
                    for (Node mctnUse : mctn.usages()) {
                        if (mctnUse instanceof Invoke i) {
                            invoke = i;
                            break;
                        }
                    }
                    if (invoke == null) {
                        continue;
                    }
                    InvokeTypeFlow invFlow = builder.invokeFlowOf(method, invoke);
                    if (invFlow == null) {
                        continue; // as for the direct Invoke: no vertex, no continuation
                    }
                    LocalFlowGraph.LocalVertex invokeVertex = newCallVertex(lfg, curVertex, invFlow, invoke);
                    TypeFlow<?> ret = invFlow.getActualReturn();
                    if (ret != null) {
                        LocalFlowGraph.LocalVertex retVertex = newResultVertex(lfg, invokeVertex, ret);
                        lfg.registerNodeVertex(invoke.asNode(), retVertex);
                        worklist.add(invoke.asNode());
                        vertexWorklist.add(retVertex);
                    }
                    continue;
                }
                if (use instanceof InstanceOfNode ion && ion.type() != null && ion.type().isExact()) {
                    if (instanceofSourceFoldAllowed(ion, method, builder::resolveAnalysisType)) {
                        // A proven instanceof-source fold with an out-of-cone target, or a checkcast-source fold, is not a
                        // strict class check (see instanceofSourceFoldAllowed): the ordinary passthrough below.
                    } else {
                        // The folded class-mirror compare: Graal canonicalizes x.getClass() == T.class into an exact
                        // InstanceOfNode (ObjectEqualsOp.canonicalizeSymmetricConstant). An exact type test is not
                        // rep-transparent (a rep fails exact-instanceof-String as it fails getClass() == String.class), so it
                        // is a strict class check, recorded as a CLASS_CHECK usage. Passing it through would be a
                        // silent-admit hole. Its IfNode also enters the guard inventory (never-direction only, see
                        // collectTypeGuards); that does not affect this recording.
                        LocalFlowGraph.LocalVertex classCheck = lfg.newVertex(LocalFlowGraph.VertexKind.CLASS_CHECK);
                        classCheck.label = "exact-instanceof";
                        classCheck.irNode = use;
                        classCheck.armAnchor = use;
                        NodeSourcePosition eiPos = ion.getNodeSourcePosition();
                        if (eiPos != null) {
                            classCheck.bci = eiPos.getBCI();
                        }
                        classCheck.from = curVertex;
                        lfg.registerNodeVertex(use, classCheck);
                        continue;
                    }
                }
                boolean unsafeUse = use instanceof ValueNode && RecursiveTracking.isUnsafeFamily(use);
                // The lowered raw-memory / word / address uses (see isRawMemoryUse).
                boolean rawMemUse = !unsafeUse && use instanceof ValueNode && isRawMemoryUse(use, cur) && !rawMemExempt(use, cur);
                // A reference stored into an SVM VM thread-local.
                boolean vmtlUse = !unsafeUse && !rawMemUse && use instanceof com.oracle.svm.core.graal.thread.VMThreadLocalAccess &&
                                use instanceof ValueNode && !(cur instanceof ValueNode tlcv && tlcv.stamp(NodeView.DEFAULT) instanceof jdk.graal.compiler.core.common.type.PrimitiveStamp);
                if (unsafeUse || rawMemUse || vmtlUse) {
                    // An input of a raw memory access or a VM thread-local store: not a passthrough. No continuation and no
                    // registration (nothing may map the access's result onto the walked value); the engine names the
                    // refusal on the IR (UNSAFE_ACCESS / THREAD_LOCAL_UNMODELLED).
                    continue;
                }
                if (use instanceof ValueNode vn) {
                    LocalFlowGraph.LocalVertex internalVertex = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
                    internalVertex.label = useClassName;
                    if (use instanceof jdk.graal.compiler.nodes.virtual.CommitAllocationNode) {
                        // A field value of a materialisation: the vertex carries the commit (ContextPolicy.siteKey).
                        internalVertex.irNode = use;
                    }
                    internalVertex.typeFlow = curVertex.typeFlow;
                    if (use instanceof PiNode || use instanceof PhiNode) {
                        // Pi/Phi carry their IR node for ContextPolicy.siteKey (Pi/Phi-scoped so the keys stay stable).
                        internalVertex.irNode = use;
                    }
                    internalVertex.from = curVertex;
                    lfg.registerNodeVertex(use, internalVertex);
                    worklist.add(use);
                    vertexWorklist.add(internalVertex);
                    continue;
                }
                // an unhandled non-value use: no vertex, no continuation
            }
        }
    }

    /** A resolvable call reached by the walk: its INVOKE_CALLSITE vertex (the LFG half of {@code callersOf}). */
    private static LocalFlowGraph.LocalVertex newCallVertex(LocalFlowGraph lfg, LocalFlowGraph.LocalVertex creator, InvokeTypeFlow invFlow, Invoke invoke) {
        LocalFlowGraph.LocalVertex v = lfg.newVertex(LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
        v.calleeMethod = invFlow.getTargetMethod();
        v.bci = StringAnalysisChildInlining.pointsToBci(invoke);
        v.typeFlow = invFlow;
        v.irNode = invoke.asNode();
        v.from = creator;
        return v;
    }

    /** The call's {@code invoke-return} INTERNAL vertex (at most one per call vertex: {@code call.result}). */
    private static LocalFlowGraph.LocalVertex newResultVertex(LocalFlowGraph lfg, LocalFlowGraph.LocalVertex call, TypeFlow<?> ret) {
        LocalFlowGraph.LocalVertex r = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        r.label = "invoke-return";
        r.typeFlow = ret;
        r.from = call;
        call.result = r;
        return r;
    }

    /**
     * Walk from all string-typed value sources, not just {@link ParameterNode}s. A parameter-only walk misses invokes
     * on values that do not flow from a parameter ({@code System.getProperty("x").indexOf(".")},
     * {@code "literal".substring()}, {@code this.field.substring()}): their SUG invoke vertex would be unmapped, the
     * fixpoint would have no seed and dangerous candidates would be admitted. Seeds: stringy invoke returns, String
     * constants, stringy allocations, stringy field and array loads, plus the container seeds. Each seed has its own
     * visited set; cross-walk duplicate vertices are deduplicated by the hierarchy's {@code ConnectorKey}.
     */
    private void walkFromAllStringySeeds(LocalFlowGraph lfg, StructuredGraph ir, AnalysisMethod method) {
        for (Node n : ir.getNodes()) {
            if (n instanceof Invoke inv) {
                seedFromInvokeReturn(lfg, inv, method);
            } else if (n instanceof ConstantNode cn) {
                seedFromConstantNode(lfg, cn, method);
            } else if (n instanceof NewInstanceNode nin) {
                seedFromNewInstanceNode(lfg, nin, method);
                seedFromContainerInstanceNode(lfg, nin, method);
            } else if (n instanceof NewArrayNode nan) {
                seedFromNewArrayNode(lfg, nan, method);
            } else if (n instanceof AllocatedObjectNode aon) {
                seedFromVirtualizedContainerInstanceNode(lfg, aon, method);
                seedFromVirtualizedNewArrayNode(lfg, aon, method);
            } else if (n instanceof LoadFieldNode lfn) {
                seedFromLoadFieldNode(lfg, lfn, method);
            } else if (n instanceof LoadIndexedNode lin) {
                seedFromLoadIndexedNode(lfg, lin, method);
            }
        }
    }

    /**
     * Seed a walk from an invoke's stringy return value (reusing a call vertex at the same bci from the parameter walk).
     */
    private void seedFromInvokeReturn(LocalFlowGraph lfg, Invoke inv, AnalysisMethod method) {
        ResolvedJavaMethod tm = inv.callTarget() != null ? inv.callTarget().targetMethod() : null;
        if (tm == null) {
            return;
        }
        if (tm.getSignature().getReturnKind() != jdk.vm.ci.meta.JavaKind.Object) {
            return;
        }
        jdk.vm.ci.meta.JavaType retType = tm.getSignature().getReturnType(null);
        if (retType == null || !isStringyReturnTypeName(retType.toJavaName(true))) {
            return;
        }
        int bci = StringAnalysisChildInlining.pointsToBci(inv);
        InvokeTypeFlow invFlow = builder.invokeFlowOf(method, inv);
        if (invFlow == null) {
            return;
        }
        LocalFlowGraph.LocalVertex invokeVertex = findInvokeVertexByBci(lfg, bci);
        if (invokeVertex == null) {
            // (no irNode here: the engine's invokesOfVertex then takes every invoke with this bci)
            invokeVertex = lfg.newVertex(LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
            invokeVertex.calleeMethod = invFlow.getTargetMethod();
            invokeVertex.bci = bci;
            invokeVertex.typeFlow = invFlow;
        }
        LocalFlowGraph.LocalVertex retVertex = invokeVertex.result;
        if (retVertex == null) {
            TypeFlow<?> ret = invFlow.getActualReturn();
            if (ret == null) {
                return;
            }
            retVertex = newResultVertex(lfg, invokeVertex, ret);
        }
        lfg.registerNodeVertex(inv.asNode(), retVertex);
        walkSSAFromParam(lfg, inv.asNode(), retVertex, method, new HashSet<>());
    }

    /**
     * Seed a walk from a String constant ({@code "literal".substring()}).
     */
    private void seedFromConstantNode(LocalFlowGraph lfg, ConstantNode cn, AnalysisMethod method) {
        JavaConstant jc = cn.asJavaConstant();
        if (jc == null || jc.getJavaKind() != jdk.vm.ci.meta.JavaKind.Object) {
            return;
        }
        String text = null;
        try {
            text = builder.bb.getSnippetReflectionProvider().asObject(String.class, jc);
        } catch (Throwable t) {
            // not a String constant
        }
        if (text == null) {
            return;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "string-constant";
        seed.irNode = cn;
        // The exact type for the dispatch actual-arg filter (constants carry no typeFlow).
        seed.declaredType = builder.resolveAnalysisTypeByName("java.lang.String");
        lfg.registerNodeVertex(cn, seed);
        walkSSAFromParam(lfg, cn, seed, method, new HashSet<>());
    }

    /**
     * Seed a walk from a stringy allocation ({@code new String(...).substring()}).
     */
    private void seedFromNewInstanceNode(LocalFlowGraph lfg, NewInstanceNode nin, AnalysisMethod method) {
        ResolvedJavaType rjt = nin.instanceClass();
        if (rjt == null) {
            return;
        }
        if (!SugNameTables.STRINGY_ALLOC_TYPES.contains(rjt.toJavaName(true))) {
            return;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "new-instance";
        seed.irNode = nin;
        // The allocation site's exact type (deterministic dispatch identity).
        seed.declaredType = builder.resolveAnalysisType(rjt);
        lfg.registerNodeVertex(nin, seed);
        walkSSAFromParam(lfg, nin, seed, method, new HashSet<>());
    }

    /**
     * Seed a walk from an array allocation whose element type can hold stringy values. The {@code "new-array"} vertex
     * is an allocation-site connector (a transfer origin); the walk connects the allocation to its field-store outputs
     * (the stamp sources, {@code this.elementData = newArray}) and its invoke/array usages. Arrays with primitive or
     * non-stringy elements cannot transport stringy values and are not seeded.
     */
    private void seedFromNewArrayNode(LocalFlowGraph lfg, NewArrayNode nan, AnalysisMethod method) {
        ResolvedJavaType elem = nan.elementType();
        if (elem == null || elem.getJavaKind() != JavaKind.Object) {
            return;
        }
        AnalysisType elemType = builder.resolveAnalysisType(elem);
        if (elemType == null || !builder.canHoldStringy(elemType)) {
            return;
        }
        LocalFlowGraph.LocalVertex seed = getOrCreateNewArrayVertex(lfg, nan, method);
        if (seed == null) {
            return;
        }
        walkSSAFromParam(lfg, nan, seed, method, new HashSet<>());
    }

    /**
     * Get-or-create the {@code "new-array"} vertex of an array allocation (registration only, no walk);
     * {@code declaredType} is the exact array type. Null when the array type cannot be resolved.
     */
    LocalFlowGraph.LocalVertex getOrCreateNewArrayVertex(LocalFlowGraph lfg, NewArrayNode nan, AnalysisMethod method) {
        LocalFlowGraph.LocalVertex existing = lfg.vertexForNode(nan);
        if (existing != null) {
            return existing;
        }
        ResolvedJavaType elem = nan.elementType();
        if (elem == null) {
            return null;
        }
        ResolvedJavaType arrayType = elem.getArrayClass();
        AnalysisType at = arrayType != null ? builder.resolveAnalysisType(arrayType) : null;
        if (at == null) {
            return null;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "new-array";
        seed.irNode = nan;
        seed.declaredType = at;
        lfg.registerNodeVertex(nan, seed);
        return seed;
    }

    /**
     * The virtualized-array seed: an {@link AllocatedObjectNode} whose virtual object is an array (e.g. a
     * {@code static String[] f = new String[2]} clinit store). The container-instance seed skips arrays, so without this
     * the allocation would never become a transfer origin and its field-store outputs (stamp sources) would be missing.
     * Same stringy-element filter as {@link #seedFromNewArrayNode}.
     */
    private void seedFromVirtualizedNewArrayNode(LocalFlowGraph lfg, AllocatedObjectNode aon, AnalysisMethod method) {
        VirtualObjectNode von = aon.getVirtualObject();
        if (von == null) {
            return;
        }
        ResolvedJavaType arrayType = von.type();
        if (arrayType == null || !arrayType.isArray()) {
            return;
        }
        ResolvedJavaType component = arrayType.getComponentType();
        if (component == null || component.getJavaKind() != JavaKind.Object) {
            return;
        }
        AnalysisType elemType = builder.resolveAnalysisType(component);
        if (elemType == null || !builder.canHoldStringy(elemType)) {
            return;
        }
        LocalFlowGraph.LocalVertex existing = lfg.vertexForNode(aon);
        if (existing != null) {
            // Already registered: a same-label re-registration guard (container seeds skip arrays).
            if ("new-array".equals(existing.label)) {
                walkSSAFromParam(lfg, aon, existing, method, new HashSet<>());
            }
            return;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "new-array";
        seed.irNode = aon;
        seed.declaredType = builder.resolveAnalysisType(arrayType);
        lfg.registerNodeVertex(aon, seed);
        walkSSAFromParam(lfg, aon, seed, method, new HashSet<>());
    }

    /**
     * Seed a walk from a non-string container or object-carrier allocation (Vector, ArrayList, a wrapper with an
     * Object field). The {@code "container-instance"} vertex is a transfer origin whose connector identity is the
     * vertex itself; the {@link NewInstanceTypeFlow} (by bci) is attached for the SUG mapping only. Stringy allocation
     * types are seeded by {@link #seedFromNewInstanceNode}.
     */
    private void seedFromContainerInstanceNode(LocalFlowGraph lfg, NewInstanceNode nin, AnalysisMethod method) {
        ResolvedJavaType rjt = nin.instanceClass();
        if (rjt == null) {
            return;
        }
        String typeName = rjt.toJavaName(true);
        if (SugNameTables.STRINGY_ALLOC_TYPES.contains(typeName)) {
            return;
        }
        AnalysisType at = builder.resolveAnalysisType(rjt);
        if (at == null || !(isContainerType(at) || isObjectCarrierType(at))) {
            return;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "container-instance";
        seed.irNode = nin;
        // The exact type (dispatch identity; also covers a failed by-bci typeFlow lookup).
        seed.declaredType = at;
        lfg.registerNodeVertex(nin, seed);
        NodeSourcePosition ninPos = nin.getNodeSourcePosition();
        if (ninPos != null) {
            NewInstanceTypeFlow newFlow = resolveNewInstanceByBci(method, ninPos.getBCI());
            if (newFlow != null) {
                seed.typeFlow = newFlow;
            }
        }
        walkSSAFromParam(lfg, nin, seed, method, new HashSet<>());
    }

    /**
     * The virtualized analogue of {@link #seedFromContainerInstanceNode}. The front-end escape analysis
     * ({@code MethodTypeFlowBuilder.optimizeGraphBeforeAnalysis} runs {@code PartialEscapePhase} before encoding)
     * turns non-escaping container allocations into {@link CommitAllocationNode} + {@link VirtualObjectNode} +
     * {@link AllocatedObjectNode}; the walk starts at the {@link AllocatedObjectNode}, the object that flows to
     * usages.
     */
    private void seedFromVirtualizedContainerInstanceNode(LocalFlowGraph lfg, AllocatedObjectNode aon, AnalysisMethod method) {
        VirtualObjectNode von = aon.getVirtualObject();
        if (von == null) {
            return;
        }
        ResolvedJavaType rjt = von.type();
        if (rjt == null) {
            return;
        }
        String typeName = rjt.toJavaName(true);
        if (SugNameTables.STRINGY_ALLOC_TYPES.contains(typeName)) {
            return;
        }
        AnalysisType at = builder.resolveAnalysisType(rjt);
        if (at == null || !(isContainerType(at) || isObjectCarrierType(at))) {
            return;
        }
        LocalFlowGraph.LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "container-instance";
        seed.irNode = aon;
        // The exact type (dispatch identity; also covers a failed by-bci typeFlow lookup).
        seed.declaredType = at;
        lfg.registerNodeVertex(aon, seed);
        NodeSourcePosition seedPos = aon.getNodeSourcePosition();
        if (seedPos == null) {
            seedPos = von.getNodeSourcePosition();
        }
        if (seedPos == null && aon.getCommit() != null) {
            seedPos = aon.getCommit().getNodeSourcePosition();
        }
        if (seedPos != null) {
            NewInstanceTypeFlow newFlow = resolveNewInstanceByBci(method, seedPos.getBCI());
            if (newFlow != null) {
                seed.typeFlow = newFlow;
            }
        }
        walkSSAFromParam(lfg, aon, seed, method, new HashSet<>());
    }

    /**
     * An object-carrier type: a class with at least one reference-kind instance field, whether or not it can hold
     * stringy values. A stringy-only gate ({@link #isContainerType}) would leave hand-rolled containers like
     * {@code MyIter} (whose {@code outer} field's type {@code MyList} holds no stringy value) without an allocation
     * seed walk (no usage edges, no RETURN_EXIT, no ctor-receiver edge), so the exploration could not cross the
     * ctor-this anchor. Only the graph is enriched; atoms stay demand-driven.
     */
    private boolean isObjectCarrierType(AnalysisType t) {
        if (t == null || t.isArray() || t.isInterface()) {
            return false;
        }
        return carrierFieldInSuperclassChain(t);
    }

    /**
     * The carrier gate walks the full superclass chain: a class whose reference fields are all inherited
     * ({@code class MyIter extends Base { }} with {@code Base { MyList outer; }}) is as much a carrier; a declared-only
     * test would leave it without a seed walk (missed usages, the false-admit direction).
     */
    static boolean carrierFieldInSuperclassChain(jdk.vm.ci.meta.ResolvedJavaType t) {
        for (jdk.vm.ci.meta.ResolvedJavaType c = t; c != null; c = c.getSuperclass()) {
            ResolvedJavaField[] fields = c.getInstanceFields(false);
            if (fields == null) {
                continue;
            }
            for (ResolvedJavaField f : fields) {
                jdk.vm.ci.meta.JavaType ft = f.getType();
                if (ft instanceof jdk.vm.ci.meta.ResolvedJavaType resolved && resolved.getJavaKind() == JavaKind.Object) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Whether the type declares (superclasses excluded) an instance field that can hold stringy values; an array field
     * is checked by its component type ({@code canHoldStringy} is false for array types). Covers the standard
     * containers ({@code Object[]} fields) and wrappers with Object-typed fields.
     */
    private boolean isContainerType(AnalysisType t) {
        if (t == null || t.isArray() || t.isInterface()) {
            return false;
        }
        ResolvedJavaField[] fields = t.getInstanceFields(false);
        if (fields == null) {
            return false;
        }
        for (ResolvedJavaField f : fields) {
            jdk.vm.ci.meta.JavaType ft = f.getType();
            if (ft instanceof ResolvedJavaType resolved) {
                AnalysisType aft = builder.resolveAnalysisType(resolved);
                if (aft == null) {
                    continue;
                }
                if (aft.isArray()) {
                    AnalysisType component = aft.getComponentType();
                    if (component != null && component.getJavaKind() == JavaKind.Object && builder.canHoldStringy(component)) {
                        return true;
                    }
                } else if (builder.canHoldStringy(aft)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The field load-seed filter: the type can hold stringy, or is an array whose component can ({@code String[]},
     * {@code Object[]}); otherwise array-typed field loads would not be seeded and the hub pool would miss the reading
     * frame's cross-frame load.
     */
    private boolean canHoldStringyOrStringyElements(AnalysisType declaredType) {
        if (declaredType.isArray()) {
            AnalysisType component = declaredType.getComponentType();
            return component != null && component.getJavaKind() == JavaKind.Object &&
                            builder.canHoldStringy(component);
        }
        return builder.canHoldStringy(declaredType);
    }

    /**
     * Seed a walk from a stringy field load ({@code this.field.substring()}), reusing the parameter walk's LOAD vertex;
     * the by-bci type flow lets the SUG vertex map to it.
     */
    private void seedFromLoadFieldNode(LocalFlowGraph lfg, LoadFieldNode lfn, AnalysisMethod method) {
        jdk.vm.ci.meta.JavaType fieldType = lfn.field() != null ? lfn.field().getType() : null;
        AnalysisType declaredType = fieldType != null && fieldType instanceof ResolvedJavaType resolved
                        ? builder.resolveAnalysisType(resolved)
                        : null;
        if (declaredType == null || !canHoldStringyOrStringyElements(declaredType)) {
            return;
        }
        AnalysisField af = resolveAnalysisField(lfn.field());
        LocalFlowGraph.LocalVertex loadVertex = findLoadVertexByNode(lfg, lfn);
        if (loadVertex == null) {
            loadVertex = lfg.newVertex(LocalFlowGraph.VertexKind.LOAD);
            loadVertex.label = "load:" + lfn.field().getName();
            loadVertex.field = af;
            loadVertex.irNode = lfn;
            NodeSourcePosition lfnPos = lfn.getNodeSourcePosition();
            if (lfnPos != null) {
                LoadFieldTypeFlow.LoadInstanceFieldTypeFlow loadFlow = resolveLoadFieldByBci(method, lfnPos.getBCI());
                if (loadFlow != null) {
                    loadVertex.typeFlow = loadFlow;
                }
            }
        }
        lfg.registerNodeVertex(lfn, loadVertex);
        walkSSAFromParam(lfg, lfn, loadVertex, method, new HashSet<>());
    }

    private void seedFromLoadIndexedNode(LocalFlowGraph lfg, LoadIndexedNode lin, AnalysisMethod method) {
        AnalysisType elementType = resolveArrayElementType(lin, method);
        OffsetLoadTypeFlow.LoadIndexedTypeFlow flow = null;
        NodeSourcePosition position = lin.getNodeSourcePosition();
        if (position != null) {
            flow = resolveLoadIndexedByBci(method, position.getBCI());
            if (elementType == null && flow != null) {
                elementType = flow.getDeclaredType();
            }
        }
        if (elementType != null && !builder.canHoldStringy(elementType)) {
            return;
        }
        if (elementType == null && lin.elementKind() != jdk.vm.ci.meta.JavaKind.Object) {
            return;
        }
        LocalFlowGraph.LocalVertex loadVertex = findLoadVertexByNode(lfg, lin);
        if (loadVertex == null) {
            loadVertex = lfg.newVertex(LocalFlowGraph.VertexKind.ARRAY_LOAD);
            loadVertex.label = "loadIndexed";
            loadVertex.arrayType = elementType;
            loadVertex.irNode = lin;
            loadVertex.typeFlow = flow;
        }
        lfg.registerNodeVertex(lin, loadVertex);
        walkSSAFromParam(lfg, lin, loadVertex, method, new HashSet<>());
    }

    private LocalFlowGraph.LocalVertex findInvokeVertexByBci(LocalFlowGraph lfg, int bci) {
        for (LocalFlowGraph.LocalVertex v : lfg.getInvokeVertices()) {
            if (v.bci == bci) {
                return v;
            }
        }
        return null;
    }

    private static LocalFlowGraph.LocalVertex findLoadVertexByNode(LocalFlowGraph lfg, Node node) {
        // Under the frame's monitor: a concurrent lazy mint must not resize the list during the scan.
        synchronized (lfg.vertexLock()) {
            for (LocalFlowGraph.LocalVertex v : lfg.getVertices()) {
                if (v.irNode == node) {
                    return v;
                }
            }
        }
        return null;
    }

    /**
     * Create the Phase-A SUG usage site of every node-shaped strict class check (GetClassNode, canonicalized exact
     * instanceof) and raw String-field read, on the same graph, one per (method, bci[, field]). Invoke-shaped class
     * checks get their sites from the invoke classification; STRING atoms create their own detached sites.
     */
    private void wireClassCheckSites(LocalFlowGraph lfg, StructuredGraph ir, AnalysisMethod method) {
        if (ir == null || ir.start() == null) {
            return;
        }
        for (LocalFlowGraph.LocalVertex vertex : lfg.getVertices()) {
            if (vertex.kind == LocalFlowGraph.VertexKind.CLASS_CHECK && vertex.armAnchor instanceof ValueNode positionNode) {
                if (vertex.rawStringField != null) {
                    builder.getOrCreateRawStringFieldReadSite(method, vertex.bci, vertex.rawStringField, positionNode);
                } else {
                    builder.getOrCreateClassCheckSite(method, vertex.bci, vertex.label, positionNode);
                }
            }
        }
    }

    /**
     * The pure guard lists of one usage anchor (used by the arm skip, {@code ForwardFixpoint}). Vacuous: a non-exact
     * guard whose dead arm hosts all anchors (always-succeeds coverage; exact guards are excluded because an
     * assignable member can still fail an exact test). Never: any guard, exact included, whose covered arm hosts all
     * anchors (always-fails coverage; for an exact guard sound a fortiori: exact-pass implies target-assignability, so
     * a key with no target-assignable member passes it for no member and no rep). Pure reachability, deterministic.
     */
    static void guardListsFor(Node start, java.util.List<Node> anchors, List<LocalFlowGraph.TypeGuard> guards,
                    java.util.List<LocalFlowGraph.TypeGuard> vacuous, java.util.List<LocalFlowGraph.TypeGuard> never) {
        for (LocalFlowGraph.TypeGuard guard : guards) {
            if (!guard.exact && LocalFlowGraph.anchorsUnreachableBehind(start, anchors, guard.deadArm())) {
                vacuous.add(guard);
            }
            if (LocalFlowGraph.anchorsUnreachableBehind(start, anchors, guard.coveredArm())) {
                never.add(guard);
            }
        }
    }

    /** Whether {@code t} is java.lang.String or a subtype of it (the reps). */
    static boolean isStringOrSubtype(AnalysisType t) {
        AnalysisType cur = t;
        while (cur != null) {
            if ("java.lang.String".equals(cur.toJavaName(true))) {
                return true;
            }
            cur = cur.getSuperclass();
        }
        return false;
    }

    /**
     * The source-shape adjudication: an exact instanceof fold from source {@code instanceof} or {@code checkcast} is
     * allowed; one from {@code getClass()} is rejected. One-way (every corner stays strict): an exact fold is not a
     * rejecting usage iff both hold:
     * <ol>
     * <li><b>Source-opcode provenance:</b> the node's source position resolves to this method's code at an
     * {@code instanceof} (193) or {@code checkcast} (192). Parse-time folds of {@code instanceof T} (leaf /
     * unique-concrete-subtype) carry exactly this position; getClass-compare folds ({@code x.getClass() == T.class},
     * canonicalized by ObjectEqualsNode) carry the compare's position (165/166), and generated accessors carry
     * synthetic bcis, so both stay strict. The opcode is what separates the cast/instanceof family from
     * getClass-compare folds.</li>
     * <li><b>The target gate, instanceof arm only:</b> for 193 the tested type must be neither String nor a rep. An
     * exact test diverges between a String and a rep exactly when the tested type is in the cone (T == String: String
     * passes, every rep fails, the leak shape; T == a rep: the symmetric corner); those stay strict. For every
     * out-of-cone T, String and every rep both fail, so the test observes nothing the substitution can change.
     * <p>
     * <b>The cast arm (192) has no cone gate:</b> user code is compiled against the unmodified JDK, where String is
     * final and no rep class exists; reps ({@code extends String}) are injected only at image-build time. So at every
     * source-level cast: (a) a cast to String is a no-op for String and every rep (a rep is a String); (b) a cast to
     * an out-of-cone type throws CCE identically for String and every rep (reps live inside the String cone), or is a
     * no-op for both. A source-level cast cannot diverge; the only strict class check is a source-level
     * {@code getClass()}, which the opcode anchor excludes.</li>
     * </ol>
     * Deterministic: a pure function of the node's position, the bytecode and closed-world types.
     */
    static boolean instanceofSourceFoldAllowed(InstanceOfNode ion, jdk.vm.ci.meta.ResolvedJavaMethod method,
                    java.util.function.Function<jdk.vm.ci.meta.ResolvedJavaType, AnalysisType> resolve) {
        if (method == null) {
            return false;
        }
        NodeSourcePosition pos = ion.getNodeSourcePosition();
        if (pos == null || pos.getBCI() < 0 || pos.getMethod() != method) {
            return false;
        }
        byte[] code = method.getCode();
        if (code == null || pos.getBCI() >= code.length) {
            return false;
        }
        int opcode = code[pos.getBCI()] & 0xFF;
        boolean instanceOfSource = opcode == Bytecodes.INSTANCEOF;
        // checkcast is allowed unconditionally (no cone gate, see the javadoc); instanceof keeps the cone gate below.
        boolean checkCastSource = opcode == Bytecodes.CHECKCAST;
        if (!instanceOfSource && !checkCastSource) {
            return false;
        }
        TypeReference typeRef = ion.type();
        if (typeRef == null || typeRef.getType() == null) {
            return false;
        }
        if (checkCastSource) {
            return true;
        }
        AnalysisType target = resolve.apply(typeRef.getType());
        return target != null && !isStringOrSubtype(target);
    }

    /**
     * The scan-record collector: one pass over {@code ir.getNodes()} recording the node, its source-location key and
     * the attributes SUG vertex creation needs, plus the {@code ParameterNode} stamp types (the param-type fallback).
     */
    private void collectSugScanRecords(LocalFlowGraph lfg, StructuredGraph ir, AnalysisMethod method) {
        for (Node n : ir.getNodes()) {
            if (n instanceof NewInstanceNode nin) {
                ResolvedJavaType rjt = nin.instanceClass();
                String typeName = rjt != null ? rjt.toJavaName(true) : null;
                if (typeName == null || !SugNameTables.STRINGY_ALLOC_TYPES.contains(typeName)) {
                    continue;
                }
                NodeSourcePosition pos = nin.getNodeSourcePosition();
                lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                LocalFlowGraph.SugScanRecord.NEW_INSTANCE, nin,
                                pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : SiteKeys.UNKNOWN_KEY,
                                pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : null,
                                typeName, builder.resolveAnalysisType(rjt), null, 0L, -1));
            } else if (!(n instanceof NewInstanceNode) && StringAtoms.allocatedType(n) != null &&
                            StringAtoms.ACC_SEED_TYPES.contains(StringAtoms.allocatedType(n).toJavaName(true)) && method.getDeclaringClass() != null &&
                            StringAnalysisPolicy.isUserCodeClass(method.getDeclaringClass().toJavaName(true))) {
                // The child's IR allocates a builder as a materialised virtual object or with an exception edge, never
                // as a NewInstanceNode: record the user-code builder allocations (the accumulator seeds) here.
                NodeSourcePosition pos = StringAtoms.allocationPosition(n);
                jdk.vm.ci.meta.ResolvedJavaType at = StringAtoms.allocatedType(n);
                lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                LocalFlowGraph.SugScanRecord.NEW_INSTANCE, n,
                                pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : SiteKeys.UNKNOWN_KEY,
                                pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : null,
                                at.toJavaName(true), builder.resolveAnalysisType(at), null, 0L, -1));
            } else if (n instanceof ConstantNode cn) {
                JavaConstant jc = cn.asJavaConstant();
                if (jc == null) {
                    continue;
                }
                if (jc.getJavaKind() == JavaKind.Object) {
                    String text = null;
                    try {
                        text = builder.bb.getSnippetReflectionProvider().asObject(String.class, jc);
                    } catch (Throwable t) {
                        // not a String constant
                    }
                    if (text == null) {
                        continue;
                    }
                    NodeSourcePosition pos = cn.getNodeSourcePosition();
                    String key = pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : null;
                    lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                    LocalFlowGraph.SugScanRecord.CONST_STRING, cn,
                                    key != null ? key : SiteKeys.UNKNOWN_KEY, key,
                                    null, null, text, 0L, -1));
                } else if (jc.getJavaKind().isPrimitive()) {
                    long val;
                    switch (jc.getJavaKind()) {
                        case Boolean -> val = jc.asInt() != 0 ? 1 : 0;
                        case Byte, Short, Char -> val = jc.asInt();
                        case Int -> val = jc.asInt();
                        case Long -> val = jc.asLong();
                        default -> {
                            continue;
                        }
                    }
                    NodeSourcePosition pos = cn.getNodeSourcePosition();
                    String key = pos != null ? SiteKeys.profileKey(method, pos.getBCI()) : null;
                    lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                    LocalFlowGraph.SugScanRecord.CONST_PRIMITIVE, cn,
                                    key != null ? key : SiteKeys.UNKNOWN_KEY, key,
                                    null, null, null, val, -1));
                }
            } else if (n instanceof Invoke inv) {
                lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                LocalFlowGraph.SugScanRecord.INVOKE, inv.asNode(),
                                null, null, null, null, null, 0L, StringAnalysisChildInlining.pointsToBci(inv)));
            } else if (n instanceof LoadFieldNode lfn) {
                lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                LocalFlowGraph.SugScanRecord.LOAD_FIELD, lfn,
                                null, null, null, null, null, 0L, -1));
            } else if (n instanceof LoadIndexedNode lin) {
                lfg.sugScanRecords.add(new LocalFlowGraph.SugScanRecord(
                                LocalFlowGraph.SugScanRecord.LOAD_INDEXED, lin,
                                null, null, null, null, null, 0L, -1));
            }
        }
        // The ParameterNode stamp types (the param-type fallback).
        int maxParam = -1;
        for (Node n : ir.getNodes()) {
            if (n instanceof ParameterNode pn && pn.index() > maxParam) {
                maxParam = pn.index();
            }
        }
        if (maxParam >= 0) {
            AnalysisType[] stamps = new AnalysisType[maxParam + 1];
            for (Node n : ir.getNodes()) {
                if (n instanceof ParameterNode pn) {
                    Stamp stamp = pn.stamp(NodeView.DEFAULT);
                    if (stamp instanceof ObjectStamp os && os.type() != null && stamps[pn.index()] == null) {
                        stamps[pn.index()] = builder.resolveAnalysisType(os.type());
                    }
                }
            }
            lfg.paramStampTypes = stamps;
        }
    }

    /**
     * Collect the method's rep-transparent type guards: every IfNode whose condition is {@code instanceof T} or its
     * negation (the covered arm is then the false arm). A guard needs a resolvable tested value and arm successors
     * (else no guard: the conservative keep). The tested value is recorded after Pi/proxy skipping, so a guard is only
     * used for the same value (a guard on a different SSA alias would be unsound to use).
     * <p>
     * Exact instanceofs (the canonicalized {@code x.getClass() == T.class} fold, the leaf-type fold of
     * {@code instanceof FinalT}) are collected too, marked {@link LocalFlowGraph.TypeGuard#exact}: in the never
     * direction an exact guard is sound a fortiori (e.g. in {@code Field.binaryValue} the dominating
     * {@code instanceof BytesRef} folds exact). {@link #guardListsFor} keeps them out of the vacuous list: an
     * assignable member can still fail an exact test.
     */
    private void collectTypeGuards(LocalFlowGraph lfg, StructuredGraph ir, AnalysisMethod method) {
        collectGuardsInto(lfg, ir, builder::resolveAnalysisType);
    }

    /** The testable pure core of {@link #collectTypeGuards} (the resolver parameterized). */
    static void collectGuardsInto(LocalFlowGraph lfg, StructuredGraph ir,
                    java.util.function.Function<jdk.vm.ci.meta.ResolvedJavaType, AnalysisType> resolve) {
        for (Node n : ir.getNodes()) {
            if (!(n instanceof IfNode ifNode)) {
                continue;
            }
            ValueNode condition = ifNode.condition();
            boolean negated = false;
            // !(x instanceof T): the covered arm flips to falseSuccessor.
            if (condition != null && condition.getClass().getSimpleName().equals("NotNode") &&
                            condition instanceof jdk.graal.compiler.nodes.calc.UnaryNode un) {
                ValueNode operand = un.getValue();
                if (operand instanceof InstanceOfNode) {
                    condition = operand;
                    negated = true;
                } else {
                    continue;
                }
            }
            if (!(condition instanceof InstanceOfNode ion)) {
                continue;
            }
            TypeReference typeRef = ion.type();
            if (typeRef == null || typeRef.getType() == null) {
                continue;
            }
            AnalysisType targetType = resolve.apply(typeRef.getType());
            if (targetType == null) {
                continue;
            }
            ValueNode tested = ion.getValue();
            if (tested == null) {
                continue;
            }
            ValueNode skipped = skipPisAndProxies(tested);
            if (skipped == null) {
                continue;
            }
            Node coveredArm = negated ? ifNode.falseSuccessor() : ifNode.trueSuccessor();
            Node otherArm = negated ? ifNode.trueSuccessor() : ifNode.falseSuccessor();
            if (coveredArm == null || otherArm == null) {
                continue;
            }
            lfg.addTypeGuard(new LocalFlowGraph.TypeGuard(ion.asNode(), skipped, targetType,
                            typeRef.isExact(), negated,
                            ifNode.trueSuccessor(), ifNode.falseSuccessor()));
        }
    }

    /** Skip PiNode/ValueProxy chains to the underlying value (identity-preserving). */
    private static ValueNode skipPisAndProxies(ValueNode node) {
        ValueNode n = node;
        while (n != null) {
            if (n instanceof PiNode pi) {
                n = pi.getOriginalNode();
            } else if (n instanceof jdk.graal.compiler.nodes.spi.ValueProxy proxy) {
                n = proxy.getOriginalNode();
            } else {
                break;
            }
        }
        return n;
    }

    /**
     * Whether a type name is stringy in the broad sense (allocation type, representation type or CharSequence).
     */
    private boolean isStringyReturnTypeName(String typeName) {
        return SugNameTables.STRINGY_ALLOC_TYPES.contains(typeName) ||
                        SugNameTables.STRINGY_REP_TYPES.contains(typeName) ||
                        "java.lang.CharSequence".equals(typeName);
    }

    private static <T> T resolveByBci(Map<AnalysisMethod, Map<Integer, T>> index, AnalysisMethod method, int bci) {
        Map<Integer, T> bciMap = index.get(method);
        return bciMap != null ? bciMap.get(bci) : null;
    }

    private LoadFieldTypeFlow.LoadInstanceFieldTypeFlow resolveLoadFieldByBci(AnalysisMethod method, int bci) {
        return resolveByBci(builder.methodBciToLoadField, method, bci);
    }

    private OffsetLoadTypeFlow.LoadIndexedTypeFlow resolveLoadIndexedByBci(AnalysisMethod method, int bci) {
        return resolveByBci(builder.methodBciToLoadIndexed, method, bci);
    }

    private NewInstanceTypeFlow resolveNewInstanceByBci(AnalysisMethod method, int bci) {
        return resolveByBci(builder.methodBciToNewInstance, method, bci);
    }

    /**
     * The {@link AnalysisField} of a decoded graph's field (which may already be one; the universe's map is keyed by the
     * unwrapped field).
     */
    AnalysisField resolveAnalysisField(ResolvedJavaField rjf) {
        if (rjf instanceof AnalysisField af) {
            return af;
        }
        return builder.bb.getUniverse().getField(rjf);
    }

    /**
     * The array element type from the array input's stamp, or {@code null} (the caller falls back to the type flow's
     * declared type).
     */
    private AnalysisType resolveArrayElementType(AccessIndexedNode node, AnalysisMethod method) {
        ValueNode arrayNode = node.array();
        if (arrayNode == null) {
            return null;
        }
        Stamp stamp = arrayNode.stamp(NodeView.DEFAULT);
        if (!(stamp instanceof ObjectStamp os)) {
            return null;
        }
        ResolvedJavaType arrayType = os.type();
        if (arrayType == null || !arrayType.isArray()) {
            return null;
        }
        ResolvedJavaType componentType = arrayType.getComponentType();
        if (componentType == null) {
            return null;
        }
        if (componentType instanceof AnalysisType at) {
            return at;
        }
        return builder.bb.getUniverse().lookup(componentType);
    }

}
