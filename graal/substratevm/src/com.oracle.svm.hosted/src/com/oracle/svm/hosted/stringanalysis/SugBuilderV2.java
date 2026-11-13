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
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import jdk.graal.compiler.nodes.EncodedGraph;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.OptimisticOptimizations;
import jdk.graal.compiler.nodes.EncodedGraph.EncodedNodeReference;

import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.flow.ActualReturnTypeFlow;
import com.oracle.graal.pointsto.flow.AnalysisParsedGraph;
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

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.NewInstanceNode;
import jdk.graal.compiler.printer.GraalDebugHandlersFactory;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * SUG builder: builds the String Utilization Graph from the IR and the points-to type-flow graph.
 * <ul>
 * <li>Phase A: the per-method {@link LocalFlowGraph}s (IR walk; undecodable IR aborts the whole analysis) and the SUG
 * vertices: stringy flows, parameters, returns, constants, allocations, and the concat/accumulator sites from the
 * capture hook.</li>
 * <li>Phase B: {@code buildInvokeQualifierParameterEdges} creates the structural edges (QUALIFIER/PARAMETER/DATAFLOW)
 * from type flows; then {@code ForwardFixpoint} writes {@code usageTags}/{@code sourceTags}/{@code incompleteTrace}
 * into the SUG, the sole source of truth.</li>
 * <li>Phase C: cleanup: merge pass-through (assignment/copy) vertices and prune container vertices that reach no usage
 * vertex.</li>
 * </ul>
 * The per-object scoping reads {@code getState().objects(bb)}, so it works with either {@code AnalysisObject}
 * granularity ({@code -H:+AllocationSiteSensitiveHeap} or not).
 */
public final class SugBuilderV2 {

    final BigBang bb;
    final PointsToAnalysis pta;
    final StringUtilizationGraph sug = new StringUtilizationGraph();

    private final Set<SugVertex> usageVertices = new LinkedHashSet<>();
    private final Set<SugVertex> nonUsageVertices = ConcurrentHashMap.newKeySet();

    final Object parallelLock = new Object();

    private Map<AnalysisMethod, Map<String, List<SugVertex>>> verticesByEnclosingAndSource = Collections.emptyMap();
    Map<AnalysisMethod, Map<Integer, InvokeTypeFlow>> methodBciToInvoke = Collections.emptyMap();
    /**
     * The keys of {@link #methodBciToInvoke} holding more than one invoke flow (invokes left by an inlined scope share
     * their root call's bci).
     */
    Map<AnalysisMethod, Set<Integer>> methodBciInvokeAmbiguous = Collections.emptyMap();
    Map<AnalysisMethod, Map<Integer, LoadFieldTypeFlow.LoadInstanceFieldTypeFlow>> methodBciToLoadField = Collections.emptyMap();
    Map<AnalysisMethod, Map<Integer, OffsetLoadTypeFlow.LoadIndexedTypeFlow>> methodBciToLoadIndexed = Collections.emptyMap();
    Map<AnalysisMethod, Map<Integer, NewInstanceTypeFlow>> methodBciToNewInstance = Collections.emptyMap();
    /** Per enclosing method, the bcis of the captured {@link ConcatMethodSite}s ({@link #hasConcatMethodSite}). */
    Map<AnalysisMethod, Set<Integer>> concatMethodSiteBcis = Collections.emptyMap();
    /** Bounded LRU cache of decoded IR graphs (access-ordered, {@link #IR_CACHE_MAX_ENTRIES} entries, synchronized). */
    private static final int IR_CACHE_MAX_ENTRIES = 4096;
    final Map<AnalysisMethod, StructuredGraph> irGraphCache = Collections.synchronizedMap(
                    new LinkedHashMap<AnalysisMethod, StructuredGraph>(256, 0.75f, true) {
                        @Override
                        protected boolean removeEldestEntry(Map.Entry<AnalysisMethod, StructuredGraph> eldest) {
                            return size() > IR_CACHE_MAX_ENTRIES;
                        }
                    });
    Map<AnalysisMethod, LocalFlowGraph> localFlowGraphs = Collections.emptyMap();

    /** The walk-window decode sequence, in access order: the input of {@link #simulateLegacyA2Regime()}. */
    final List<AnalysisMethod> walkDecodeSeq = new ArrayList<>();
    /** 0 = the LFG-walk window (sequence logged); 1 = after. */
    int decodePhase;
    /** The arg-position receiver-stamp resolution, collected in the same IR pass as the LFGs. */
    final ArgStampResolution argStampResolution = new ArgStampResolution(this);
    /**
     * Copy-anchor diagnostics (always-on counters). Site counters fire at the first resolution of a distinct (LFG,
     * node), so they count resolved copy shapes, not raw scans; inheritance counters mark endpoints whose root
     * resolution used an inheritance.
     */
    long diagCopyOfSites;
    long diagCloneInvokeSites;
    long diagCloneNodeSites;
    long diagArraycopyInvokeSites;
    long diagArraycopyNodeSites;
    long diagWrapperReturnsCrossed;
    long diagWrapperMethodsResolved;
    long diagCopyInheritComplete;
    long diagCopyInheritTaint;
    long diagInterprocDepthTaint;
    long diagInterprocCycleTaint;
    long diagCalleeAllocTaint;
    long diagSyntheticFieldConnectors;
    long diagEndpointsUsingInheritanceStores;
    long diagEndpointsUsingInheritanceLoads;
    DebugContext irDebugContext;
    private Map<String, List<SugVertex>> verticesBySourceKeyForAccumulator = Collections.emptyMap();
    private Map<AnalysisMethod, Map<String, List<SugVertex>>> verticesByEnclosingAndSourceForAccumulator = Collections.emptyMap();

    /** The LFG construction (holds this builder as its substrate). */
    final LfgWalk lfgWalk = new LfgWalk(this);

    public SugBuilderV2(BigBang bb) {
        this.bb = bb;
        this.pta = (bb instanceof PointsToAnalysis p) ? p : null;
    }

    public StringUtilizationGraph build(AnalysisUniverse universe, Map<AnalysisMethod, List<CapturedSite>> captured) {
        LfgWalk.initStringyRawMemTypes(this); // the stringy-type set (isAssignableFrom test)
        buildLoadIndex(universe);
        System.out.println("[sug-perf] Phase A (SUG-from-IR) start");
        long phaseAStart = System.currentTimeMillis();
        phaseABuildSugFromIr(universe, captured);
        long phaseAEnd = System.currentTimeMillis();
        System.out.println("[sug-perf] Phase A (SUG-from-IR) done: " + (phaseAEnd - phaseAStart) + "ms, " + sug.getVertices().size() + " vertices");
        phaseBDownstreamSearch(universe);
        long phaseBEnd = System.currentTimeMillis();
        System.out.println("[sug-perf] Phase B done: " + (phaseBEnd - phaseAEnd) + "ms");
        System.out.println("[sug-perf] Phase C start");
        long phaseCStart = System.currentTimeMillis();
        phaseCCleanup();
        long phaseCEnd = System.currentTimeMillis();
        System.out.println("[sug-perf] Phase C done: " + (phaseCEnd - phaseCStart) + "ms");
        sug.clearReachabilityCache();
        return sug;
    }

    /** Builds the bci indices of the LFG walk: invokes, instance-field loads, indexed loads and new-instances. */
    private void buildLoadIndex(AnalysisUniverse universe) {
        long start = System.currentTimeMillis();
        if (pta == null) {
            System.out.println("[sug-perf] buildLoadIndex done: " + (System.currentTimeMillis() - start) + "ms");
            return;
        }
        Map<AnalysisMethod, Map<Integer, InvokeTypeFlow>> bciIndex = new LinkedHashMap<>();
        Map<AnalysisMethod, Set<Integer>> ambiguous = new LinkedHashMap<>();
        Map<AnalysisMethod, Map<Integer, LoadFieldTypeFlow.LoadInstanceFieldTypeFlow>> loadBciIndex = new LinkedHashMap<>();
        Map<AnalysisMethod, Map<Integer, OffsetLoadTypeFlow.LoadIndexedTypeFlow>> loadIndexedBciIndex = new LinkedHashMap<>();
        Map<AnalysisMethod, Map<Integer, NewInstanceTypeFlow>> newInstanceBciIndex = new LinkedHashMap<>();
        for (AnalysisMethod am : universe.getMethods()) {
            if (!am.isReachable() || !(am instanceof PointsToAnalysisMethod ptm)) {
                continue;
            }
            MethodTypeFlow mtf = ptm.getTypeFlow();
            if (mtf == null || !mtf.flowsGraphCreated()) {
                continue;
            }
            MethodFlowsGraph graph = mtf.getMethodFlowsGraph();
            if (graph.isStub()) {
                continue;
            }
            for (TypeFlow<?> flow : graph.getLinearizedGraph()) {
                if (flow instanceof LoadFieldTypeFlow.LoadInstanceFieldTypeFlow load) {
                    Object loadSrc = load.getSource();
                    if (loadSrc instanceof BytecodePosition loadPos) {
                        loadBciIndex.computeIfAbsent(am, k -> new LinkedHashMap<>()).putIfAbsent(loadPos.getBCI(), load);
                    }
                }
                if (flow instanceof OffsetLoadTypeFlow.LoadIndexedTypeFlow load) {
                    Object loadSrc = load.getSource();
                    if (loadSrc instanceof BytecodePosition loadPos) {
                        loadIndexedBciIndex.computeIfAbsent(am, k -> new LinkedHashMap<>()).putIfAbsent(loadPos.getBCI(), load);
                    }
                }
                if (flow instanceof NewInstanceTypeFlow nif) {
                    Object nifSrc = nif.getSource();
                    if (nifSrc instanceof BytecodePosition nifPos) {
                        newInstanceBciIndex.computeIfAbsent(am, k -> new LinkedHashMap<>()).putIfAbsent(nifPos.getBCI(), nif);
                    }
                }
            }
            for (InvokeTypeFlow inv : graph.getInvokes()) {
                Object src = inv.getSource();
                if (src instanceof BytecodePosition pos) {
                    InvokeTypeFlow first = bciIndex.computeIfAbsent(am, k -> new LinkedHashMap<>()).putIfAbsent(pos.getBCI(), inv);
                    if (first != null && first != inv) {
                        ambiguous.computeIfAbsent(am, k -> new HashSet<>()).add(pos.getBCI());
                    }
                }
            }
        }
        this.methodBciToInvoke = bciIndex;
        this.methodBciInvokeAmbiguous = ambiguous;
        this.methodBciToLoadField = loadBciIndex;
        this.methodBciToLoadIndexed = loadIndexedBciIndex;
        this.methodBciToNewInstance = newInstanceBciIndex;
        System.out.println("[sug-perf] buildLoadIndex done: " + (System.currentTimeMillis() - start) + "ms");
    }

    /** The invoke flow of an IR invoke of {@code method}: {@link #invokeFlowAt} over the bci index. */
    InvokeTypeFlow invokeFlowOf(AnalysisMethod method, Invoke inv) {
        return invokeFlowAt(methodBciToInvoke.get(method), methodBciInvokeAmbiguous.get(method), inv, InvokeTypeFlow::getTargetMethod);
    }

    /**
     * The call-site identity of an IR invoke: its flow is the one the points-to analysis keyed at the invoke's
     * points-to bci ({@link StringAnalysisChildInlining#pointsToBci}). An invoke left by an inlined scope is keyed by its
     * root call's bci, which it may share with other invokes of that scope; its flow is accepted only when that key holds
     * one flow and the flow's target is the invoke's own target, otherwise it has none (no LFG vertex). Every other
     * invoke is looked up by its own bci.
     */
    static <F> F invokeFlowAt(Map<Integer, F> byBci, Set<Integer> ambiguous, Invoke inv, Function<F, ?> targetOf) {
        if (byBci == null) {
            return null;
        }
        int bci = StringAnalysisChildInlining.pointsToBci(inv);
        F flow = byBci.get(bci);
        if (flow == null || !StringAnalysisChildInlining.isFromInlinedScope(inv)) {
            return flow;
        }
        if (ambiguous != null && ambiguous.contains(bci)) {
            return null;
        }
        Object target = inv.callTarget() != null ? inv.callTarget().targetMethod() : null;
        return target != null && target.equals(targetOf.apply(flow)) ? flow : null;
    }

    /**
     * Phase A: (1) the concat-method-site bci index from the capture hook; (2) the per-method {@link LocalFlowGraph}s
     * (their parameter/return/load vertices and scan records drive the vertex creation); (3) SUG vertices from the scan
     * records ({@link NewInstanceNode}, {@link ConstantNode}, {@link Invoke}, {@link ParameterNode}, {@link ReturnNode}),
     * registered with their type flows; (4) the vertex source index, the concat and accumulator-op vertices, and the
     * usage-vertex classification. The structural edges come in Phase B.
     */
    private void phaseABuildSugFromIr(AnalysisUniverse universe, Map<AnalysisMethod, List<CapturedSite>> captured) {
        concatMethodSiteBcis = buildConcatMethodSiteBciIndex(captured);

        // LFGs first: vertex creation reads their parameter/return/load vertices and scan records.
        long lfgStart = System.currentTimeMillis();
        decodePhase = 0;
        localFlowGraphs = lfgWalk.buildLocalFlowGraphs(universe);
        decodePhase = 1;
        System.out.println("[sug-perf] Phase A sub: localFlows=" + (System.currentTimeMillis() - lfgStart) + "ms, " + localFlowGraphs.size() + " methods");
        System.out.println("[sug-copy-anchor] copyOfSites=" + diagCopyOfSites +
                        ", cloneInvokeSites=" + diagCloneInvokeSites +
                        ", cloneNodeSites=" + diagCloneNodeSites +
                        ", arraycopyInvokeSites=" + diagArraycopyInvokeSites +
                        ", arraycopyNodeSites=" + diagArraycopyNodeSites +
                        ", wrapperReturnsCrossed=" + diagWrapperReturnsCrossed +
                        ", wrapperMethodsResolved=" + diagWrapperMethodsResolved +
                        ", copyInheritComplete=" + diagCopyInheritComplete +
                        ", copyInheritTaint=" + diagCopyInheritTaint +
                        ", interprocDepthTaint=" + diagInterprocDepthTaint +
                        ", interprocCycleTaint=" + diagInterprocCycleTaint +
                        ", calleeAllocTaint=" + diagCalleeAllocTaint +
                        ", syntheticFieldConnectors=" + diagSyntheticFieldConnectors +
                        ", inheritanceStores=" + diagEndpointsUsingInheritanceStores +
                        ", inheritanceLoads=" + diagEndpointsUsingInheritanceLoads);

        // Vertices come from the walk-phase scan records (LfgWalk.collectSugScanRecords), not a second decode. The
        // load vertices are created only where a two-pass build would have found the method's graph in the decoded-IR
        // cache (simulateLegacyA2Regime), which keeps the vertex population of that regime.
        long vertexStart = System.currentTimeMillis();
        Set<AnalysisMethod> legacyRegimeHits = simulateLegacyA2Regime();
        for (Map.Entry<AnalysisMethod, LocalFlowGraph> entry : localFlowGraphs.entrySet()) {
            AnalysisMethod method = entry.getKey();
            LocalFlowGraph lfg = entry.getValue();
            createSugVerticesFromRecords(method, lfg, legacyRegimeHits.contains(method));
        }
        walkDecodeSeq.clear();
        System.out.println("[sug-perf] Phase A sub: createSugVerticesFromIr=" + (System.currentTimeMillis() - vertexStart) + "ms, " + sug.getVertices().size() + " vertices, legacyRegimeHits=" +
                        legacyRegimeHits.size());

        long t0 = System.currentTimeMillis();
        buildVertexSourceIndex();
        System.out.println("[sug-perf] Phase A sub: buildVertexSourceIndex=" + (System.currentTimeMillis() - t0) + "ms");

        t0 = System.currentTimeMillis();
        buildConcatVertices(captured);
        System.out.println("[sug-perf] Phase A sub: buildConcatVertices=" + (System.currentTimeMillis() - t0) + "ms");

        t0 = System.currentTimeMillis();
        buildAccumulatorOpVertices(captured);
        System.out.println("[sug-perf] Phase A sub: buildAccumulatorOpVertices=" + (System.currentTimeMillis() - t0) + "ms");

        t0 = System.currentTimeMillis();
        classifyUsageVertices();
        System.out.println("[sug-perf] Phase A sub: classifyUsageVertices=" + (System.currentTimeMillis() - t0) + "ms");
    }

    /**
     * Creates one method's SUG vertices from its walk-phase scan records ({@code LfgWalk.collectSugScanRecords}):
     * new-instance, constant and invoke vertices (invokes resolved through {@link #methodBciToInvoke}), one VARIABLE per
     * stringy parameter (from the formal parameter flows) and one RETURN vertex for a stringy return type, shared by all
     * RETURN_EXIT LFG vertices.
     *
     * <p>{@code identityLinksLive} reproduces the two-pass cache regime: a second pass re-decoded every method the
     * bounded LRU ({@code IR_CACHE_MAX_ENTRIES}) had evicted, and the fresh node identities made its identity-keyed scans
     * fail. {@code true} = the method's graph would have been cache-served: the load vertices are created; {@code false}
     * = they are not.
     */
    private void createSugVerticesFromRecords(AnalysisMethod method, LocalFlowGraph lfg, boolean identityLinksLive) {
        // Create VARIABLE vertices for stringy-typed parameters.
        TypeFlow<?>[] paramFlows = null;
        if (method instanceof PointsToAnalysisMethod ptm) {
            MethodTypeFlow mtf = ptm.getTypeFlow();
            if (mtf != null && mtf.flowsGraphCreated()) {
                MethodFlowsGraph mfg = mtf.getMethodFlowsGraph();
                if (mfg != null && !mfg.isStub()) {
                    paramFlows = mfg.getParameters();
                }
            }
        }
        for (LocalFlowGraph.LocalVertex pv : lfg.getParamVertices()) {
            int idx = pv.paramIndex;
            AnalysisType paramType = null;
            if (paramFlows != null && idx < paramFlows.length && paramFlows[idx] != null) {
                paramType = paramFlows[idx].getDeclaredType();
            }
            if (paramType == null) {
                // Fall back to the recorded walk-graph ParameterNode stamp.
                if (lfg.paramStampTypes != null && idx < lfg.paramStampTypes.length) {
                    paramType = lfg.paramStampTypes[idx];
                }
            }
            if (!isStringyType(paramType)) {
                continue;
            }
            SugVertex v = sug.newVertex();
            v.setEnclosingMethod(method);
            v.setJavaType(paramType);
            v.setNodeType(SugNodeType.VARIABLE);
            v.setLabel("param" + idx);
            if (pv.typeFlow != null) {
                v.setSourceFlow(pv.typeFlow);
                initSourcePosition(v, pv.typeFlow);
                sug.registerFlow(pv.typeFlow, v);
            }
        }

        // Create RETURN vertices for stringy return type.
        AnalysisType returnType = null;
        if (method.getSignature() != null) {
            jdk.vm.ci.meta.JavaKind retKind = method.getSignature().getReturnKind();
            if (retKind == jdk.vm.ci.meta.JavaKind.Object) {
                ResolvedJavaType retType = method.getSignature().getReturnType(null);
                if (retType != null) {
                    returnType = resolveAnalysisType(retType);
                }
            }
        }
        if (isStringyType(returnType)) {
            TypeFlow<?> formalReturn = null;
            if (method instanceof PointsToAnalysisMethod ptm) {
                MethodTypeFlow mtf = ptm.getTypeFlow();
                if (mtf != null && mtf.flowsGraphCreated()) {
                    MethodFlowsGraph mfg = mtf.getMethodFlowsGraph();
                    if (mfg != null && !mfg.isStub()) {
                        formalReturn = mfg.getReturnFlow();
                    }
                }
            }
            for (LocalFlowGraph.LocalVertex rv : lfg.getReturnVertices()) {
                SugVertex v = sug.newVertex();
                v.setEnclosingMethod(method);
                v.setJavaType(returnType);
                v.setNodeType(SugNodeType.RETURN);
                v.setLabel("return");
                if (formalReturn != null) {
                    v.setSourceFlow(formalReturn);
                    initSourcePosition(v, formalReturn);
                    // Only register the first return vertex with the formal return flow;
                    // subsequent RETURN_EXIT vertices share the same typeFlow (set in
                    // buildLocalFlowForMethod) and would overwrite the first in the flow map.
                    if (sug.getVertex(formalReturn) == null) {
                        sug.registerFlow(formalReturn, v);
                    }
                }
            }
        }

        // The record scan (the recorded IR-node order).
        Map<Integer, InvokeTypeFlow> bciToInvoke = methodBciToInvoke.get(method);
        for (LocalFlowGraph.SugScanRecord rec : lfg.sugScanRecords) {
            switch (rec.kind) {
                case LocalFlowGraph.SugScanRecord.NEW_INSTANCE -> createNewInstanceVertexFromRecord(rec, method);
                case LocalFlowGraph.SugScanRecord.CONST_STRING -> createConstantVertexFromRecord(rec, method);
                case LocalFlowGraph.SugScanRecord.CONST_PRIMITIVE -> createPrimitiveConstantVertexFromRecord(rec, method);
                case LocalFlowGraph.SugScanRecord.INVOKE -> {
                    InvokeTypeFlow invFlow = bciToInvoke != null ? bciToInvoke.get(rec.bci) : null;
                    if (invFlow == null) {
                        continue;
                    }
                    createInvokeVertexByBci(invFlow, method);
                }
                case LocalFlowGraph.SugScanRecord.LOAD_FIELD, LocalFlowGraph.SugScanRecord.LOAD_INDEXED -> {
                    if (identityLinksLive) {
                        createLoadVertex(lfg, (Node) rec.node, method);
                    }
                }
                default -> {
                }
            }
        }
    }

    /**
     * The two-pass cache-regime simulation: a second pass calling {@code decodeIrGraph} for every LFG-bearing method
     * after the walk would hit the bounded LRU (the walk's own graph instance, identity links match) or re-decode (fresh
     * identities, identity links fail). Replays the walk-window decode sequence through an access-ordered
     * {@link LinkedHashMap} with the same capacity, then the second-pass access sequence ({@code localFlowGraphs}
     * order), and returns the methods that would hit. A pure function of the logged sequence.
     */
    private Set<AnalysisMethod> simulateLegacyA2Regime() {
        LinkedHashMap<AnalysisMethod, Boolean> sim = new LinkedHashMap<>(256, 0.75f, true) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<AnalysisMethod, Boolean> eldest) {
                return size() > IR_CACHE_MAX_ENTRIES;
            }
        };
        for (AnalysisMethod m : walkDecodeSeq) {
            sim.put(m, Boolean.TRUE);
        }
        Set<AnalysisMethod> hits = new LinkedHashSet<>();
        for (AnalysisMethod m : localFlowGraphs.keySet()) {
            if (sim.containsKey(m)) {
                sim.get(m);
                hits.add(m);
            } else {
                sim.put(m, Boolean.TRUE);
            }
        }
        return hits;
    }

    private void createLoadVertex(LocalFlowGraph lfg, Node loadNode, AnalysisMethod enclosing) {
        for (LocalFlowGraph.LocalVertex local : lfg.getVertices()) {
            if (local.irNode != loadNode || (local.kind != LocalFlowGraph.VertexKind.LOAD &&
                            local.kind != LocalFlowGraph.VertexKind.ARRAY_LOAD)) {
                continue;
            }
            SugVertex vertex = sug.newVertex();
            vertex.setEnclosingMethod(enclosing);
            vertex.setNodeType(SugNodeType.VARIABLE);
            vertex.setLabel(local.kind == LocalFlowGraph.VertexKind.LOAD ? "field-load" : "array-load");
            vertex.setJavaType(local.kind == LocalFlowGraph.VertexKind.LOAD && local.field != null
                            ? local.field.getType()
                            : local.arrayType);
            initSourcePositionFromNode(vertex, loadNode, enclosing);
            if (local.typeFlow != null) {
                vertex.setSourceFlow(local.typeFlow);
                sug.registerFlow(local.typeFlow, vertex);
            }
        }
    }

    /** The new-instance vertex of a scan record (the record carries the type name and the position key). */
    private void createNewInstanceVertexFromRecord(LocalFlowGraph.SugScanRecord rec, AnalysisMethod enclosing) {
        String t = rec.typeName;
        SugVertex v = sug.newVertex();
        v.setEnclosingMethod(enclosing);
        v.setJavaType(rec.type);
        v.setNodeType(t.equals("java.lang.String") ? SugNodeType.NEW_STRING : SugNodeType.NEW_ACCUMULATOR);
        v.setLabel(t.substring(t.lastIndexOf('.') + 1));
        v.setSourceLocation(rec.sourceLocation);
        if (rec.sourceKey != null) {
            v.setSourceKey(rec.sourceKey);
        }
    }

    /** The string-literal vertex of a scan record (interned: the shared representative is the first in records order). */
    private void createConstantVertexFromRecord(LocalFlowGraph.SugScanRecord rec, AnalysisMethod enclosing) {
        String text = rec.constText;
        boolean skipIntern = text.length() == 1;
        SugVertex interned = !skipIntern ? sug.internedLiterals().get(text) : null;
        if (interned != null) {
            return;
        }
        SugVertex v = sug.newVertex();
        v.setEnclosingMethod(enclosing);
        v.setNodeType(SugNodeType.STRING_LITERAL);
        v.setLiteralText(text);
        v.setLabel(text);
        v.setLength(text.length());
        AnalysisType stringType = resolveAnalysisTypeByName("java.lang.String");
        if (stringType != null) {
            v.setJavaType(stringType);
        }
        v.setSourceLocation(rec.sourceLocation);
        if (rec.sourceKey != null) {
            v.setSourceKey(rec.sourceKey);
        }
        if (!skipIntern) {
            sug.internedLiterals().putIfAbsent(text, v);
        }
    }

    /** The primitive-constant vertex of a scan record (CONSTANT_ARG, never identity-linked). */
    private void createPrimitiveConstantVertexFromRecord(LocalFlowGraph.SugScanRecord rec, AnalysisMethod enclosing) {
        SugVertex v = sug.newVertex();
        v.setEnclosingMethod(enclosing);
        v.setNodeType(SugNodeType.CONSTANT_ARG);
        v.setConstantValue(rec.constValue);
        v.setLabel(Long.toString(rec.constValue));
        v.setSourceLocation(rec.sourceLocation);
        if (rec.sourceKey != null) {
            v.setSourceKey(rec.sourceKey);
        }
    }

    /**
     * The bci-driven invoke-site vertex (the {@code createInvokeVertex} logic; bci-keyed, identity-immune).
     */
    private void createInvokeVertexByBci(InvokeTypeFlow invFlow, AnalysisMethod enclosing) {
        PointsToAnalysisMethod tm = invFlow.getTargetMethod();
        if (tm == null) {
            return;
        }
        String name = tm.getName();
        if (!SugNameTables.STRINGY_METHOD_NAMES.contains(name) && !ElementSources.isRowName(name)) { // + the element-source table's names
            return;
        }
        // Skip String.concat invokes that have a captured ConcatMethodSite — buildConcatMethodVertex
        // will create the CONCAT_EXPRESSION vertex for them.
        if (name.equals("concat") && hasConcatMethodSite(invFlow, enclosing)) {
            return;
        }
        // Skip accumulator ops (append/insert/delete/replace) — buildAccumulatorOpVertices creates them.
        if (isAccumulatorOpName(name, tm)) {
            return;
        }
        // Skip makeConcat — buildConcatVertices creates CONCAT_EXPRESSION from the capture hook.
        if (SugNameTables.CONCAT_INVOKE_NAMES.contains(name)) {
            return;
        }
        classifyInvokeFromFlow(invFlow, enclosing); // registers the site (no LFG-vertex links)
    }

    /**
     * The SUG usage-site vertex of a node-shaped strict class check (an intrinsified {@code GetClassNode} or a
     * canonicalized exact {@code x.getClass() == T.class} InstanceOfNode). Created in the LFG walk phase
     * ({@code LfgWalk.wireClassCheckSites}), never by a later re-scan: the bounded IR cache may re-decode a method
     * between phases, breaking node identity. One site per (method, bci): a JDK_LIBRARY_CALL labelled
     * {@code Object.getClass}, which the whitelist verdict rejects (getClass is whitelisted for no rep); a class check
     * in a provably dead arm is not recorded.
     */
    private final Map<String, SugVertex> classCheckSiteByMethodBci = new HashMap<>();
    private final Object classCheckSiteLock = new Object();

    SugVertex getOrCreateClassCheckSite(AnalysisMethod enclosing, int bci, String label, Node positionNode) {
        String key = (enclosing != null ? enclosing.format("%H#%n") : "null") + "@" + bci;
        synchronized (classCheckSiteLock) {
            SugVertex existing = classCheckSiteByMethodBci.get(key);
            if (existing != null) {
                return existing;
            }
            SugVertex v = sug.newVertex();
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass("java.lang.Object");
            v.setMethodName("getClass");
            v.setMethodSignature("");
            v.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
            v.setLabel(label != null ? label : "Object.getClass");
            initSourcePositionFromNode(v, positionNode, enclosing);
            classCheckSiteByMethodBci.put(key, v);
            return v;
        }
    }

    /**
     * The SUG usage site of a raw {@code java.lang.String} field read on a walked value
     * ({@code LfgWalk.mintRawStringFieldReadUsage}), created in the walk phase like the class-check site. One site
     * per (method, bci, field), never shared with a class-check site; a {@code JDK_LIBRARY_CALL} declared by
     * {@code java.lang.String}, named {@link SugNameTables#RAW_VALUE_USAGE} / {@link SugNameTables#RAW_CODER_USAGE}
     * with an empty signature; the heuristics' whitelists decide it per representation.
     */
    private final Map<String, SugVertex> rawFieldReadSiteByKey = new HashMap<>();

    SugVertex getOrCreateRawStringFieldReadSite(AnalysisMethod enclosing, int bci, String fieldName, Node positionNode) {
        String usageName = SugNameTables.rawStringFieldUsageName(fieldName);
        String key = (enclosing != null ? enclosing.format("%H#%n(%p)") : "null") + "@" + bci + "#" + usageName;
        synchronized (classCheckSiteLock) {
            SugVertex existing = rawFieldReadSiteByKey.get(key);
            if (existing != null) {
                return existing;
            }
            SugVertex v = sug.newVertex();
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass("java.lang.String");
            v.setMethodName(usageName);
            v.setMethodSignature("");
            v.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
            v.setLabel("String." + usageName);
            initSourcePositionFromNode(v, positionNode, enclosing);
            rawFieldReadSiteByKey.put(key, v);
            return v;
        }
    }

    private static boolean isAccumulatorOpName(String name, PointsToAnalysisMethod tm) {
        String decl = tm.getDeclaringClass().toJavaName(true);
        if (!SugNameTables.ACCUMULATOR_RECEIVERS.contains(decl)) {
            return false;
        }
        return name.equals("append") || name.equals("insert") || name.equals("delete") || name.equals("replace");
    }

    /**
     * Classifies an invoke from its {@link InvokeTypeFlow} (intern, Object.equals, non-stringy-receiver whitelisted
     * methods, accumulator toString, stringy-receiver invokes); creates its SUG vertex and registers it with the flow.
     */
    private SugVertex classifyInvokeFromFlow(InvokeTypeFlow inv, AnalysisMethod enclosing) {
        PointsToAnalysisMethod tm = inv.getTargetMethod();
        if (tm == null) {
            return null;
        }
        String name = tm.getName();
        if (!SugNameTables.STRINGY_METHOD_NAMES.contains(name) && !ElementSources.isRowName(name)) { // + the element-source table's names
            return null;
        }
        if (name.equals("concat") && hasConcatMethodSite(inv, enclosing)) {
            return null;
        }
        String decl = tm.getDeclaringClass().toJavaName(true);
        if (SugNameTables.isStrictClassCheckName(name, decl)) {
            // A strict class check of a stringy-capable value is an ordinary usage site (getClass on the receiver;
            // Class.isInstance/cast with the value as an argument). getClass is whitelisted for no rep, so a live-arm
            // class check rejects through the ordinary verdict. Scope: the receiver (getClass) or any argument
            // (isInstance/cast) can hold a stringy value by declared type (a conservative superset).
            boolean inScope;
            if (name.equals("getClass")) {
                TypeFlow<?> receiverFlow = inv.getReceiver();
                AnalysisType recvDeclType = receiverFlow != null ? receiverFlow.getDeclaredType() : null;
                inScope = recvDeclType == null || canHoldStringy(recvDeclType);
            } else {
                inScope = hasStringyArgument(inv);
            }
            if (inScope) {
                SugVertex v = sug.newVertex();
                v.setSourceFlow(inv);
                initSourcePosition(v, inv);
                v.setEnclosingMethod(enclosing);
                v.setDeclaringClass(decl);
                v.setMethodName(name);
                v.setMethodSignature(formatSignature(tm));
                v.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
                v.setLabel(decl.substring(decl.lastIndexOf('.') + 1) + "." + name);
                sug.registerFlow(inv, v);
                return v;
            }
            return null;
        }
        if (decl.equals(SugNameTables.STRING_INTERN_SUPPORT_CLASS) && name.equals("intern")) {
            SugVertex v = sug.newVertex();
            v.setSourceFlow(inv);
            initSourcePosition(v, inv);
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass("java.lang.String");
            v.setMethodName("intern");
            v.setMethodSignature(formatSignature(tm));
            v.setNodeType(SugNodeType.STRING_METHOD_CALL);
            v.setLabel("String.intern");
            sug.registerFlow(inv, v);
            return v;
        }
        if (name.equals("equals") && decl.equals("java.lang.Object")) {
            TypeFlow<?> receiverFlow = inv.getReceiver();
            if (receiverFlow == null) {
                return null;
            }
            AnalysisType recvDeclType = receiverFlow.getDeclaredType();
            if (recvDeclType != null && !canHoldStringy(recvDeclType)) {
                return null;
            }
            // Declared-type scope: a receiver whose declared type
            // {@link #canHoldStringy can hold stringy} stays in scope (conservative
            // superset of the points-to stringy states, deterministic).
            String enclosingName0 = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
            boolean jdkInternal0 = StringAnalysisPolicy.isInternalClass(enclosingName0);
            SugVertex v = sug.newVertex();
            v.setSourceFlow(inv);
            initSourcePosition(v, inv);
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass("java.lang.String");
            v.setMethodName("equals");
            v.setMethodSignature(formatSignature(tm));
            v.setNodeType(jdkInternal0 ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
            v.setLabel("Object.equals");
            sug.registerFlow(inv, v);
            return v;
        }
        if (!SugNameTables.STRINGY_INVOKE_RECEIVERS.contains(decl) && ElementSources.isSource(decl, name, formatSignature(tm))) {
            // A row of the element-source table whose receiver is not stringy (Pattern.splitAsStream/split)
            // gets its call vertex, as the generic tail makes one (an ELEM seed in user code; String rows reach the tail)
            String enclosingName0 = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
            boolean jdkInternal0 = StringAnalysisPolicy.isInternalClass(enclosingName0);
            SugVertex v = sug.newVertex();
            v.setSourceFlow(inv);
            initSourcePosition(v, inv);
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass(decl);
            v.setMethodName(name);
            v.setMethodSignature(formatSignature(tm));
            v.setNodeType(jdkInternal0 ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
            v.setLabel(decl.substring(decl.lastIndexOf('.') + 1) + "." + name);
            sug.registerFlow(inv, v);
            return v;
        }
        if (!tm.isStatic() && !SugNameTables.STRINGY_INVOKE_RECEIVERS.contains(decl) && !SugNameTables.ACCUMULATOR_RECEIVERS.contains(decl)) {
            TypeFlow<?>[] aps = inv.getActualParameters();
            if (aps == null || aps.length == 0 || aps[0] == null) {
                return null;
            }
            TypeFlow<?> receiverFlow = aps[0];
            AnalysisType recvDeclType = receiverFlow.getDeclaredType();
            if (recvDeclType != null && !canHoldStringy(recvDeclType)) {
                return null;
            }
            String sig = formatSignature(tm);
            if (!StringViewWhitelist.isWhitelisted(name, "java.lang.String", sig)) {
                return null;
            }
            // The declared-type gate above (canHoldStringy) is the scoping rule.
            String enclosingName0 = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
            boolean jdkInternal0 = StringAnalysisPolicy.isInternalClass(enclosingName0);
            SugVertex v = sug.newVertex();
            v.setSourceFlow(inv);
            initSourcePosition(v, inv);
            v.setEnclosingMethod(enclosing);
            v.setDeclaringClass("java.lang.String");
            v.setMethodName(name);
            v.setMethodSignature(sig);
            v.setNodeType(jdkInternal0 ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
            v.setLabel(decl.substring(decl.lastIndexOf('.') + 1) + "." + name);
            sug.registerFlow(inv, v);
            return v;
        }
        if (SugNameTables.ACCUMULATOR_RECEIVERS.contains(decl)) {
            if (name.equals("toString")) {
                String enclosingName = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
                boolean jdkInternal = StringAnalysisPolicy.isInternalClass(enclosingName);
                SugVertex v = sug.newVertex();
                v.setSourceFlow(inv);
                initSourcePosition(v, inv);
                v.setEnclosingMethod(enclosing);
                v.setDeclaringClass(decl);
                v.setMethodName(name);
                v.setMethodSignature(formatSignature(tm));
                v.setNodeType(jdkInternal ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
                v.setLabel(decl.substring(decl.lastIndexOf('.') + 1) + "." + name);
                sug.registerFlow(inv, v);
                return v;
            }
            if (hasStringyArgument(inv)) {
                return null;
            }
        }
        if (!SugNameTables.STRINGY_INVOKE_RECEIVERS.contains(decl)) {
            // java.util.Objects.equals(Object,Object) static content-compare — handled
            // before the SugNameTables.STRINGY_INVOKE_RECEIVERS rejection (Objects is not in that set).
            SugVertex v0 = classifyObjectsEquals(inv, enclosing);
            if (v0 != null) {
                return v0;
            }
            return null;
        }
        String enclosingName = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
        boolean jdkInternal = StringAnalysisPolicy.isInternalClass(enclosingName);
        SugVertex v = sug.newVertex();
        v.setSourceFlow(inv);
        initSourcePosition(v, inv);
        v.setEnclosingMethod(enclosing);
        v.setDeclaringClass(decl);
        v.setMethodName(name);
        v.setMethodSignature(formatSignature(tm));
        if (SugNameTables.CONCAT_INVOKE_NAMES.contains(name)) {
            v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
            v.setLabel(name);
        } else {
            v.setNodeType(jdkInternal ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
            v.setLabel(decl.substring(decl.lastIndexOf('.') + 1) + "." + name);
        }
        sug.registerFlow(inv, v);
        return v;
    }

    /**
     * {@code java.util.Objects.equals(Object, Object)}: a static wrapper whose parameters both flow to
     * {@code Object.equals}. The vertex is labelled as a {@code String.equals} usage, so the LFG walk maps the parameter
     * flow (UsageRole.PARAMETER) instead of UNMAPPED_USAGE and the usage is checked against W_view (which contains
     * {@code equals}; String.equals and the StringView override are safe on a lazy rep). Admission stays whitelist-gated.
     */
    private SugVertex classifyObjectsEquals(InvokeTypeFlow inv, AnalysisMethod enclosing) {
        TypeFlow<?>[] params = inv.getActualParameters();
        if (params == null || params.length != 2) {
            return null;
        }
        if (!canHoldStringyNullable(params[0]) && !canHoldStringyNullable(params[1])) {
            return null;
        }
        String enclosingName = enclosing != null ? enclosing.getDeclaringClass().toJavaName(true) : null;
        boolean jdkInternal = StringAnalysisPolicy.isInternalClass(enclosingName);
        SugVertex v = sug.newVertex();
        v.setSourceFlow(inv);
        initSourcePosition(v, inv);
        v.setEnclosingMethod(enclosing);
        v.setDeclaringClass("java.lang.String");
        v.setMethodName("equals");
        v.setMethodSignature("(Ljava/lang/Object;)");
        v.setNodeType(jdkInternal ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
        v.setLabel("Objects.equals");
        sug.registerFlow(inv, v);
        return v;
    }

    /**
     * Whether some argument's declared type {@link #canHoldStringyNullable can hold stringy} (a conservative,
     * deterministic superset: a wider scope only creates more invoke vertices, each whitelist-gated downstream).
     */
    private boolean hasStringyArgument(InvokeTypeFlow inv) {
        TypeFlow<?>[] params = inv.getActualParameters();
        if (params == null || params.length <= 1) {
            return false;
        }
        for (int i = 1; i < params.length; i++) {
            TypeFlow<?> param = params[i];
            if (param == null) {
                continue;
            }
            AnalysisType dt = param.getDeclaredType();
            if (dt != null) {
                String tn = dt.toJavaName(true);
                if (SugNameTables.STRINGY_ALLOC_TYPES.contains(tn) || "java.lang.CharSequence".equals(tn)) {
                    return true;
                }
            }
            if (canHoldStringyNullable(param)) {
                return true;
            }
        }
        return false;
    }

    private void classifyUsageVertices() {
        for (SugVertex v : sug.getVertices()) {
            SugNodeType t = v.getNodeType();
            if (t == SugNodeType.STRING_METHOD_CALL || t == SugNodeType.JDK_LIBRARY_CALL ||
                            t == SugNodeType.CONCAT_EXPRESSION) {
                usageVertices.add(v);
            }
        }
    }

    private void phaseBDownstreamSearch(AnalysisUniverse universe) {
        int trackTargetCount = sug.getVertices().size();
        System.out.println("[sug-perf] Phase B (unified) start: " + trackTargetCount + " track targets");
        long phaseBStartTime = System.currentTimeMillis();
        // The structural edges come from type-flow actuals (sug.getVertex(flow)); Phase A registered the vertices with
        // their type flows.
        buildInvokeQualifierParameterEdges();
        // Step 1: the LFGs built in Phase A.
        Map<AnalysisMethod, LocalFlowGraph> localFlows = localFlowGraphs;
        System.out.println("[sug-perf] Phase B Step 1 (local flows) reused: " + localFlows.size() + " methods");
        // Step 2: the forward fixpoint, the sole source of usageTags/sourceTags/incompleteTrace.
        long step2Start = System.currentTimeMillis();
        ForwardFixpoint.runAndEmit(sug, localFlows, methodBciToInvoke, lfgWalk);
        System.out.println("[sug-perf] Phase B Step 2 (forward fixpoint) done: " + (System.currentTimeMillis() - step2Start) + "ms");
        System.out.println("[sug-perf] Phase B (unified) done: " + (System.currentTimeMillis() - phaseBStartTime) + "ms");
    }

    // ==================== Helper methods ====================

    /** A non-stringy but can-hold-stringy actual-return flow (for the {@code createConcatReturnFlowNode} fallback). */
    private boolean isNonStringyActualReturnFlow(TypeFlow<?> flow) {
        if (!(flow instanceof ActualReturnTypeFlow)) {
            return false;
        }
        AnalysisType dt = flow.getDeclaredType();
        return dt != null && canHoldStringy(dt) && !isStringyType(dt);
    }

    private boolean isUsageVertex(SugVertex v) {
        SugNodeType t = v.getNodeType();
        return t == SugNodeType.STRING_METHOD_CALL || t == SugNodeType.JDK_LIBRARY_CALL || t == SugNodeType.CONCAT_EXPRESSION;
    }

    private SugVertex getOrCreateFlowNodeVertex(TypeFlow<?> flow) {
        SugVertex existing = sug.getVertex(flow);
        if (existing != null) {
            return existing;
        }
        AnalysisType dt = flow.getDeclaredType();
        // Declared-type scoping: stringy or can-hold-stringy (a deterministic superset of the points-to stringy states).
        boolean stringyDecl = dt != null && isStringyType(dt);
        if (!stringyDecl && (dt == null || !canHoldStringy(dt))) {
            return null;
        }
        synchronized (parallelLock) {
            existing = sug.getVertex(flow);
            if (existing != null) {
                return existing;
            }
            SugVertex v = sug.newVertex();
            v.setSourceFlow(flow);
            initSourcePosition(v, flow);
            v.setEnclosingMethod(flow.method());
            v.setJavaType(dt);
            v.setNodeType(SugNodeType.FLOW_NODE);
            sug.registerFlow(flow, v);
            return v;
        }
    }

    /**
     * Creates a {@code FLOW_NODE} vertex for a flow without the scope check of {@link #getOrCreateFlowNodeVertex}: for
     * usage-site receivers/arguments and {@code equals} arguments it would reject, so the PARAMETER/QUALIFIER edges the
     * fixpoint seeds from exist, and for non-stringy can-hold-stringy concat return flows.
     */
    private SugVertex forceCreateFlowNodeVertex(TypeFlow<?> flow) {
        SugVertex existing = sug.getVertex(flow);
        if (existing != null) {
            return existing;
        }
        synchronized (parallelLock) {
            existing = sug.getVertex(flow);
            if (existing != null) {
                return existing;
            }
            SugVertex v = sug.newVertex();
            v.setSourceFlow(flow);
            initSourcePosition(v, flow);
            v.setEnclosingMethod(flow.method());
            v.setJavaType(flow.getDeclaredType());
            v.setNodeType(SugNodeType.FLOW_NODE);
            sug.registerFlow(flow, v);
            return v;
        }
    }

    StructuredGraph decodeIrGraph(AnalysisMethod method) {
        StructuredGraph cached = irGraphCache.get(method);
        if (cached != null) {
            if (decodePhase == 0) {
                walkDecodeSeq.add(method);
            }
            return cached;
        }
        if (!(method instanceof PointsToAnalysisMethod)) {
            return null;
        }
        if (method.getAnalyzedGraph() == null) {
            return null;
        }
        Iterable<EncodedNodeReference> nodeReferences = null;
        if (irDebugContext == null) {
            irDebugContext = new DebugContext.Builder(bb.getOptions(),
                            new GraalDebugHandlersFactory(bb.getSnippetReflectionProvider())).build();
        }
        StructuredGraph graph = method.decodeAnalyzedGraph(irDebugContext, nodeReferences);
        if (graph != null) {
            // LRU eviction is handled by removeEldestEntry in the LinkedHashMap override.
            irGraphCache.put(method, graph);
            if (decodePhase == 0) {
                walkDecodeSeq.add(method);
            }
        }
        return graph;
    }

    /**
     * Force-parses a method the points-to analysis never decoded: almost always a target only the deterministic CHA
     * reaches (bytecode but no analyzed graph: an instantiated-subtype implementation points-to never linked).
     *
     * <p>Parse shape: the {@code AnalysisParsedGraph} regular-method parse (same {@code GraphBuilderConfiguration}:
     * eager resolving, unresolved-not-error, node positions, CheckAll bytecode exceptions, retained locals; same
     * {@code createGraphBuilderPhase}) without the analysis's parse hooks ({@code methodAfterParsingHook} notifies SVM
     * features whose state is analysis-phase, e.g. an NPE in {@code EnumSwitchFeature.methodsSafeForExecution}) and
     * without the encode/decode roundtrip (no pre-analysis optimization, so allocations stay plain
     * {@code NewInstanceNode}s; graph building never inlines). Only adds information; {@code null} on any failure (the
     * MISSING_IR fact stays).
     */
    StructuredGraph forceParseIrGraph(AnalysisMethod method) {
        try {
            if (method.getCode() == null) {
                return null;
            }
            OptionValues options = bb.getOptions();
            if (irDebugContext == null) {
                irDebugContext = new DebugContext.Builder(options,
                                new GraalDebugHandlersFactory(bb.getSnippetReflectionProvider())).build();
            }
            StructuredGraph graph = new StructuredGraph.Builder(options, irDebugContext)
                            .method(method)
                            .recordInlinedMethods(bb.getHostVM().recordInlinedMethods(method))
                            .build();
            GraphBuilderConfiguration config = GraphBuilderConfiguration.getDefault(bb.getProviders(method).getGraphBuilderPlugins())
                            .withEagerResolving(true)
                            .withUnresolvedIsError(false)
                            .withNodeSourcePosition(true)
                            .withBytecodeExceptionMode(GraphBuilderConfiguration.BytecodeExceptionMode.CheckAll)
                            .withRetainLocalVariables(true);
            config = bb.getHostVM().updateGraphBuilderConfiguration(config, method);
            bb.getHostVM().createGraphBuilderPhase(bb.getProviders(method), config, OptimisticOptimizations.NONE, null).apply(graph);
            irGraphCache.put(method, graph);
            return graph;
        } catch (Throwable t) {
            // The method keeps its MISSING_IR fact (known failure class: SharedBytecodeParser's post-analysis
            // "Initializing type after analysis" guard).
            return null;
        }
    }

    private void buildInvokeQualifierParameterEdges() {
        for (SugVertex v : new ArrayList<>(sug.getVertices())) {
            TypeFlow<?> src = v.getSourceFlow();
            if (!(src instanceof InvokeTypeFlow inv)) {
                continue;
            }
            addInvokeEdges(inv, v);
        }
    }

    private void addInvokeEdges(InvokeTypeFlow inv, SugVertex invokeVertex) {
        TypeFlow<?>[] actuals = inv.getActualParameters();
        if (actuals == null || actuals.length == 0) {
            return;
        }
        PointsToAnalysisMethod tm = inv.getTargetMethod();
        boolean isStatic = tm != null && tm.isStatic();
        boolean internInvoke = isInternInvoke(inv);
        int start = isStatic ? 0 : 1;
        // Usage sites force-create receiver/argument vertices so the QUALIFIER/PARAMETER edges exist for the fixpoint
        // to seed (else a generic-typed receiver, e.g. Comparable.compareTo in TreeMap.getEntry, has no edge).
        boolean isUsageSite = invokeVertex.getNodeType() == SugNodeType.STRING_METHOD_CALL ||
                        invokeVertex.getNodeType() == SugNodeType.JDK_LIBRARY_CALL;
        if (!isStatic) {
            TypeFlow<?> receiver = actuals[0];
            SugVertex recvVertex = sug.getVertex(receiver);
            if (recvVertex == null) {
                recvVertex = getOrCreateFlowNodeVertex(receiver);
            }
            if (recvVertex == null && isUsageSite && canHoldStringy(receiver.getDeclaredType())) {
                recvVertex = forceCreateFlowNodeVertex(receiver);
            }
            if (recvVertex != null && recvVertex != invokeVertex) {
                sug.addEdge(recvVertex, invokeVertex, SugEdgeType.QUALIFIER, -1);
            }
        }
        for (int i = start; i < actuals.length; i++) {
            if (internInvoke && i == 0) {
                continue;
            }
            TypeFlow<?> arg = actuals[i];
            if (arg == null) {
                continue;
            }
            SugVertex argVertex = sug.getVertex(arg);
            if (argVertex == null) {
                argVertex = getOrCreateFlowNodeVertex(arg);
            }
            if (argVertex == null && isUsageSite && canHoldStringy(arg.getDeclaredType())) {
                argVertex = forceCreateFlowNodeVertex(arg);
            }
            if (argVertex != null && argVertex != invokeVertex) {
                sug.addEdge(argVertex, invokeVertex, SugEdgeType.PARAMETER, isStatic ? i : i - 1);
            }
        }
        if (internInvoke && actuals[0] != null) {
            SugVertex argVertex = sug.getVertex(actuals[0]);
            if (argVertex == null) {
                argVertex = getOrCreateFlowNodeVertex(actuals[0]);
            }
            if (argVertex != null && argVertex != invokeVertex) {
                sug.addEdge(argVertex, invokeVertex, SugEdgeType.QUALIFIER, -1);
            }
        }
        TypeFlow<?> ret = inv.getActualReturn();
        if (ret != null) {
            SugVertex retVertex = sug.getVertex(ret);
            if (retVertex == null) {
                retVertex = getOrCreateFlowNodeVertex(ret);
            }
            if (retVertex != null && retVertex != invokeVertex) {
                if (!hasEdge(invokeVertex, retVertex, SugEdgeType.DATAFLOW)) {
                    sug.addEdge(invokeVertex, retVertex, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
                }
                if (invokeVertex.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) {
                    if (!hasEdge(invokeVertex, retVertex, SugEdgeType.JDK)) {
                        sug.addEdge(invokeVertex, retVertex, SugEdgeType.JDK, -1, SugEdge.FlowRole.RECEIVER);
                    }
                }
            }
        }
    }

    private void phaseCCleanup() {
        Set<SugVertex> removedVertices = new HashSet<>();
        mergeNonUsageVertices(removedVertices);
        pruneDeadEndContainers(removedVertices);
        sug.bulkRemove(removedVertices);
    }

    /**
     * Collapses pass-through vertices: a {@code FLOW_NODE}/{@code VARIABLE}/{@code RETURN} vertex with exactly one
     * in-edge and one out-edge (both {@code DATAFLOW}) is replaced by a direct edge.
     */
    private void mergeNonUsageVertices(Set<SugVertex> removed) {
        Deque<SugVertex> worklist = new ArrayDeque<>();
        Set<SugVertex> inWorklist = new HashSet<>();
        for (SugVertex v : new ArrayList<>(sug.getVertices())) {
            if (isPassthroughCandidate(v)) {
                worklist.add(v);
                inWorklist.add(v);
            }
        }
        while (!worklist.isEmpty()) {
            SugVertex v = worklist.pollFirst();
            inWorklist.remove(v);
            if (removed.contains(v)) {
                continue;
            }
            if (!isPassthroughCandidate(v)) {
                continue;
            }
            List<SugEdge> inEdges = new ArrayList<>(v.getInEdges());
            List<SugEdge> outEdges = new ArrayList<>(v.getOutEdges());
            if (inEdges.size() != 1 || outEdges.size() != 1) {
                continue;
            }
            SugEdge in = inEdges.get(0);
            SugEdge out = outEdges.get(0);
            if (in.getEdgeType() != SugEdgeType.DATAFLOW || out.getEdgeType() != SugEdgeType.DATAFLOW) {
                continue;
            }
            SugVertex producer = in.getFrom();
            SugVertex consumer = out.getTo();
            if (producer == v || consumer == v || producer == consumer) {
                markVertexRemoved(v, removed);
                continue;
            }
            if (!hasEdge(producer, consumer, SugEdgeType.DATAFLOW)) {
                SugEdge.FlowRole mergedRole = (in.getFlowRole() == out.getFlowRole())
                                ? in.getFlowRole()
                                : SugEdge.FlowRole.NONE;
                sug.addEdge(producer, consumer, SugEdgeType.DATAFLOW, -1, mergedRole);
            }
            markVertexRemoved(v, removed);
            for (SugVertex neighbor : List.of(producer, consumer)) {
                if (!removed.contains(neighbor) && !inWorklist.contains(neighbor) && isPassthroughCandidate(neighbor)) {
                    worklist.add(neighbor);
                    inWorklist.add(neighbor);
                }
            }
        }
    }

    private boolean isPassthroughCandidate(SugVertex v) {
        if (isUsageVertex(v)) {
            return false;
        }
        SugNodeType t = v.getNodeType();
        return t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE || t == SugNodeType.RETURN;
    }

    /** Prunes dead-end container vertices: a container track target that reaches no usage vertex is removed. */
    private void pruneDeadEndContainers(Set<SugVertex> removed) {
        Set<SugVertex> reachableToUsage = new HashSet<>();
        Set<SugVertex> allUsage = new HashSet<>();
        for (SugVertex v : sug.getVertices()) {
            if (isUsageVertex(v)) {
                allUsage.add(v);
            }
        }
        Deque<SugVertex> work = new ArrayDeque<>(allUsage);
        reachableToUsage.addAll(allUsage);
        while (!work.isEmpty()) {
            SugVertex v = work.pollFirst();
            for (SugEdge e : new ArrayList<>(v.getInEdges())) {
                SugVertex from = e.getFrom();
                if (reachableToUsage.add(from)) {
                    work.add(from);
                }
            }
        }
        for (SugVertex v : new ArrayList<>(sug.getVertices())) {
            if (isUsageVertex(v)) {
                continue;
            }
            SugNodeType t = v.getNodeType();
            if (t != SugNodeType.FLOW_NODE) {
                continue;
            }
            if (v.getLabel() != null && v.getLabel().startsWith("container:")) {
                if (!reachableToUsage.contains(v)) {
                    markVertexRemoved(v, removed);
                }
            }
        }
    }

    private boolean hasEdge(SugVertex from, SugVertex to, SugEdgeType type) {
        for (SugEdge e : from.getOutEdges()) {
            if (e.getTo() == to && e.getEdgeType() == type) {
                return true;
            }
        }
        return false;
    }

    private void markVertexRemoved(SugVertex v, Set<SugVertex> removed) {
        for (SugEdge e : new ArrayList<>(v.getInEdges())) {
            e.getFrom().removeOutEdge(e);
        }
        for (SugEdge e : new ArrayList<>(v.getOutEdges())) {
            e.getTo().removeInEdge(e);
        }
        v.clearEdges();
        removed.add(v);
        nonUsageVertices.remove(v);
    }

    private void buildConcatVertices(Map<AnalysisMethod, List<CapturedSite>> captured) {
        if (captured == null || captured.isEmpty()) {
            return;
        }
        for (Map.Entry<AnalysisMethod, List<CapturedSite>> entry : captured.entrySet()) {
            AnalysisMethod enclosing = entry.getKey();
            for (CapturedSite site : entry.getValue()) {
                if (site instanceof ConcatSite cs) {
                    buildConcatVertex(cs, enclosing);
                } else if (site instanceof ConcatMethodSite cms) {
                    buildConcatMethodVertex(cms, enclosing);
                }
            }
        }
    }

    private static Map<AnalysisMethod, Set<Integer>> buildConcatMethodSiteBciIndex(Map<AnalysisMethod, List<CapturedSite>> captured) {
        if (captured == null || captured.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<AnalysisMethod, Set<Integer>> idx = new LinkedHashMap<>();
        for (Map.Entry<AnalysisMethod, List<CapturedSite>> entry : captured.entrySet()) {
            for (CapturedSite site : entry.getValue()) {
                if (site instanceof ConcatMethodSite cms) {
                    idx.computeIfAbsent(entry.getKey(), k -> new HashSet<>()).add(cms.bci());
                }
            }
        }
        return idx;
    }

    private boolean hasConcatMethodSite(InvokeTypeFlow inv, AnalysisMethod enclosing) {
        Set<Integer> bcis = concatMethodSiteBcis.get(enclosing);
        if (bcis == null || bcis.isEmpty()) {
            return false;
        }
        Object src = inv.getSource();
        if (src instanceof BytecodePosition pos) {
            return bcis.contains(pos.getBCI());
        }
        return false;
    }

    private void buildAccumulatorOpVertices(Map<AnalysisMethod, List<CapturedSite>> captured) {
        if (captured == null || captured.isEmpty()) {
            return;
        }
        for (Map.Entry<AnalysisMethod, List<CapturedSite>> entry : captured.entrySet()) {
            AnalysisMethod enclosing = entry.getKey();
            for (CapturedSite site : entry.getValue()) {
                if (site instanceof AccumulatorOpSite aos) {
                    buildAccumulatorOpVertex(aos, enclosing);
                }
            }
        }
    }

    private void buildAccumulatorOpVertex(AccumulatorOpSite aos, AnalysisMethod enclosing) {
        String targetQualified = aos.targetQualified();
        int dot = targetQualified.lastIndexOf('.');
        String declaringClass = dot >= 0 ? targetQualified.substring(0, dot) : targetQualified;
        String methodName = dot >= 0 ? targetQualified.substring(dot + 1) : targetQualified;
        Map<Integer, InvokeTypeFlow> bciMap = methodBciToInvoke.get(enclosing);
        InvokeTypeFlow invFlow = bciMap != null ? bciMap.get(aos.bci()) : null;
        SugVertex existing = invFlow != null ? sug.getVertex(invFlow) : null;
        SugVertex op;
        if (existing != null) {
            op = existing;
        } else {
            op = sug.newVertex();
            op.setNodeType(SugNodeType.STRING_METHOD_CALL);
            op.setSourceLocation(aos.sourceLocation());
            op.setEnclosingMethod(enclosing);
            op.setDeclaringClass(declaringClass);
            op.setMethodName(methodName);
            op.setLabel(declaringClass.substring(declaringClass.lastIndexOf('.') + 1) + "." + methodName);
            if (invFlow != null) {
                sug.registerFlow(invFlow, op);
                // Downstream passes resolve the target method via getSourceFlow().
                op.setSourceFlow(invFlow);
                // The signature lets StringViewWhitelist gate on argument types (append(String) is safe,
                // append(CharSequence,int,int) reads value()).
                PointsToAnalysisMethod tm = invFlow.getTargetMethod();
                if (tm != null) {
                    op.setMethodSignature(formatSignature(tm));
                }
            }
        }
        op.markAccumulatorOp();
        if (invFlow != null && existing == null) {
            TypeFlow<?> ret = invFlow.getActualReturn();
            if (ret != null) {
                SugVertex retVertex = sug.getVertex(ret);
                if (retVertex == null) {
                    retVertex = getOrCreateFlowNodeVertex(ret);
                }
                if (retVertex != null && retVertex != op && !hasEdge(op, retVertex, SugEdgeType.DATAFLOW)) {
                    sug.addEdge(op, retVertex, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
                }
            }
        }
        SugVertex receiver = ReceiverCorrelation.correlateReceiverByKey(aos.receiverSourceKey(), aos.receiverLocation(), enclosing,
                        verticesBySourceKeyForAccumulator, verticesByEnclosingAndSourceForAccumulator);
        if (receiver != null && receiver != op) {
            sug.addEdge(receiver, op, SugEdgeType.QUALIFIER, -1);
        }
    }

    private void buildConcatVertex(ConcatSite cs, AnalysisMethod enclosing) {
        SugVertex concat = sug.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation(cs.sourceLocation());
        concat.setEnclosingMethod(enclosing);
        concat.setMethodName(cs.bootstrapName());
        concat.setLabel(cs.bootstrapName());
        concat.setDynamicOperandCount(cs.dynamicOperandCount());
        concat.setConcatRecipe(cs.recipe());
        concat.setConcatOperandKinds(cs.operandKinds());
        List<OperandRef> dynRefs = cs.operands();
        List<String> opLocs = new ArrayList<>(dynRefs.size());
        for (OperandRef op : dynRefs) {
            opLocs.add(op != null ? op.sourceLocation() : null);
        }
        concat.setOperandSourceLocations(opLocs);
        InvokeTypeFlow concatInvoke = findConcatInvoke(cs, enclosing);
        if (concatInvoke != null) {
            concat.setSourceFlow(concatInvoke);
            initSourcePosition(concat, concatInvoke);
            sug.registerFlow(concatInvoke, concat);
        }
        List<SugVertex> orderedOperands = buildOrderedOperands(cs, enclosing);
        for (int i = 0; i < orderedOperands.size(); i++) {
            SugEdgeType edgeType = (i % 2 == 0) ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT;
            sug.addEdge(orderedOperands.get(i), concat, edgeType, i);
        }
        if (concatInvoke != null) {
            TypeFlow<?> ret = concatInvoke.getActualReturn();
            if (ret != null) {
                SugVertex retVertex = sug.getVertex(ret);
                if (retVertex == null) {
                    retVertex = getOrCreateFlowNodeVertex(ret);
                }
                if (retVertex == null && isNonStringyActualReturnFlow(ret)) {
                    retVertex = forceCreateFlowNodeVertex(ret);
                }
                if (retVertex != null && retVertex != concat) {
                    sug.addEdge(concat, retVertex, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
                }
            }
        }
    }

    private List<SugVertex> buildOrderedOperands(ConcatSite cs, AnalysisMethod enclosing) {
        List<OperandRef> dynRefs = cs.operands();
        List<String> constants = cs.constantOperands();
        String recipe = cs.recipe();
        if (recipe != null) {
            return buildOrderedOperandsFromRecipe(cs, enclosing, recipe, dynRefs, constants);
        }
        int total = Math.max(cs.totalOperandCount(), cs.dynamicOperandCount());
        List<SugVertex> result = new ArrayList<>(total);
        for (int i = 0; i < total; i++) {
            SugVertex operand;
            if (i < cs.dynamicOperandCount() && i < dynRefs.size()) {
                operand = correlateOperand(dynRefs.get(i), enclosing);
            } else {
                operand = null;
            }
            if (operand == null) {
                int constantIndex = i - cs.dynamicOperandCount();
                String text = (constantIndex >= 0 && constantIndex < constants.size()) ? constants.get(constantIndex) : null;
                operand = syntheticOperandVertex(i < cs.dynamicOperandCount(), enclosing, cs.sourceLocation(), text);
            }
            result.add(operand);
        }
        return result;
    }

    private List<SugVertex> buildOrderedOperandsFromRecipe(ConcatSite cs, AnalysisMethod enclosing, String recipe,
                    List<OperandRef> dynRefs, List<String> constants) {
        List<SugVertex> result = new ArrayList<>();
        int dynIndex = 0;
        int constIndex = 0;
        StringBuilder literal = new StringBuilder();
        for (int i = 0; i < recipe.length(); i++) {
            char c = recipe.charAt(i);
            if (c == RECIPE_DYNAMIC_TAG) {
                if (!literal.isEmpty()) {
                    String text = literal.toString();
                    result.add(syntheticOperandVertex(false, enclosing, cs.sourceLocation(), text));
                    literal.setLength(0);
                }
                SugVertex operand = null;
                if (dynIndex < dynRefs.size()) {
                    operand = correlateOperand(dynRefs.get(dynIndex), enclosing);
                }
                if (operand == null) {
                    operand = syntheticOperandVertex(true, enclosing, cs.sourceLocation(), null);
                }
                result.add(operand);
                dynIndex++;
            } else if (c == RECIPE_CONSTANT_TAG) {
                if (!literal.isEmpty()) {
                    String text = literal.toString();
                    result.add(syntheticOperandVertex(false, enclosing, cs.sourceLocation(), text));
                    literal.setLength(0);
                }
                String text = (constIndex < constants.size()) ? constants.get(constIndex) : null;
                result.add(syntheticOperandVertex(false, enclosing, cs.sourceLocation(), text));
                constIndex++;
            } else {
                literal.append(c);
            }
        }
        if (!literal.isEmpty()) {
            String text = literal.toString();
            result.add(syntheticOperandVertex(false, enclosing, cs.sourceLocation(), text));
        }
        return result;
    }

    private static final char RECIPE_DYNAMIC_TAG = '\u0001';
    private static final char RECIPE_CONSTANT_TAG = '\u0002';

    private InvokeTypeFlow findConcatInvoke(ConcatSite cs, AnalysisMethod enclosing) {
        return findConcatInvoke(cs.bci(), enclosing);
    }

    private void buildConcatMethodVertex(ConcatMethodSite cms, AnalysisMethod enclosing) {
        SugVertex concat = sug.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation(cms.sourceLocation());
        concat.setEnclosingMethod(enclosing);
        concat.setMethodName("concat");
        concat.setLabel("concat");
        concat.setDynamicOperandCount(2);
        List<OperandRef> refs = cms.operands();
        List<String> opLocs = new ArrayList<>(2);
        for (OperandRef op : refs) {
            opLocs.add(op != null ? op.sourceLocation() : null);
        }
        concat.setOperandSourceLocations(opLocs);
        InvokeTypeFlow concatInvoke = findConcatInvoke(cms.bci(), enclosing);
        if (concatInvoke != null) {
            concat.setSourceFlow(concatInvoke);
            initSourcePosition(concat, concatInvoke);
            sug.registerFlow(concatInvoke, concat);
        }
        List<SugVertex> orderedOperands = new ArrayList<>(2);
        for (int i = 0; i < 2; i++) {
            OperandRef ref = (i < refs.size()) ? refs.get(i) : null;
            SugVertex operand = (ref != null) ? correlateOperand(ref, enclosing) : null;
            if (operand == null) {
                operand = syntheticOperandVertex(true, enclosing, cms.sourceLocation(), null);
            }
            orderedOperands.add(operand);
        }
        for (int i = 0; i < orderedOperands.size(); i++) {
            SugEdgeType edgeType = (i % 2 == 0) ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT;
            sug.addEdge(orderedOperands.get(i), concat, edgeType, i);
        }
        if (concatInvoke != null) {
            TypeFlow<?> ret = concatInvoke.getActualReturn();
            if (ret != null) {
                SugVertex retVertex = sug.getVertex(ret);
                if (retVertex == null) {
                    retVertex = getOrCreateFlowNodeVertex(ret);
                }
                if (retVertex == null && isNonStringyActualReturnFlow(ret)) {
                    retVertex = forceCreateFlowNodeVertex(ret);
                }
                if (retVertex != null && retVertex != concat) {
                    sug.addEdge(concat, retVertex, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
                }
            }
        }
    }

    private InvokeTypeFlow findConcatInvoke(int bci, AnalysisMethod enclosing) {
        if (!(enclosing instanceof PointsToAnalysisMethod ptm)) {
            return null;
        }
        Map<Integer, InvokeTypeFlow> bciMap = methodBciToInvoke.get(enclosing);
        if (bciMap != null) {
            return bciMap.get(bci);
        }
        MethodTypeFlow mtf = ptm.getTypeFlow();
        if (mtf == null || !mtf.flowsGraphCreated()) {
            return null;
        }
        MethodFlowsGraph graph = mtf.getMethodFlowsGraph();
        if (graph.isStub()) {
            return null;
        }
        for (InvokeTypeFlow inv : graph.getInvokes()) {
            Object src = inv.getSource();
            if (src instanceof BytecodePosition pos) {
                if (pos.getBCI() == bci) {
                    return inv;
                }
            }
        }
        return null;
    }

    private void buildVertexSourceIndex() {
        Map<AnalysisMethod, Map<String, List<SugVertex>>> idx = new LinkedHashMap<>();
        Map<String, List<SugVertex>> sourceKeyIdx = new LinkedHashMap<>();
        Map<AnalysisMethod, Map<String, List<SugVertex>>> accIdx = new LinkedHashMap<>();
        for (SugVertex v : sug.getVertices()) {
            SugNodeType t = v.getNodeType();
            if (t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE || t == SugNodeType.NEW_STRING) {
                AnalysisMethod enc = v.getEnclosingMethod();
                if (enc != null && v.getSourceLocation() != null) {
                    idx.computeIfAbsent(enc, k -> new LinkedHashMap<>())
                                    .computeIfAbsent(v.getSourceLocation(), k -> new ArrayList<>())
                                    .add(v);
                }
            }
            if (t == SugNodeType.NEW_ACCUMULATOR || t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE) {
                String sk = v.getSourceKey();
                if (sk != null) {
                    sourceKeyIdx.computeIfAbsent(sk, k -> new ArrayList<>()).add(v);
                }
                AnalysisMethod enc = v.getEnclosingMethod();
                if (enc != null && v.getSourceLocation() != null) {
                    accIdx.computeIfAbsent(enc, k -> new LinkedHashMap<>())
                                    .computeIfAbsent(v.getSourceLocation(), k -> new ArrayList<>())
                                    .add(v);
                }
            }
        }
        this.verticesByEnclosingAndSource = idx;
        this.verticesBySourceKeyForAccumulator = sourceKeyIdx;
        this.verticesByEnclosingAndSourceForAccumulator = accIdx;
    }

    private SugVertex correlateOperand(OperandRef op, AnalysisMethod enclosing) {
        if (op == null || op.sourceLocation() == null) {
            return null;
        }
        Map<String, List<SugVertex>> bySource = verticesByEnclosingAndSource.get(enclosing);
        if (bySource == null) {
            return null;
        }
        List<SugVertex> candidates = bySource.get(op.sourceLocation());
        if (candidates == null || candidates.size() != 1) {
            return null;
        }
        return candidates.get(0);
    }

    private SugVertex syntheticOperandVertex(boolean dynamic, AnalysisMethod enclosing, String sourceLocation, String literalText) {
        SugVertex v = sug.newVertex();
        v.setEnclosingMethod(enclosing);
        v.setSourceLocation(sourceLocation);
        if (dynamic) {
            v.setNodeType(SugNodeType.VARIABLE);
            v.setLabel("concat-operand");
        } else {
            v.setNodeType(SugNodeType.STRING_LITERAL);
            v.setLabel("concat-constant");
            v.setLiteralText(literalText);
            if (literalText != null) {
                v.setLength(literalText.length());
            }
        }
        return v;
    }

    boolean isStringyType(AnalysisType dt) {
        if (dt == null) {
            return false;
        }
        return SugNameTables.STRINGY_ALLOC_TYPES.contains(dt.toJavaName(true));
    }

    /** Like {@link #canHoldStringy(AnalysisType)} on a flow's declared type; a null flow
     * or null declared type conservatively holds stringy values. */
    boolean canHoldStringyNullable(TypeFlow<?> flow) {
        return flow == null || canHoldStringy(flow.getDeclaredType());
    }

    boolean canHoldStringy(AnalysisType t) {
        return SugNameTables.canHoldStringy(t);
    }

    private boolean isInternInvoke(InvokeTypeFlow inv) {
        PointsToAnalysisMethod tm = inv.getTargetMethod();
        if (tm == null) {
            return false;
        }
        return tm.getDeclaringClass().toJavaName(true).equals(SugNameTables.STRING_INTERN_SUPPORT_CLASS) && tm.getName().equals("intern");
    }

    private static void initSourcePosition(SugVertex v, TypeFlow<?> flow) {
        String key = SiteKeys.sourceKey(flow.getSource());
        v.setSourceLocation(key != null ? key : SiteKeys.UNKNOWN_KEY);
        v.setSourceKey(key);
    }

    /** Sets a vertex's source location from an IR node's {@link NodeSourcePosition} (vertices without a type flow). */
    private static void initSourcePositionFromNode(SugVertex v, Node node, AnalysisMethod enclosing) {
        NodeSourcePosition pos = node.getNodeSourcePosition();
        if (pos != null) {
            String key = SiteKeys.profileKey(enclosing, pos.getBCI());
            v.setSourceLocation(key);
            v.setSourceKey(key);
        } else {
            v.setSourceLocation(SiteKeys.UNKNOWN_KEY);
        }
    }

    AnalysisType resolveAnalysisType(ResolvedJavaType rjt) {
        if (rjt instanceof AnalysisType at) {
            return at;
        }
        return bb.getUniverse().lookup(rjt);
    }

    AnalysisType resolveAnalysisTypeByName(String qualifiedName) {
        try {
            Class<?> cls = Class.forName(qualifiedName, false, getClass().getClassLoader());
            return bb.getMetaAccess().lookupJavaType(cls);
        } catch (Throwable t) {
            return null;
        }
    }

    static String formatSignature(AnalysisMethod m) {
        return SiteKeys.formatSignature(m);
    }

}
