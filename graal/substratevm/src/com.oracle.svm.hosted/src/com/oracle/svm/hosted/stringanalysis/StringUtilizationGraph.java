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
import java.util.BitSet;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisMethod;

/**
 * The String Utilization Graph (SUG): the data model built by {@code SugBuilderV2} from the
 * points-to type-flow graph (plus the pre-lowering capture side table). Vertices represent string
 * sources, calls, and merge points; edges encode dataflow, qualifier, concat-operand, and JDK
 * relationships. The heuristics traverse this graph to derive representation decisions.
 */
public final class StringUtilizationGraph {

    private final List<SugVertex> vertices = new ArrayList<>();
    private final List<SugEdge> edges = new ArrayList<>();
    private final Map<TypeFlow<?>, SugVertex> flowToVertex = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<String, SugVertex> internedLiterals = new ConcurrentHashMap<>();
    private final Map<SugVertex, Set<SugVertex>> reachabilityCache = new HashMap<>();
    private final AtomicInteger nextId = new AtomicInteger(0);
    private boolean usageSourceBuilt;
    private List<UsageTag> usageTags;
    private List<SourceTag> sourceTags;
    private List<SugVertex> callSiteVertices;
    private List<SugVertex> equalsVerticesForCrossRep;
    private boolean callSiteIndexBuilt;
    /**
     * Type-check IC (child, observation only): per {@code checkcast}/{@code instanceof String} site key, the creation
     * sites (seed vertices) of the STRING atoms whose walk reached the site's {@code InstanceOfNode}
     * ({@link TypeCheckSites}). Never read by a verdict layer.
     */
    private Map<String, Set<SugVertex>> typeCheckObservations = Collections.emptyMap();

    Map<String, Set<SugVertex>> getTypeCheckObservations() {
        return typeCheckObservations;
    }

    void setTypeCheckObservations(Map<String, Set<SugVertex>> obs) {
        this.typeCheckObservations = obs;
    }

    public List<SugVertex> getVertices() {
        return Collections.unmodifiableList(vertices);
    }

    public List<SugEdge> getEdges() {
        return Collections.unmodifiableList(edges);
    }

    public Map<TypeFlow<?>, SugVertex> getFlowToVertex() {
        return Collections.unmodifiableMap(flowToVertex);
    }

    public Map<String, SugVertex> getInternedLiterals() {
        return Collections.unmodifiableMap(internedLiterals);
    }

    Map<String, SugVertex> internedLiterals() {
        return internedLiterals;
    }

    public synchronized SugVertex newVertex() {
        SugVertex v = new SugVertex(nextId.getAndIncrement());
        vertices.add(v);
        return v;
    }

    public void registerFlow(TypeFlow<?> flow, SugVertex vertex) {
        flowToVertex.put(flow, vertex);
    }

    public SugVertex getVertex(TypeFlow<?> flow) {
        return flowToVertex.get(flow);
    }

    public SugEdge addEdge(SugVertex from, SugVertex to, SugEdgeType type, int paramIndex) {
        return addEdge(from, to, type, paramIndex, inferFlowRole(type));
    }

    public SugEdge addEdge(SugVertex from, SugVertex to, SugEdgeType type, int paramIndex, SugEdge.FlowRole flowRole) {
        SugEdge edge = new SugEdge(from, to, type, paramIndex, flowRole);
        from.addOutEdge(edge);
        to.addInEdge(edge);
        edges.add(edge);
        return edge;
    }

    private static SugEdge.FlowRole inferFlowRole(SugEdgeType type) {
        return switch (type) {
            case QUALIFIER -> SugEdge.FlowRole.RECEIVER;
            case PARAMETER -> SugEdge.FlowRole.ARG;
            default -> SugEdge.FlowRole.NONE;
        };
    }

    public Set<SugVertex> forwardReachable(SugVertex start) {
        Set<SugVertex> cached = reachabilityCache.get(start);
        if (cached != null) {
            return cached;
        }
        Set<SugVertex> seen = new HashSet<>();
        Deque<SugVertex> work = new ArrayDeque<>();
        work.add(start);
        seen.add(start);
        while (!work.isEmpty()) {
            SugVertex v = work.removeFirst();
            for (SugEdge e : v.getOutEdges()) {
                SugVertex to = e.getTo();
                if (seen.add(to)) {
                    work.add(to);
                }
            }
        }
        reachabilityCache.put(start, seen);
        return seen;
    }

    public void computeMultiSourceForwardReachability(
                    List<SugVertex> seeds,
                    Map<SugVertex, BitSet> reachingDecisionIndices,
                    List<Set<SugVertex>> reachableByDecision) {
        int n = seeds.size();
        Deque<SugVertex> work = new ArrayDeque<>(n);
        Map<SugVertex, BitSet> pendingDelta = new HashMap<>();
        for (int i = 0; i < n; i++) {
            SugVertex s = seeds.get(i);
            BitSet bs = new BitSet(n);
            bs.set(i);
            reachingDecisionIndices.put(s, bs);
            reachableByDecision.get(i).add(s);
            BitSet delta = new BitSet(n);
            delta.set(i);
            pendingDelta.put(s, delta);
            work.add(s);
        }
        while (!work.isEmpty()) {
            SugVertex v = work.removeFirst();
            BitSet delta = pendingDelta.get(v);
            if (delta == null || delta.isEmpty()) {
                continue;
            }
            pendingDelta.put(v, new BitSet(n));
            for (SugEdge e : v.getOutEdges()) {
                SugVertex w = e.getTo();
                BitSet wTags = reachingDecisionIndices.get(w);
                if (wTags == null) {
                    wTags = new BitSet(n);
                    reachingDecisionIndices.put(w, wTags);
                }
                BitSet added = new BitSet(n);
                for (int i = delta.nextSetBit(0); i >= 0; i = delta.nextSetBit(i + 1)) {
                    if (!wTags.get(i)) {
                        wTags.set(i);
                        added.set(i);
                    }
                }
                if (!added.isEmpty()) {
                    for (int i = added.nextSetBit(0); i >= 0; i = added.nextSetBit(i + 1)) {
                        reachableByDecision.get(i).add(w);
                    }
                    BitSet wDelta = pendingDelta.get(w);
                    if (wDelta == null) {
                        wDelta = new BitSet(n);
                        pendingDelta.put(w, wDelta);
                    }
                    wDelta.or(added);
                    work.add(w);
                }
            }
        }
        for (int i = 0; i < n; i++) {
            reachabilityCache.put(seeds.get(i), reachableByDecision.get(i));
        }
    }

    public Map<SugNodeType, Integer> vertexTypeCounts() {
        Map<SugNodeType, Integer> counts = new LinkedHashMap<>();
        for (SugVertex v : vertices) {
            counts.merge(v.getNodeType(), 1, Integer::sum);
        }
        return counts;
    }

    public String dumpText() {
        StringBuilder sb = new StringBuilder();
        sb.append("===== String Utilization Graph =====\n");
        sb.append("Vertices: ").append(vertices.size()).append("  Edges: ").append(edges.size()).append("\n");

        List<SugVertex> sorted = new ArrayList<>(vertices);
        sorted.sort(Comparator.comparingInt(SugVertex::getId));
        sb.append("--- Vertices ---\n");
        for (SugVertex v : sorted) {
            sb.append("  ").append(v.describe()).append("\n");
        }

        List<SugEdge> sortedEdges = new ArrayList<>(edges);
        sortedEdges.sort(Comparator.<SugEdge> comparingInt(e -> e.getFrom().getId())
                        .thenComparingInt(e -> e.getTo().getId())
                        .thenComparing(e -> e.getEdgeType().name()));
        sb.append("--- Edges ---\n");
        for (SugEdge e : sortedEdges) {
            sb.append("  ").append(e).append("\n");
        }

        sb.append("--- Vertex type counts ---\n");
        Map<SugNodeType, Integer> counts = vertexTypeCounts();
        List<SugNodeType> keys = new ArrayList<>(counts.keySet());
        keys.sort(Comparator.comparing(Enum::name));
        for (SugNodeType t : keys) {
            sb.append("  ").append(t).append(" = ").append(counts.get(t)).append("\n");
        }
        sb.append("===== String Utilization Graph (end) =====");
        return sb.toString();
    }

    public String dumpDot() {
        StringBuilder sb = new StringBuilder();
        sb.append("digraph SUG {\n");
        sb.append("  rankdir=LR;\n");
        List<SugVertex> sorted = new ArrayList<>(vertices);
        sorted.sort(Comparator.comparingInt(SugVertex::getId));
        for (SugVertex v : sorted) {
            sb.append("  v").append(v.getId()).append(" [label=\"")
                            .append(v.getNodeType()).append(" #").append(v.getId());
            if (v.getLabel() != null) {
                sb.append(" \\\"").append(dotEscape(v.getLabel())).append("\\\"");
            }
            if (v.getMethodName() != null) {
                sb.append(" ").append(v.getMethodName());
            }
            sb.append("\"];\n");
        }
        List<SugEdge> sortedEdges = new ArrayList<>(edges);
        sortedEdges.sort(Comparator.<SugEdge> comparingInt(e -> e.getFrom().getId())
                        .thenComparingInt(e -> e.getTo().getId()));
        for (SugEdge e : sortedEdges) {
            sb.append("  v").append(e.getFrom().getId()).append(" -> v").append(e.getTo().getId())
                            .append(" [label=\"").append(e.getEdgeType());
            if (e.getEdgeType() == SugEdgeType.PARAMETER) {
                sb.append("[").append(e.getParamIndex()).append("]");
            }
            sb.append("\"];\n");
        }
        sb.append("}\n");
        return sb.toString();
    }

    private static String dotEscape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                default -> sb.append(c);
            }
        }
        return sb.toString();
    }

    public List<SugVertex> verticesForEnclosingClass(String classToken) {
        List<SugVertex> out = new ArrayList<>();
        for (SugVertex v : vertices) {
            AnalysisMethod m = v.getEnclosingMethod();
            if (m != null && m.getDeclaringClass().toJavaName(true).contains(classToken)) {
                out.add(v);
            }
        }
        out.sort(Comparator.comparingInt(SugVertex::getId));
        return out;
    }

    public String dumpTextFiltered(String enclosingClassToken) {
        StringBuilder sb = new StringBuilder();
        sb.append("===== String Utilization Graph (filtered: ").append(enclosingClassToken).append(") =====\n");
        Set<SugVertex> keep = new HashSet<>(verticesForEnclosingClass(enclosingClassToken));
        List<SugVertex> sorted = new ArrayList<>(keep);
        sorted.sort(Comparator.comparingInt(SugVertex::getId));
        sb.append("--- Vertices (").append(keep.size()).append(") ---\n");
        for (SugVertex v : sorted) {
            sb.append("  ").append(v.describe()).append("\n");
        }
        sb.append("--- Edges ---\n");
        int edgeCount = 0;
        for (SugEdge e : edges) {
            if (keep.contains(e.getFrom()) && keep.contains(e.getTo())) {
                sb.append("  ").append(e).append("\n");
                edgeCount++;
            }
        }
        sb.append("--- edges shown: ").append(edgeCount).append(" ---\n");
        sb.append("--- Vertex type counts ---\n");
        Map<SugNodeType, Integer> counts = new LinkedHashMap<>();
        for (SugVertex v : keep) {
            counts.merge(v.getNodeType(), 1, Integer::sum);
        }
        List<SugNodeType> keys = new ArrayList<>(counts.keySet());
        keys.sort(Comparator.comparing(Enum::name));
        for (SugNodeType t : keys) {
            sb.append("  ").append(t).append(" = ").append(counts.get(t)).append("\n");
        }
        sb.append("===== String Utilization Graph (end) =====");
        return sb.toString();
    }

    public Map<SugVertex, Set<SugVertex>> computeReachabilityFromAll() {
        Map<SugVertex, Set<SugVertex>> all = new HashMap<>();
        for (SugVertex v : vertices) {
            all.put(v, forwardReachable(v));
        }
        return Collections.unmodifiableMap(all);
    }

    public Map<SugVertex, Set<SugVertex>> getReachabilityCache() {
        return Collections.unmodifiableMap(reachabilityCache);
    }

    /**
     * Clears the {@link #reachabilityCache}: the cache has no invalidation, so the builder clears it after Phase B/C
     * edge-building and before any heuristic {@code forwardReachable} call.
     */
    public void clearReachabilityCache() {
        reachabilityCache.clear();
    }

    public boolean isUsageSourceBuilt() {
        return usageSourceBuilt;
    }

    /**
     * Accumulator pass 2: the seeded builder extractions, each with the ACC seed vertices its receiver provably comes
     * from (the receiver proof in {@code ForwardFixpoint.accPass2}); read by
     * {@link AccumulatorHeuristic}.
     */
    private final Map<SugVertex, Set<SugVertex>> accExtractionReceivers = new java.util.LinkedHashMap<>();
    /** Accumulator pass 2: extractions of pass-1 accumulators that were not seeded, with the reason (print-only). */
    private final Map<SugVertex, String> accExtractionUnseeded = new java.util.LinkedHashMap<>();

    Map<SugVertex, Set<SugVertex>> accExtractionReceivers() {
        return accExtractionReceivers;
    }

    Map<SugVertex, String> accExtractionUnseeded() {
        return accExtractionUnseeded;
    }

    /** The seeded element-source calls ({@link ElementSources}), in seed order. */
    private final Set<SugVertex> elemSources = new java.util.LinkedHashSet<>();

    Set<SugVertex> elemSources() {
        return elemSources;
    }

    public void setUsageSourceBuilt() {
        usageSourceBuilt = true;
    }

    public void setUsageTags(List<UsageTag> tags) {
        this.usageTags = tags;
    }

    public List<UsageTag> getUsageTags() {
        return usageTags;
    }

    public void setSourceTags(List<SourceTag> tags) {
        this.sourceTags = tags;
    }

    public UsageTag getUsageTag(int index) {
        return usageTags.get(index);
    }

    public SourceTag getSourceTag(int index) {
        return sourceTags.get(index);
    }

    public List<SugVertex> getCallSiteVertices() {
        ensureCallSiteIndexBuilt();
        return Collections.unmodifiableList(callSiteVertices);
    }

    public List<SugVertex> getEqualsVerticesForCrossRep() {
        ensureCallSiteIndexBuilt();
        return Collections.unmodifiableList(equalsVerticesForCrossRep);
    }

    private void ensureCallSiteIndexBuilt() {
        if (callSiteIndexBuilt) {
            return;
        }
        List<SugVertex> cs = new ArrayList<>();
        List<SugVertex> eq = new ArrayList<>();
        for (SugVertex v : vertices) {
            SugNodeType t = v.getNodeType();
            if (t == SugNodeType.STRING_METHOD_CALL || t == SugNodeType.JDK_LIBRARY_CALL) {
                cs.add(v);
                if ("equals".equals(v.getMethodName()) || "compareTo".equals(v.getMethodName())) {
                    eq.add(v); // compareTo sites too (the cross-rep compareTo conflict, HeuristicOrchestrator)
                }
            }
        }
        callSiteVertices = cs;
        equalsVerticesForCrossRep = eq;
        callSiteIndexBuilt = true;
    }

    public void removeVertex(SugVertex v) {
        vertices.remove(v);
        flowToVertex.values().remove(v);
        internedLiterals.values().remove(v);
        reachabilityCache.remove(v);
        reachabilityCache.values().remove(v);
    }

    public void removeEdge(SugEdge e) {
        edges.remove(e);
    }

    /** Removes all vertices in {@code removed} (and their edges) in a single O(V+E) pass (Phase C mark-and-sweep). */
    public void bulkRemove(Set<SugVertex> removed) {
        if (removed.isEmpty()) {
            return;
        }
        vertices.removeIf(removed::contains);
        edges.removeIf(e -> removed.contains(e.getFrom()) || removed.contains(e.getTo()));
        flowToVertex.entrySet().removeIf(e -> removed.contains(e.getValue()));
        internedLiterals.entrySet().removeIf(e -> removed.contains(e.getValue()));
        reachabilityCache.clear();
        callSiteVertices = null;
        equalsVerticesForCrossRep = null;
        callSiteIndexBuilt = false;
    }

    public String dumpLengthSummary(String enclosingClassToken) {
        Set<SugVertex> keep = new HashSet<>(verticesForEnclosingClass(enclosingClassToken));
        List<SugVertex> withLength = new ArrayList<>();
        List<SugVertex> noLength = new ArrayList<>();
        for (SugVertex v : keep) {
            if (v.getLength() != SugVertex.UNKNOWN_LENGTH) {
                withLength.add(v);
            } else {
                noLength.add(v);
            }
        }
        withLength.sort(Comparator.comparingInt(SugVertex::getId));
        noLength.sort(Comparator.comparingInt(SugVertex::getId));
        StringBuilder sb = new StringBuilder();
        sb.append("--- Length summary (filtered: ").append(enclosingClassToken).append(") ---\n");
        sb.append("  with length (").append(withLength.size()).append("):\n");
        for (SugVertex v : withLength) {
            sb.append("    V").append(v.getId()).append(" ").append(v.getNodeType());
            if (v.getMethodName() != null) {
                sb.append(" ").append(v.getMethodName());
            }
            if (v.getLiteralText() != null) {
                sb.append(" \"").append(v.getLiteralText().replace("\n", "\\n")).append("\"");
            }
            sb.append(" length=").append(v.getLength()).append("\n");
        }
        sb.append("  without length (").append(noLength.size()).append("):\n");
        for (SugVertex v : noLength) {
            sb.append("    V").append(v.getId()).append(" ").append(v.getNodeType());
            if (v.getMethodName() != null) {
                sb.append(" ").append(v.getMethodName());
            }
            sb.append(" @ ").append(v.getSourceLocation()).append("\n");
        }
        return sb.toString().stripTrailing();
    }

    public String dumpDotFiltered(String enclosingClassToken) {
        Set<SugVertex> keep = new HashSet<>(verticesForEnclosingClass(enclosingClassToken));
        StringBuilder sb = new StringBuilder();
        sb.append("digraph SUG_filtered {\n");
        sb.append("  rankdir=LR;\n");
        List<SugVertex> sorted = new ArrayList<>(keep);
        sorted.sort(Comparator.comparingInt(SugVertex::getId));
        for (SugVertex v : sorted) {
            sb.append("  v").append(v.getId()).append(" [label=\"")
                            .append(v.getNodeType()).append(" #").append(v.getId());
            if (v.getLiteralText() != null) {
                sb.append(" \\\"").append(dotEscape(v.getLiteralText())).append("\\\" len=").append(v.getLiteralText().length());
            }
            if (v.getMethodName() != null) {
                sb.append(" ").append(v.getMethodName());
            }
            if (v.getConstantValue() != 0 || v.getNodeType() == SugNodeType.CONSTANT_ARG) {
                sb.append(" const=").append(v.getConstantValue());
            }
            sb.append("\"];\n");
        }
        List<SugEdge> sortedEdges = new ArrayList<>();
        for (SugEdge e : edges) {
            if (keep.contains(e.getFrom()) && keep.contains(e.getTo())) {
                sortedEdges.add(e);
            }
        }
        sortedEdges.sort(Comparator.<SugEdge> comparingInt(e -> e.getFrom().getId())
                        .thenComparingInt(e -> e.getTo().getId()));
        for (SugEdge e : sortedEdges) {
            sb.append("  v").append(e.getFrom().getId()).append(" -> v").append(e.getTo().getId())
                            .append(" [label=\"").append(e.getEdgeType());
            if (e.getEdgeType() == SugEdgeType.PARAMETER) {
                sb.append("[").append(e.getParamIndex()).append("]");
            }
            sb.append("\"];\n");
        }
        sb.append("}\n");
        return sb.toString();
    }
}
