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

import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/** The SUG-edge path ({@code new AccumulatorHeuristic(false)}); the two-pass path: {@link AccumulatorDecisionTableTest}. */
public class AccumulatorHeuristicTest {

    private static SugVertex newAccumulator(StringUtilizationGraph graph, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.NEW_ACCUMULATOR);
        v.setDeclaringClass("java.lang.StringBuilder");
        v.setSourceLocation(loc);
        v.setEnclosingClassName("TestUserClass");
        return v;
    }

    private static SugVertex accumulatorCall(StringUtilizationGraph graph, String name, String sig, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        v.setDeclaringClass("java.lang.StringBuilder");
        v.setSourceLocation(loc);
        return v;
    }

    private static SugVertex stringCall(StringUtilizationGraph graph, String name, String sig, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        return v;
    }

    @Test
    public void accumulatorWithExtractionAndWhitelistedDownstreamAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:2");
        SugVertex result = graph.newVertex();
        result.setNodeType(SugNodeType.VARIABLE);
        SugVertex length = stringCall(graph, "length", "", "A.java:3");
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(result, length, SugEdgeType.DATAFLOW, 0);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, heuristic.getCandidateCount());
        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertEquals("ACCUMULATOR_VIEW", decisions.get(0).getVariant());
        Assert.assertSame(toString, decisions.get(0).getCandidate());
        // no backward receiver proof on this path, so no trusted exact class (the parent declines)
        Assert.assertNull(decisions.get(0).getAccumulatorClass());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void accumulatorWithoutExtractionCallRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex append = accumulatorCall(graph, "append", "Ljava/lang/String;", "A.java:2");
        SugVertex charAt = accumulatorCall(graph, "charAt", "I", "A.java:3");
        graph.addEdge(acc, append, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(acc, charAt, SugEdgeType.QUALIFIER, 0);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        String rejection = heuristic.getRejections().get(0);
        Assert.assertTrue(rejection.contains("extraction"));
    }

    @Test
    public void visibleInsertOpRejectsAccumulator() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex insert = accumulatorCall(graph, "insert", "IC", "A.java:2");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:3");
        SugVertex result = graph.newVertex();
        result.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(acc, insert, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, 0);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("insert"));
    }

    @Test
    public void appendOpsVisibleDoNotFalselyReject() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex append1 = accumulatorCall(graph, "append", "Ljava/lang/String;", "A.java:2");
        SugVertex append2 = accumulatorCall(graph, "append", "Ljava/lang/String;", "A.java:3");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:4");
        SugVertex result = graph.newVertex();
        result.setNodeType(SugNodeType.VARIABLE);
        SugVertex length = stringCall(graph, "length", "", "A.java:5");
        graph.addEdge(acc, append1, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(acc, append2, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(result, length, SugEdgeType.DATAFLOW, 0);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, heuristic.getCandidateCount());
        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertEquals("ACCUMULATOR_VIEW", decisions.get(0).getVariant());
        Assert.assertSame(toString, decisions.get(0).getCandidate());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void internOnExtractedStringRejectsAccumulator() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:2");
        SugVertex result = graph.newVertex();
        result.setNodeType(SugNodeType.VARIABLE);
        SugVertex intern = stringCall(graph, "intern", "Ljava/lang/String;", "A.java:3");
        intern.setLabel("String.intern");
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(result, intern, SugEdgeType.QUALIFIER, -1);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("intern"));
    }

    @Test
    public void internalClassAccumulatorCandidateSkipped() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = graph.newVertex();
        acc.setNodeType(SugNodeType.NEW_ACCUMULATOR);
        acc.setDeclaringClass("java.lang.StringBuilder");
        acc.setSourceLocation("A.java:1");
        acc.setEnclosingClassName("java.lang.AbstractStringBuilder");

        List<InstrumentationDecision> decisions = new AccumulatorHeuristic(false).apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    /**
     * An extraction whose downstream is a complete trace over non-call vertices with no usage facts: ADMIT with the
     * no-usage warning.
     */
    @Test
    public void extractionWithCompleteTraceButNoUsagesAdmittedWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:2");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        SugVertex variable = graph.newVertex();
        variable.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, passthrough, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(passthrough, variable, SugEdgeType.DATAFLOW, 0);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the no-usage extraction ADMITs with the dev-time warning; the
        // no-proof predicate pin still holds (the extraction `toString`, not the accumulator: the accumulator's own
        // toString QUALIFIER usage is a RECEIVER-role proof).
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, toString));
    }

    /** The same no-proof shape with the wired-any-load bit set on the extraction: ADMIT (the heap-reaching proof). */

    @Test
    public void extractionWithWiredHeapPathAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph, "A.java:1");
        SugVertex toString = accumulatorCall(graph, "toString", null, "A.java:2");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        SugVertex variable = graph.newVertex();
        variable.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, 0);
        graph.addEdge(toString, passthrough, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(passthrough, variable, SugEdgeType.DATAFLOW, 0);
        toString.markWiredAnyLoad();

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertEquals("ACCUMULATOR_VIEW", decisions.get(0).getVariant());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }
}
