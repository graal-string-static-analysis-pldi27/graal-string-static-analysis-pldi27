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

import org.junit.Assert;
import org.junit.Test;

public class LengthPropagationTest {

    @Test
    public void e1LiteralLengthFromLiteralText() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex comma = graph.newVertex();
        comma.setNodeType(SugNodeType.STRING_LITERAL);
        comma.setLiteralText(",,");
        SugVertex x = graph.newVertex();
        x.setNodeType(SugNodeType.STRING_LITERAL);
        x.setLiteralText("x");

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(2, comma.getLength());
        Assert.assertEquals(1, x.getLength());
        Assert.assertEquals(2, propagator.getE1Count());
        Assert.assertEquals(0, propagator.getE2Count());
        Assert.assertEquals(0, propagator.getE4Count());
        Assert.assertEquals(0, propagator.getConflictCount());
    }

    @Test
    public void e2SubstringLengthFromTwoConstantArgs() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("Sub.java:1");
        SugVertex begin = graph.newVertex();
        begin.setNodeType(SugNodeType.CONSTANT_ARG);
        begin.setConstantValue(1L);
        SugVertex end = graph.newVertex();
        end.setNodeType(SugNodeType.CONSTANT_ARG);
        end.setConstantValue(4L);
        graph.addEdge(begin, sub, SugEdgeType.PARAMETER, 0);
        graph.addEdge(end, sub, SugEdgeType.PARAMETER, 1);

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(3, sub.getLength());
        Assert.assertEquals(1, propagator.getE2Count());
        Assert.assertEquals(0, propagator.getE1Count());
    }

    @Test
    public void e4ForwardThroughLengthPreservingCallBlockedAtConcat() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("abc");
        SugVertex upper = graph.newVertex();
        upper.setNodeType(SugNodeType.STRING_METHOD_CALL);
        upper.setMethodName("toUpperCase");
        upper.setDeclaringClass("java.lang.String");
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        graph.addEdge(lit, upper, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(lit, concat, SugEdgeType.DATAFLOW, 0);

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(3, lit.getLength());
        Assert.assertEquals(3, upper.getLength());
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, concat.getLength());
        Assert.assertEquals(1, propagator.getE4Count());
        Assert.assertEquals(0, propagator.getConflictCount());
    }

    @Test
    public void e4BlockedAtNonLengthPreservingCall() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("abcde");
        SugVertex trim = graph.newVertex();
        trim.setNodeType(SugNodeType.STRING_METHOD_CALL);
        trim.setMethodName("trim");
        trim.setDeclaringClass("java.lang.String");
        SugVertex downstream = graph.newVertex();
        downstream.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(lit, trim, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(trim, downstream, SugEdgeType.DATAFLOW, 0);

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(5, lit.getLength());
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, trim.getLength());
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, downstream.getLength());
        Assert.assertEquals(0, propagator.getE4Count());
        Assert.assertEquals(0, propagator.getConflictCount());
    }

    @Test
    public void e5ConflictResetsToUnknownAndCascadesDownstream() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex l1 = graph.newVertex();
        l1.setNodeType(SugNodeType.STRING_LITERAL);
        l1.setLiteralText("ab");
        SugVertex l2 = graph.newVertex();
        l2.setNodeType(SugNodeType.STRING_LITERAL);
        l2.setLiteralText("123456789");
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.VARIABLE);
        v.setSourceLocation("V.java:1");
        SugVertex w = graph.newVertex();
        w.setNodeType(SugNodeType.VARIABLE);
        SugVertex p = graph.newVertex();
        p.setNodeType(SugNodeType.VARIABLE);
        SugVertex q = graph.newVertex();
        q.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(l1, v, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(v, w, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(l2, p, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(p, q, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(q, v, SugEdgeType.DATAFLOW, 0);

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, v.getLength());
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, w.getLength());
        Assert.assertEquals(1, propagator.getConflictCount());
    }

    @Test
    public void e3UnitRangeSetsLengthOneBySourceKey() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("Sub.java:10");
        sub.setSourceKey("pkg.Sub#main([Ljava/lang/String;)V@42");

        LengthPropagator propagator = new LengthPropagator(graph);
        boolean assigned = propagator.assignUnitRange("pkg.Sub#main([Ljava/lang/String;)V@42", "Sub.java:10");
        propagator.propagate();

        Assert.assertTrue(assigned);
        Assert.assertEquals(1, sub.getLength());
        Assert.assertEquals(1, propagator.getE3Count());
    }

    @Test
    public void e3UnitRangeNoMatchLeavesLengthUnknown() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("Sub.java:10");
        sub.setSourceKey("pkg.Sub#main([Ljava/lang/String;)V@42");

        LengthPropagator propagator = new LengthPropagator(graph);
        boolean assigned = propagator.assignUnitRange("pkg.Other#run()V@99", "Other.java:1");
        propagator.propagate();

        Assert.assertFalse(assigned);
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, sub.getLength());
        Assert.assertEquals(0, propagator.getE3Count());
    }

    @Test
    public void e3UnitRangeFallbackBySourceLocation() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("Sub.java:10");

        LengthPropagator propagator = new LengthPropagator(graph);
        boolean assigned = propagator.assignUnitRange("nonexistent-key", "Sub.java:10");
        propagator.propagate();

        Assert.assertTrue(assigned);
        Assert.assertEquals(1, sub.getLength());
        Assert.assertEquals(1, propagator.getE3Count());
    }

    @Test
    public void e3UnitRangeAmbiguousLocationDoesNotAssign() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub1 = graph.newVertex();
        sub1.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub1.setMethodName("substring");
        sub1.setDeclaringClass("java.lang.String");
        sub1.setSourceLocation("Sub.java:10");
        SugVertex sub2 = graph.newVertex();
        sub2.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub2.setMethodName("substring");
        sub2.setDeclaringClass("java.lang.String");
        sub2.setSourceLocation("Sub.java:10");

        LengthPropagator propagator = new LengthPropagator(graph);
        boolean assigned = propagator.assignUnitRange(null, "Sub.java:10");
        propagator.propagate();

        Assert.assertFalse(assigned);
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, sub1.getLength());
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, sub2.getLength());
        Assert.assertEquals(0, propagator.getE3Count());
    }

    /**
     * A unit-range substring with no downstream proof (no usage facts, no safe-sink evidence, no wired-heap path) ADMITs
     * with the no-usage warning. The
     * length assignment itself is unchanged (length=1 asserted). The positive-proof admit variant is pinned by
     * {@code SingleByteHeuristicTest.substringWithUsageFactAccepted}.
     */
    @Test
    public void e3UnitRangeThenSingleByteAdmitsWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("Sub.java:10");
        sub.setSourceKey("pkg.Sub#main([Ljava/lang/String;)V@42");
        sub.setEnclosingClassName("TestUserClass");

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.assignUnitRange("pkg.Sub#main([Ljava/lang/String;)V@42", "Sub.java:10");
        propagator.propagate();

        Assert.assertEquals(1, sub.getLength());
        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        java.util.List<InstrumentationDecision> decisions = heuristic.apply(graph);
        // no proof: ADMIT with the warning; length=1 still asserted
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, sub));
    }

    @Test
    public void e2ValueOfCharAssignsLength1() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("char");
        voc.setDeclaringClass("java.lang.String");
        voc.setSourceLocation("Voc.java:1");
        voc.setEnclosingClassName("TestUserClass");

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(1, voc.getLength());
        Assert.assertEquals(1, propagator.getE2Count());
    }

    @Test
    public void e2ValueOfIntDoesNotAssign() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("int");
        voc.setDeclaringClass("java.lang.String");
        voc.setSourceLocation("Voc.java:1");
        voc.setEnclosingClassName("TestUserClass");

        LengthPropagator propagator = new LengthPropagator(graph);
        propagator.propagate();

        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, voc.getLength());
        Assert.assertEquals(0, propagator.getE2Count());
    }
}
