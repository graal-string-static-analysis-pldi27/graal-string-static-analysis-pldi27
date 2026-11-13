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

public class SingleByteHeuristicTest {

    /**
     * A length-1 substring with no usage facts, no safe-sink evidence and NO wired-heap path has no positive
     * downstream proof (PDP). It admits with the dev-time warning. The no-proof
     * predicate holds.
     */
    @Test
    public void substringWithoutDownstreamProofRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the no-usage length-1 substring ADMITs with the dev-time warning; the no-proof predicate
        // holds.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertTrue(AdmissionProof.hasNoUsage(sub));
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, sub));
    }

    /**
     * A length-1 substring carrying a RECEIVER/NONE-role usage fact (here a NONE-role DATAFLOW tag at a length call) has
     * positive downstream proof: ADMIT (the usage-validated shape).
     */
    @Test
    public void substringWithUsageFactAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setEnclosingClassName("TestUserClass");

        SugVertex lengthCall = graph.newVertex();
        lengthCall.setNodeType(SugNodeType.STRING_METHOD_CALL);
        lengthCall.setMethodName("length");
        lengthCall.setDeclaringClass("java.lang.String");
        lengthCall.setEnclosingClassName("TestUserClass");
        graph.addEdge(sub, lengthCall, SugEdgeType.DATAFLOW, 0);

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, decisions.get(0).getType());
        Assert.assertSame(sub, decisions.get(0).getCandidate());
    }

    @Test
    public void literalAloneRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("x");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertFalse(heuristic.getRejections().isEmpty());
    }

    /**
     * The substring's only usage tag is PARAMETER-role at {@code equals} (not a safe sink): under the uniform PDP rule
     * this is not positive downstream proof (a PARAMETER tag at a non-safe-sink is an argument pass-through, not
     * terminal evidence). The literal (whose tag is NONE-role at the same equals site) ADMITS; the substring ADMITS
     * through the no-usage warning.
     */
    @Test
    public void literalAndSubstringInteractingBothAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("x");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setEnclosingClassName("TestUserClass");

        SugVertex call = graph.newVertex();
        call.setNodeType(SugNodeType.STRING_METHOD_CALL);
        call.setMethodName("equals");
        call.setDeclaringClass("java.lang.String");
        call.setEnclosingClassName("TestUserClass");

        graph.addEdge(lit, call, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, call, SugEdgeType.PARAMETER, 1);

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // both admit — the literal through the interaction rule (its NONE-role tag at the equals; through
        // the SB literal seed also the seeded path's PDP) and the substring through the no-usage default (a non-terminal
        // PARAMETER is not PDP). The equals-argument terminal admits it without a warning.
        Assert.assertEquals(2, decisions.size());
        Assert.assertTrue(heuristic.getRejections().stream().noneMatch(r -> r.contains("no positive proof")));
        Assert.assertTrue(decisions.stream().anyMatch(d -> d.getCandidate() == lit));
        Assert.assertTrue(decisions.stream().anyMatch(d -> d.getCandidate() == sub));
    }

    @Test
    public void literalNotInteractingWithSubstringRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("x");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setEnclosingClassName("TestUserClass");

        SugVertex litCall = graph.newVertex();
        litCall.setNodeType(SugNodeType.STRING_METHOD_CALL);
        litCall.setMethodName("charAt");
        litCall.setDeclaringClass("java.lang.String");
        litCall.setEnclosingClassName("TestUserClass");

        SugVertex subCall = graph.newVertex();
        subCall.setNodeType(SugNodeType.STRING_METHOD_CALL);
        subCall.setMethodName("charAt");
        subCall.setDeclaringClass("java.lang.String");
        subCall.setEnclosingClassName("TestUserClass");

        graph.addEdge(lit, litCall, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, subCall, SugEdgeType.DATAFLOW, 0);

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertSame(sub, decisions.get(0).getCandidate());
        Assert.assertFalse(heuristic.getRejections().isEmpty());
    }

    @Test
    public void multiCharLiteralNotAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("abc");
        lit.setLength(3);
        lit.setEnclosingClassName("TestUserClass");

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    @Test
    public void lengthOneNonSubstringCallNotAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex call = graph.newVertex();
        call.setNodeType(SugNodeType.STRING_METHOD_CALL);
        call.setMethodName("toUpperCase");
        call.setDeclaringClass("java.lang.String");
        call.setLength(1);
        call.setEnclosingClassName("TestUserClass");

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    @Test
    public void incompleteNonCandidateIsNotReportedAsRejectedCandidate() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex variable = graph.newVertex();
        variable.setNodeType(SugNodeType.VARIABLE);
        variable.setLength(1);
        variable.setEnclosingClassName("TestUserClass");
        variable.markIncompleteTrace();
        variable.markResourceLimitedTrace();

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void internalClassCandidateSkipped() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setEnclosingClassName("java.lang.String");

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    @Test
    public void nullEnclosingCandidateSkipped() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    @Test
    public void rejectionsListPopulatedForRejectedLiterals() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("a");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SugVertex lit2 = graph.newVertex();
        lit2.setNodeType(SugNodeType.STRING_LITERAL);
        lit2.setLiteralText("b");
        lit2.setLength(1);
        lit2.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        heuristic.apply(graph);

        Assert.assertEquals(2, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("REJECT"));
    }

    /**
     * valueOf(char) with no downstream proof admits with the no-usage warning.
     */
    @Test
    public void valueOfCharAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("char");
        voc.setDeclaringClass("java.lang.String");
        voc.setLength(1);
        voc.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the valueOf(char) candidate with no downstream proof ADMITs with the warning.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, voc));
    }

    @Test
    public void valueOfIntNotAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("int");
        voc.setDeclaringClass("java.lang.String");
        voc.setLength(1);
        voc.setEnclosingClassName("TestUserClass");

        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    /**
     * The valueOf(char) candidate's only tag is PARAMETER-role at equals
     * (not a safe sink): no PDP; the literal (NONE-role tag at the same equals) has PDP.
     * Both admit: the literal through the interaction rule (through the SB literal seed, also the seeded path), the voc
     * through the no-usage warning.
     */
    @Test
    public void valueOfCharAndLiteralInteracting() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("A");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("char");
        voc.setDeclaringClass("java.lang.String");
        voc.setLength(1);
        voc.setEnclosingClassName("TestUserClass");

        SugVertex call = graph.newVertex();
        call.setNodeType(SugNodeType.STRING_METHOD_CALL);
        call.setMethodName("equals");
        call.setDeclaringClass("java.lang.String");
        call.setEnclosingClassName("TestUserClass");

        graph.addEdge(lit, call, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(voc, call, SugEdgeType.PARAMETER, 1);

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(2, decisions.size());
        Assert.assertTrue(heuristic.getRejections().stream().noneMatch(r -> r.contains("no positive proof")));
        Assert.assertTrue(decisions.stream().anyMatch(d -> d.getCandidate() == lit));
        Assert.assertTrue(decisions.stream().anyMatch(d -> d.getCandidate() == voc));
    }

    /**
     * valueOf(char) without a source flow is a dynamic-substring-class candidate; with no downstream proof it admits

     * with the no-usage warning.
     */
    @Test
    public void valueOfCharWithoutSourceFlowTreatedAsDynamicSubstring() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("char");
        voc.setDeclaringClass("java.lang.String");
        voc.setLength(1);
        voc.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the valueOf(char) dynamic-substring-class candidate with no proof ADMITs with the
        // warning.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
    }

    /**
     * The valueOf(char) dynamic candidate admits at the no-usage default, and the seeded literal still rejects: a literal with no usage has no
     * positive downstream proof, so it must not admit on the interaction rule alone.
     */
    @Test
    public void valueOfCharWithoutSourceFlowDoesNotBlockLiteral() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("A");
        lit.setLength(1);
        lit.setEnclosingClassName("TestUserClass");

        SugVertex voc = graph.newVertex();
        voc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        voc.setMethodName("valueOf");
        voc.setMethodSignature("char");
        voc.setDeclaringClass("java.lang.String");
        voc.setLength(1);
        voc.setEnclosingClassName("TestUserClass");

        SingleByteHeuristic heuristic = new SingleByteHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);
        // the voc ADMITs at the no-usage default (with the warning); the literal REJECTs.
        Assert.assertEquals(1, decisions.size());
        Assert.assertSame(voc, decisions.get(0).getCandidate());
        Assert.assertTrue("the literal must not admit",
                        heuristic.getRejections().stream().anyMatch(r -> r.contains("lost downstream trace")));
        Assert.assertEquals(1, heuristic.getWarnings().size());
    }
}
