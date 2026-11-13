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

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

public class HeuristicOrchestratorTest {

    @Test
    public void precedenceSingleByteOverStringViewOnSharedSubstring() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(1);
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("TestUserClass");
        SugVertex length = graph.newVertex();
        length.setNodeType(SugNodeType.STRING_METHOD_CALL);
        length.setMethodName("length");
        length.setMethodSignature("");
        length.setDeclaringClass("java.lang.String");
        length.setSourceLocation("S.java:2");
        graph.addEdge(sub, length, SugEdgeType.DATAFLOW, 0);

        List<InstrumentationDecision> singleByte = new SingleByteHeuristic().apply(graph);
        List<InstrumentationDecision> stringView = new StringViewHeuristic().apply(graph);

        Assert.assertEquals(1, singleByte.size());
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, singleByte.get(0).getType());
        Assert.assertEquals(1, stringView.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, stringView.get(0).getType());

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(singleByte, stringView, Collections.emptyList(), Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, orchestrator.getValidatedDecisions().get(0).getType());
        Assert.assertEquals(1, orchestrator.getPrecedenceSuppressed().size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, orchestrator.getPrecedenceSuppressed().get(0).getType());
        Assert.assertTrue(orchestrator.getConflicts().isEmpty());
    }

    @Test
    public void singleRepresentationValidationAllowsRepsAtDistinctCallSites() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("k");
        lit.setLength(1);
        lit.setSourceLocation("L.java:1");
        lit.setEnclosingClassName("TestUserClass");
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(5);
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("TestUserClass");
        SugVertex shared = graph.newVertex();
        shared.setNodeType(SugNodeType.VARIABLE);
        shared.setSourceLocation("M.java:1");
        graph.addEdge(lit, shared, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, shared, SugEdgeType.DATAFLOW, 0);

        SugVertex subByte = graph.newVertex();
        subByte.setNodeType(SugNodeType.STRING_METHOD_CALL);
        subByte.setMethodName("substring");
        subByte.setDeclaringClass("java.lang.String");
        subByte.setLength(1);
        subByte.setSourceLocation("SB.java:1");
        subByte.setEnclosingClassName("TestUserClass");
        graph.addEdge(subByte, shared, SugEdgeType.DATAFLOW, 0);

        SugVertex svUsage = graph.newVertex();
        svUsage.setNodeType(SugNodeType.STRING_METHOD_CALL);
        svUsage.setMethodName("charAt");
        svUsage.setDeclaringClass("java.lang.String");
        svUsage.setMethodSignature("I");
        svUsage.setSourceLocation("U1.java:1");
        graph.addEdge(sub, svUsage, SugEdgeType.DATAFLOW, 0);

        SugVertex sbUsage = graph.newVertex();
        sbUsage.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sbUsage.setMethodName("charAt");
        sbUsage.setDeclaringClass("java.lang.String");
        sbUsage.setMethodSignature("I");
        sbUsage.setSourceLocation("U2.java:1");
        graph.addEdge(subByte, sbUsage, SugEdgeType.DATAFLOW, 0);

        SugVertex sbEquals = graph.newVertex();
        sbEquals.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sbEquals.setMethodName("equals");
        sbEquals.setDeclaringClass("java.lang.String");
        sbEquals.setSourceLocation("E1.java:1");
        graph.addEdge(lit, sbEquals, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(subByte, sbEquals, SugEdgeType.PARAMETER, 1);

        List<InstrumentationDecision> singleByte = new SingleByteHeuristic().apply(graph);
        List<InstrumentationDecision> stringView = new StringViewHeuristic().apply(graph);

        Assert.assertEquals(2, singleByte.size());
        Assert.assertEquals(2, stringView.size());

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(singleByte, stringView, Collections.emptyList(), Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(3, orchestrator.getValidatedDecisions().size());
        Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
        Assert.assertTrue(orchestrator.getConflicts().isEmpty());
    }

    @Test
    public void conflictBetweenStringViewAndLazyConcatAtVariableAllowed() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(5);
        sub.setSourceLocation("SV.java:1");
        sub.setEnclosingClassName("TestUserClass");
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setLength(10);
        concat.setSourceLocation("LC.java:1");
        concat.setEnclosingClassName("TestUserClass");
        SugVertex shared = graph.newVertex();
        shared.setNodeType(SugNodeType.VARIABLE);
        shared.setSourceLocation("M.java:1");
        graph.addEdge(sub, shared, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(concat, shared, SugEdgeType.DATAFLOW, 0);

        List<InstrumentationDecision> stringView = List.of(new InstrumentationDecision(sub, OptimizationType.STRING_VIEW, null));
        List<InstrumentationDecision> lazyConcat = List.of(new InstrumentationDecision(concat, OptimizationType.LAZY_CONCAT, "ROPE"));

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Collections.emptyList(), stringView, lazyConcat, Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(2, orchestrator.getValidatedDecisions().size());
        Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
        Assert.assertTrue(orchestrator.getConflicts().isEmpty());
    }

    @Test
    public void threeReceiverRepsAtCallSiteAllSurvive() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("k");
        lit.setLength(1);
        lit.setSourceLocation("L.java:1");
        lit.setEnclosingClassName("TestUserClass");

        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(5);
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("TestUserClass");

        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setLength(10);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");

        SugVertex callSite = graph.newVertex();
        callSite.setNodeType(SugNodeType.STRING_METHOD_CALL);
        callSite.setMethodName("charAt");
        callSite.setDeclaringClass("java.lang.String");
        callSite.setMethodSignature("I");
        callSite.setSourceLocation("U.java:1");

        graph.addEdge(lit, callSite, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, callSite, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(concat, callSite, SugEdgeType.DATAFLOW, 0);

        InstrumentationDecision sbDec = new InstrumentationDecision(lit, OptimizationType.SINGLE_BYTE, null);
        InstrumentationDecision svDec = new InstrumentationDecision(sub, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision ropeDec = new InstrumentationDecision(concat, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Arrays.asList(sbDec), Arrays.asList(svDec), Arrays.asList(ropeDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(3, orchestrator.getValidatedDecisions().size());
        Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
        Assert.assertTrue(orchestrator.getConflicts().isEmpty());
    }

    @Test
    public void fourReceiverRepsAtCallSiteDisablesLowestPriority() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex lit = graph.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("k");
        lit.setLength(1);
        lit.setSourceLocation("L.java:1");
        lit.setEnclosingClassName("TestUserClass");

        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(5);
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("TestUserClass");

        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setLength(10);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");

        SugVertex concat2 = graph.newVertex();
        concat2.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat2.setLength(10);
        concat2.setSourceLocation("C2.java:1");
        concat2.setEnclosingClassName("TestUserClass");

        SugVertex callSite = graph.newVertex();
        callSite.setNodeType(SugNodeType.STRING_METHOD_CALL);
        callSite.setMethodName("charAt");
        callSite.setDeclaringClass("java.lang.String");
        callSite.setMethodSignature("I");
        callSite.setSourceLocation("U.java:1");

        graph.addEdge(lit, callSite, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, callSite, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(concat, callSite, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(concat2, callSite, SugEdgeType.DATAFLOW, 0);

        InstrumentationDecision sbDec = new InstrumentationDecision(lit, OptimizationType.SINGLE_BYTE, null);
        InstrumentationDecision svDec = new InstrumentationDecision(sub, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision ropeDec = new InstrumentationDecision(concat, OptimizationType.LAZY_CONCAT, "ROPE");
        InstrumentationDecision threeWayDec = new InstrumentationDecision(concat2, OptimizationType.LAZY_CONCAT, "THREE_WAY");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Arrays.asList(sbDec), Arrays.asList(svDec),
                        Arrays.asList(ropeDec, threeWayDec),
                        Collections.emptyList(), Collections.emptyList());

        if (HeuristicOrchestrator.MAX_RECEIVER_CUSTOM_REPS >= 4) {
            /* The cap is 5 (svm.stringanalysis.orch.maxreceiverreps, default 5): 4 reps all survive. */
            Assert.assertEquals(4, orchestrator.getValidatedDecisions().size());
            Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
            Assert.assertTrue(orchestrator.getConflicts().isEmpty());
            return;
        }
        Assert.assertEquals(3, orchestrator.getValidatedDecisions().size());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        InstrumentationDecision suppressed = orchestrator.getConflictSuppressed().get(0);
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, suppressed.getType());
        Assert.assertEquals("THREE_WAY", suppressed.getVariant());
        Assert.assertEquals(1, orchestrator.getConflicts().size());
    }

    @Test
    public void equalsCallSiteEnforcesStrictCrossRepConflict() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setLength(5);
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("TestUserClass");

        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setLength(10);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");

        SugVertex equalsCall = graph.newVertex();
        equalsCall.setNodeType(SugNodeType.STRING_METHOD_CALL);
        equalsCall.setMethodName("equals");
        equalsCall.setDeclaringClass("java.lang.String");
        equalsCall.setMethodSignature("Ljava/lang/Object;");
        equalsCall.setSourceLocation("E.java:1");

        // the tag rule reads the roles: the view is the RECEIVER, the rope the ARGUMENT (slot 1)
        graph.addEdge(sub, equalsCall, SugEdgeType.QUALIFIER, -1);
        graph.addEdge(concat, equalsCall, SugEdgeType.PARAMETER, 1);
        UsageSourceBuilder.build(graph);

        InstrumentationDecision svDec = new InstrumentationDecision(sub, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision ropeDec = new InstrumentationDecision(concat, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Collections.emptyList(), Arrays.asList(svDec), Arrays.asList(ropeDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, orchestrator.getValidatedDecisions().get(0).getType());
        Assert.assertEquals(1, orchestrator.getConflicts().size());
        Assert.assertTrue(orchestrator.getConflicts().get(0), orchestrator.getConflicts().get(0).startsWith("REJECT V" + concat.getId() +
                        " (concat @ C.java:1): cross-rep equals conflict at E.java:1 (ROPE reverted, SV kept)"));
    }

    @Test
    public void nestedConcatLSInLSRejectsInner() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex inner = graph.newVertex();
        inner.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        inner.setSourceLocation("Inner.java:1");
        inner.setEnclosingClassName("TestUserClass");
        inner.setDynamicOperandCount(2);

        SugVertex outer = graph.newVertex();
        outer.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        outer.setSourceLocation("Outer.java:1");
        outer.setEnclosingClassName("TestUserClass");
        outer.setDynamicOperandCount(2);
        outer.setOperandSourceLocations(Arrays.asList("Inner.java:1", "Lit.java:1"));

        InstrumentationDecision innerDec = new InstrumentationDecision(inner, OptimizationType.LAZY_CONCAT, "ROPE");
        InstrumentationDecision outerDec = new InstrumentationDecision(outer, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Collections.emptyList(), Collections.emptyList(),
                        Arrays.asList(innerDec, outerDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertSame(outer, orchestrator.getValidatedDecisions().get(0).getCandidate());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        Assert.assertSame(inner, orchestrator.getConflictSuppressed().get(0).getCandidate());
    }

    /**
     * An inner LS admitted as a lazy operand of the outer site (SugVertex#getLazyOperandSites, set by
     * LazyConcatHeuristic.isLazyOperandOk) is not disabled under that outer by the nested-concat pass; an operand site of
     * another outer still is. The nested-concat pass is checked under {@code lc.lazyoperand=1} (pinned: no nested-LS rule
     * after it); under the default 2 the kept inner is then refused as LS_NESTED_INNER.
     */
    @Test
    public void nestedConcatLazyOperandKeepsInner() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex inner = graph.newVertex();
        inner.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        inner.setSourceLocation("Inner.java:1");
        inner.setEnclosingClassName("TestUserClass");
        inner.setDynamicOperandCount(3);
        inner.addLazyOperandSite("Outer.java:1");

        SugVertex outer = graph.newVertex();
        outer.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        outer.setSourceLocation("Outer.java:1");
        outer.setEnclosingClassName("TestUserClass");
        outer.setDynamicOperandCount(2);
        outer.setOperandSourceLocations(Arrays.asList("Inner.java:1", "Lit.java:1"));

        InstrumentationDecision innerDec = new InstrumentationDecision(inner, OptimizationType.LAZY_CONCAT, "THREE_WAY");
        InstrumentationDecision outerDec = new InstrumentationDecision(outer, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.lazyOperandMode = 1;
        orchestrator.run(Collections.emptyList(), Collections.emptyList(),
                        Arrays.asList(innerDec, outerDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(2, orchestrator.getValidatedDecisions().size());
        Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
        Assert.assertTrue(orchestrator.getConflicts().stream().noneMatch(c -> c.contains("NESTED-CONCAT-CONFLICT")));

        // the default lc.lazyoperand=2 refuses that kept inner (LS inside a kept LS site), the outer stays
        Assert.assertEquals(2, LazyConcatHeuristic.LAZY_OPERAND_MODE);
        HeuristicOrchestrator orchestratorDefault = new HeuristicOrchestrator(graph);
        orchestratorDefault.run(Collections.emptyList(), Collections.emptyList(),
                        Arrays.asList(new InstrumentationDecision(inner, OptimizationType.LAZY_CONCAT, "THREE_WAY"),
                                        new InstrumentationDecision(outer, OptimizationType.LAZY_CONCAT, "ROPE")),
                        Collections.emptyList(), Collections.emptyList());
        Assert.assertEquals(1, orchestratorDefault.getValidatedDecisions().size());
        Assert.assertSame(outer, orchestratorDefault.getValidatedDecisions().get(0).getCandidate());
        Assert.assertEquals(1, orchestratorDefault.getConflictSuppressed().size());
        Assert.assertSame(inner, orchestratorDefault.getConflictSuppressed().get(0).getCandidate());
        Assert.assertTrue(orchestratorDefault.getConflicts().stream().anyMatch(c -> c.contains("NESTED-CONCAT-CONFLICT") && c.contains(LazyConcatHeuristic.LS_NESTED_INNER)));

        // contrast: the recorded site is a different outer -> the inner is disabled as before
        StringUtilizationGraph graph2 = new StringUtilizationGraph();
        SugVertex inner2 = graph2.newVertex();
        inner2.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        inner2.setSourceLocation("Inner.java:1");
        inner2.setEnclosingClassName("TestUserClass");
        inner2.setDynamicOperandCount(3);
        inner2.addLazyOperandSite("Other.java:1");
        SugVertex outer2 = graph2.newVertex();
        outer2.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        outer2.setSourceLocation("Outer.java:1");
        outer2.setEnclosingClassName("TestUserClass");
        outer2.setDynamicOperandCount(2);
        outer2.setOperandSourceLocations(Arrays.asList("Inner.java:1", "Lit.java:1"));
        HeuristicOrchestrator orchestrator2 = new HeuristicOrchestrator(graph2);
        orchestrator2.run(Collections.emptyList(), Collections.emptyList(),
                        Arrays.asList(new InstrumentationDecision(inner2, OptimizationType.LAZY_CONCAT, "THREE_WAY"),
                                        new InstrumentationDecision(outer2, OptimizationType.LAZY_CONCAT, "ROPE")),
                        Collections.emptyList(), Collections.emptyList());
        Assert.assertEquals(1, orchestrator2.getValidatedDecisions().size());
        Assert.assertSame(outer2, orchestrator2.getValidatedDecisions().get(0).getCandidate());
        Assert.assertEquals(1, orchestrator2.getConflictSuppressed().size());
        Assert.assertSame(inner2, orchestrator2.getConflictSuppressed().get(0).getCandidate());
    }

    @Test
    public void nestedConcatSVInLSRejectsOuter() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sv = graph.newVertex();
        sv.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sv.setMethodName("substring");
        sv.setDeclaringClass("java.lang.String");
        sv.setSourceLocation("SV.java:1");
        sv.setEnclosingClassName("TestUserClass");

        SugVertex ls = graph.newVertex();
        ls.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        ls.setSourceLocation("LS.java:1");
        ls.setEnclosingClassName("TestUserClass");
        ls.setDynamicOperandCount(2);
        ls.setOperandSourceLocations(Arrays.asList("SV.java:1", "Lit.java:1"));

        InstrumentationDecision svDec = new InstrumentationDecision(sv, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision lsDec = new InstrumentationDecision(ls, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Collections.emptyList(), Arrays.asList(svDec),
                        Arrays.asList(lsDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertSame(sv, orchestrator.getValidatedDecisions().get(0).getCandidate());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        Assert.assertSame(ls, orchestrator.getConflictSuppressed().get(0).getCandidate());
    }

    @Test
    public void nestedConcatSBSInLSRejectsOuter() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sbs = graph.newVertex();
        sbs.setNodeType(SugNodeType.STRING_LITERAL);
        sbs.setLiteralText("k");
        sbs.setLength(1);
        sbs.setSourceLocation("SBS.java:1");
        sbs.setEnclosingClassName("TestUserClass");

        SugVertex ls = graph.newVertex();
        ls.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        ls.setSourceLocation("LS.java:1");
        ls.setEnclosingClassName("TestUserClass");
        ls.setDynamicOperandCount(2);
        ls.setOperandSourceLocations(Arrays.asList("SBS.java:1", "Lit.java:1"));

        InstrumentationDecision sbsDec = new InstrumentationDecision(sbs, OptimizationType.SINGLE_BYTE, null);
        InstrumentationDecision lsDec = new InstrumentationDecision(ls, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Arrays.asList(sbsDec), Collections.emptyList(),
                        Arrays.asList(lsDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertSame(sbs, orchestrator.getValidatedDecisions().get(0).getCandidate());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        Assert.assertSame(ls, orchestrator.getConflictSuppressed().get(0).getCandidate());
    }

    @Test
    public void nestedConcatNoCustomRepOperandsKeepsLS() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex ls = graph.newVertex();
        ls.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        ls.setSourceLocation("LS.java:1");
        ls.setEnclosingClassName("TestUserClass");
        ls.setDynamicOperandCount(2);
        ls.setOperandSourceLocations(Arrays.asList("Lit1.java:1", "Lit2.java:1"));

        InstrumentationDecision lsDec = new InstrumentationDecision(ls, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Collections.emptyList(), Collections.emptyList(),
                        Arrays.asList(lsDec),
                        Collections.emptyList(), Collections.emptyList());

        Assert.assertEquals(1, orchestrator.getValidatedDecisions().size());
        Assert.assertSame(ls, orchestrator.getValidatedDecisions().get(0).getCandidate());
        Assert.assertTrue(orchestrator.getConflictSuppressed().isEmpty());
    }
}
