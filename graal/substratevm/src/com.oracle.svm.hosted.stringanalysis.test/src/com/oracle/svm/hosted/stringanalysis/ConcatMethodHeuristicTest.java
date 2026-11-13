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

/**
 * {@code String.concat} lazy-concat support: a {@code String.concat(String)} call site is captured as a
 * {@link ConcatMethodSite}, built into a 2-operand {@code CONCAT_EXPRESSION} vertex (receiver + arg), admitted as a
 * {@code LAZY_CONCAT ROPE} by {@link LazyConcatHeuristic}, and handled by the nested-concat conflict rule when an operand
 * is itself a custom rep or nested concat.
 */
public class ConcatMethodHeuristicTest {

    private static SugVertex concatMethodVertex(StringUtilizationGraph graph, List<String> opLocs) {
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");
        concat.setDynamicOperandCount(2);
        concat.setOperandSourceLocations(opLocs);
        // receiver (operand 0) -> CONCAT_LEFT, arg (operand 1) -> CONCAT_RIGHT
        SugVertex recv = graph.newVertex();
        recv.setNodeType(SugNodeType.VARIABLE);
        recv.setSourceLocation(opLocs.get(0));
        graph.addEdge(recv, concat, SugEdgeType.CONCAT_LEFT, 0);
        SugVertex arg = graph.newVertex();
        arg.setNodeType(SugNodeType.VARIABLE);
        arg.setSourceLocation(opLocs.get(1));
        graph.addEdge(arg, concat, SugEdgeType.CONCAT_RIGHT, 1);
        return concat;
    }

    private static void addDownstreamUsage(StringUtilizationGraph graph, SugVertex concat) {
        SugVertex length = graph.newVertex();
        length.setNodeType(SugNodeType.STRING_METHOD_CALL);
        length.setMethodName("length");
        length.setDeclaringClass("java.lang.String");
        length.setSourceLocation("C.java:99");
        graph.addEdge(concat, length, SugEdgeType.DATAFLOW, 0);
    }

    @Test
    public void stringConcatSiteAdmittedAsRope() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatMethodVertex(graph, Arrays.asList("Recv.java:1", "Arg.java:1"));
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, decisions.get(0).getType());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
        Assert.assertSame(concat, decisions.get(0).getCandidate());
    }

    @Test
    public void stringConcatReceiverStringViewArgSbsMixRepConflict() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // A String.concat ROPE whose receiver is a STRING_VIEW and whose arg is an SBS.
        SugVertex sv = graph.newVertex();
        sv.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sv.setMethodName("substring");
        sv.setDeclaringClass("java.lang.String");
        sv.setLength(5);
        sv.setSourceLocation("SV.java:1");
        sv.setEnclosingClassName("TestUserClass");

        SugVertex sbs = graph.newVertex();
        sbs.setNodeType(SugNodeType.STRING_LITERAL);
        sbs.setLiteralText("k");
        sbs.setLength(1);
        sbs.setSourceLocation("SBS.java:1");
        sbs.setEnclosingClassName("TestUserClass");

        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");
        concat.setDynamicOperandCount(2);
        // receiver is the StringView, arg is the SBS -> mix-rep inside the concat.
        concat.setOperandSourceLocations(Arrays.asList("SV.java:1", "SBS.java:1"));
        graph.addEdge(sv, concat, SugEdgeType.CONCAT_LEFT, 0);
        graph.addEdge(sbs, concat, SugEdgeType.CONCAT_RIGHT, 1);

        InstrumentationDecision svDec = new InstrumentationDecision(sv, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision sbsDec = new InstrumentationDecision(sbs, OptimizationType.SINGLE_BYTE, null);
        InstrumentationDecision lsDec = new InstrumentationDecision(concat, OptimizationType.LAZY_CONCAT, "ROPE");

        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(graph);
        orchestrator.run(Arrays.asList(sbsDec), Arrays.asList(svDec), Arrays.asList(lsDec),
                        Collections.emptyList(), Collections.emptyList());

        // A String.concat ROPE whose operands are custom reps is disabled; the higher-priority
        // custom reps survive.
        Assert.assertEquals(2, orchestrator.getValidatedDecisions().size());
        Assert.assertEquals(1, orchestrator.getConflictSuppressed().size());
        Assert.assertSame(concat, orchestrator.getConflictSuppressed().get(0).getCandidate());
        Assert.assertTrue(orchestrator.getConflicts().stream().anyMatch(c -> c.contains("NESTED-CONCAT-CONFLICT")));
    }

    @Test
    public void stringConcatNestedLazyInsideLazyDisablesInner() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // Inner lazy concat (a 2-op + concat) flows as the arg of a String.concat ROPE.
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
        outer.setOperandSourceLocations(Arrays.asList("Recv.java:1", "Inner.java:1"));

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
}
