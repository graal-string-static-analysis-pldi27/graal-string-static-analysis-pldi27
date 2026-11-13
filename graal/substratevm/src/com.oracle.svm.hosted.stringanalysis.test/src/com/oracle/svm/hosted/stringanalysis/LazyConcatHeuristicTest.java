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

public class LazyConcatHeuristicTest {

    private static SugVertex concatWithOperands(StringUtilizationGraph graph, int operandCount, String loc) {
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation(loc);
        concat.setEnclosingClassName("TestUserClass");
        for (int i = 0; i < operandCount; i++) {
            SugVertex operand = graph.newVertex();
            operand.setNodeType(SugNodeType.STRING_LITERAL);
            operand.setLiteralText("o" + i);
            SugEdgeType edgeType = (i % 2 == 0) ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT;
            graph.addEdge(operand, concat, edgeType, i);
        }
        return concat;
    }

    private static SugVertex concatWithOperandTexts(StringUtilizationGraph graph, String[] texts, String loc) {
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation(loc);
        concat.setEnclosingClassName("TestUserClass");
        for (int i = 0; i < texts.length; i++) {
            SugVertex operand = graph.newVertex();
            operand.setNodeType(texts[i] == null ? SugNodeType.VARIABLE : SugNodeType.STRING_LITERAL);
            if (texts[i] != null) {
                operand.setLiteralText(texts[i]);
            }
            SugEdgeType edgeType = (i % 2 == 0) ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT;
            graph.addEdge(operand, concat, edgeType, i);
        }
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
    public void twoOperandsRopeVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 2, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, decisions.get(0).getType());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
        Assert.assertSame(concat, decisions.get(0).getCandidate());
    }

    @Test
    public void threeOperandsThreeWayVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 3, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("THREE_WAY", decisions.get(0).getVariant());
    }

    @Test
    public void fourOperandsFixed4Variant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 4, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("FIXED4", decisions.get(0).getVariant());
    }

    @Test
    public void fiveOperandsInterleavedVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null, ",", null, ",", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("INTERLEAVED", decisions.get(0).getVariant());
    }

    @Test
    public void sevenOperandsInterleavedVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null, ",", null, ",", null, ",", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("INTERLEAVED", decisions.get(0).getVariant());
    }

    @Test
    public void fiveOperandsArrayLazyAllVariablesVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null, null, null, null, null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ARRAY_LAZY", decisions.get(0).getVariant());
    }

    @Test
    public void fiveOperandsArrayLazyVaryingSeparatorsVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null, ",", null, ";", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ARRAY_LAZY", decisions.get(0).getVariant());
    }

    @Test
    public void sixOperandsArrayLazyEvenCountVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null, ",", null, ",", null, ","}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ARRAY_LAZY", decisions.get(0).getVariant());
    }

    @Test
    public void fiveOperandsArrayLazyConstantAtEvenIndexVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{",", ",", null, ",", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ARRAY_LAZY", decisions.get(0).getVariant());
    }

    @Test
    public void zeroOperandsNoDecision() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(0, decisions.size());
    }

    @Test
    public void oneOperandNoDecision() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperandTexts(graph, new String[]{null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(0, decisions.size());
    }

    @Test
    public void nestedConcatBothAdmittedWithoutIsOutermost() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex outer = concatWithOperands(graph, 2, "C.java:1");
        SugVertex inner = concatWithOperands(graph, 2, "C.java:2");
        addDownstreamUsage(graph, inner);
        addDownstreamUsage(graph, outer);

        LazyConcatHeuristic heuristic = new LazyConcatHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(2, heuristic.getConcatExpressionTotal());
        Assert.assertEquals(2, heuristic.getCandidateCount());
        Assert.assertEquals(2, decisions.size());
    }

    @Test
    public void reachableNonWhitelistedCallRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 2, "C.java:1");
        SugVertex replace = graph.newVertex();
        replace.setNodeType(SugNodeType.STRING_METHOD_CALL);
        replace.setMethodName("replace");
        replace.setMethodSignature("CC");
        replace.setDeclaringClass("java.lang.String");
        replace.setSourceLocation("C.java:3");
        graph.addEdge(concat, replace, SugEdgeType.DATAFLOW, 0);

        LazyConcatHeuristic heuristic = new LazyConcatHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("replace"));
    }

    @Test
    public void concatLeftRightEdgesCountedForVariant() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");
        SugVertex left = graph.newVertex();
        left.setNodeType(SugNodeType.VARIABLE);
        SugVertex right = graph.newVertex();
        right.setNodeType(SugNodeType.VARIABLE);
        SugVertex third = graph.newVertex();
        third.setNodeType(SugNodeType.STRING_LITERAL);
        graph.addEdge(left, concat, SugEdgeType.CONCAT_LEFT, 0);
        graph.addEdge(right, concat, SugEdgeType.CONCAT_RIGHT, 1);
        graph.addEdge(third, concat, SugEdgeType.CONCAT_LEFT, 2);
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("THREE_WAY", decisions.get(0).getVariant());
        int operandEdges = 0;
        for (SugEdge e : concat.getInEdges()) {
            if (e.getEdgeType() == SugEdgeType.CONCAT_LEFT || e.getEdgeType() == SugEdgeType.CONCAT_RIGHT) {
                operandEdges++;
            }
        }
        Assert.assertEquals(3, operandEdges);
    }

    @Test
    public void concatWithParameterEdgesFallsBackToRope() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation("C.java:1");
        concat.setEnclosingClassName("TestUserClass");
        SugVertex a = graph.newVertex();
        a.setNodeType(SugNodeType.VARIABLE);
        SugVertex b = graph.newVertex();
        b.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(a, concat, SugEdgeType.PARAMETER, 0);
        graph.addEdge(b, concat, SugEdgeType.PARAMETER, 1);
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
    }

    // --- Total (actual) operand count + empty-operand rejection (the empty-operand rules) ---

    private static SugVertex concatWithDynamicCountAndOperands(StringUtilizationGraph graph, int dynamicCount, String[] texts, String loc) {
        SugVertex concat = graph.newVertex();
        concat.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concat.setSourceLocation(loc);
        concat.setEnclosingClassName("TestUserClass");
        concat.setDynamicOperandCount(dynamicCount);
        for (int i = 0; i < texts.length; i++) {
            SugVertex operand = graph.newVertex();
            if (texts[i] == null) {
                operand.setNodeType(SugNodeType.VARIABLE);
            } else {
                operand.setNodeType(SugNodeType.STRING_LITERAL);
                operand.setLiteralText(texts[i]);
                operand.setLength(texts[i].length());
            }
            SugEdgeType edgeType = (i % 2 == 0) ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT;
            graph.addEdge(operand, concat, edgeType, i);
        }
        return concat;
    }

    @Test
    public void oneDynamicPlusOneConstantAdmittedAsRope() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // "string" + x : 1 dynamic operand + 1 recipe constant = 2 total operands.
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"string", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.LAZY_CONCAT, decisions.get(0).getType());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
    }

    @Test
    public void oneDynamicPlusTwoConstantsAdmittedAsThreeWay() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // "a" + x + "b" : 1 dynamic + 2 constants = 3 total operands. The variant is derived
        // from totalCount -> THREE_WAY, consistent with the runtime lowering by totalParts==3.
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"a", null, "b"}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("THREE_WAY", decisions.get(0).getVariant());
    }

    @Test
    public void oneDynamicPlusThreeConstantsAdmittedAsFixed4() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // 1 dynamic + 3 constants = 4 total operands -> FIXED4.
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"a", null, "b", "c"}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("FIXED4", decisions.get(0).getVariant());
    }

    @Test
    public void oneDynamicPlusManyConstantsAdmittedAsArrayLazy() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // 1 dynamic + 4 constants = 5 total operands -> ARRAY_LAZY (not a regular interleave).
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"a", null, "b", "c", "d"}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ARRAY_LAZY", decisions.get(0).getVariant());
    }

    @Test
    public void twoDynamicAdmittedAsRope() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 2, new String[]{null, null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
    }

    @Test
    public void emptyConstantOperandRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // "" + x : an empty constant operand as the left child.
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"", null}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(0, decisions.size());
    }

    @Test
    public void emptyConstantOperandRejectedThreeWay() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        // "" + x + "b" : empty constant in the middle of a 3-part concat.
        SugVertex concat = concatWithDynamicCountAndOperands(graph, 1, new String[]{"", null, "b"}, "C.java:1");
        addDownstreamUsage(graph, concat);

        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);

        Assert.assertEquals(0, decisions.size());
    }

    /**
     * A concat with out-edges to non-call vertices, a complete trace and no usage facts: it is ADMITted
     * with the no-usage warning.
     * (The operands' CONCAT_LEFT/CONCAT_RIGHT in-edges are the concat's inputs, not its downstream.)
     */
    @Test
    public void completeTraceNoUsagesAdmittedWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 2, "C.java:1");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        graph.addEdge(concat, passthrough, SugEdgeType.DATAFLOW, 0);

        LazyConcatHeuristic heuristic = new LazyConcatHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the no-usage concat ADMITs with the dev-time warning; the no-proof
        // predicate is pinned.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, concat));
    }

    /**
     * The same no-proof shape with the wired-any-load bit set (a STORE endpoint of one of the concat's origins wired a
     * non-empty load set): ADMIT; the bit is the heap-reaching proof.
     */

    @Test
    public void wiredHeapPathConcatAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithOperands(graph, 2, "C.java:1");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        graph.addEdge(concat, passthrough, SugEdgeType.DATAFLOW, 0);
        concat.markWiredAnyLoad();

        LazyConcatHeuristic heuristic = new LazyConcatHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ROPE", decisions.get(0).getVariant());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    // --- An indy vertex with a recorded shape is named by its total parts; Rule 2's operand kinds ---

    private static String admittedVariant(int dyn, String recipe, String kinds, String[] texts) {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex concat = concatWithDynamicCountAndOperands(graph, dyn, texts, "C.java:1");
        concat.setMethodName(recipe == null ? "makeConcat" : "makeConcatWithConstants");
        concat.setConcatRecipe(recipe);
        concat.setConcatOperandKinds(kinds);
        addDownstreamUsage(graph, concat);
        List<InstrumentationDecision> decisions = new LazyConcatHeuristic().apply(graph);
        return decisions.isEmpty() ? null : decisions.get(0).getVariant();
    }

    @Test
    public void recordedShapeIsNamedByTotalParts() {
        // "string" + i + "string" + i: dyn 2, total 4 -> FIXED4
        Assert.assertEquals("FIXED4", admittedVariant(2, "string\u0001string\u0001", "PP", new String[]{"string", null, "string", null}));
        // "string" + z + b: dyn 2, total 3 -> THREE_WAY
        Assert.assertEquals("THREE_WAY", admittedVariant(2, "string\u0001\u0001", "PP", new String[]{"string", null, null}));
        // a regular \1,\1,\1: dyn 3, total 5 -> INTERLEAVED
        Assert.assertEquals("INTERLEAVED", admittedVariant(3, "\u0001,\u0001,\u0001", "SSS", new String[]{null, ",", null, ",", null}));
        // dyn 2, total 5 -> ARRAY_LAZY (and the parent mints it: the total-parts gate)
        Assert.assertEquals("ARRAY_LAZY", admittedVariant(2, "a\u0001b\u0001c", "SS", new String[]{"a", null, "b", null, "c"}));
        Assert.assertEquals("ARRAY_LAZY", LazyConcatMint.mintedRep("ARRAY_LAZY", 2, "a\u0001b\u0001c"));
        // makeConcat, 2 dynamic: ROPE; 1-part recipe: rejected (too few)
        Assert.assertEquals("ROPE", admittedVariant(2, null, "SS", new String[]{null, null}));
        Assert.assertNull(admittedVariant(1, "\u0001", "S", new String[]{null}));
    }

    @Test
    public void primitiveOnlySiteStaysLazy() {
        // a site whose dynamic operands are all primitives stays lazy (each operand its own converted part)
        Assert.assertEquals("ROPE", admittedVariant(1, "k=\u0001", "P", new String[]{"k=", null}));
    }

    /** The nested lazy-operand rule (isLazyOperandOk): non-copying indy site x a rep with getBytes. */
    @Test
    public void lazyOperandRule() {
        SugVertex site = new SugVertex(1);
        site.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        site.setMethodName("makeConcatWithConstants");
        site.setSourceLocation("Outer.java:1");
        // not (yet) marked scfNoCopy: a copying strategy (newStringOf/simpleConcat) rejects every rep
        for (String rep : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            Assert.assertFalse(rep, LazyConcatHeuristic.isLazyOperandOk(site, rep));
        }
        site.markScfNoCopy();
        // every lazy rep overrides the protected getBytes(byte[],int,byte), ROPE included
        for (String rep : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            Assert.assertEquals(rep, LazyConcatHeuristic.LAZY_OPERAND, LazyConcatHeuristic.isLazyOperandOk(site, rep));
        }
        Assert.assertFalse(LazyConcatHeuristic.isLazyOperandOk(site, null));
        // a String.concat vertex is never marked scfNoCopy by the forward fixpoint: it rejects every rep
        SugVertex concatCall = new SugVertex(2);
        concatCall.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        concatCall.setMethodName("concat");
        Assert.assertTrue(concatCall.isStringConcatCall());
        Assert.assertFalse(concatCall.isScfNoCopy());
        Assert.assertFalse(LazyConcatHeuristic.isLazyOperandOk(concatCall, "THREE_WAY"));
    }
}
