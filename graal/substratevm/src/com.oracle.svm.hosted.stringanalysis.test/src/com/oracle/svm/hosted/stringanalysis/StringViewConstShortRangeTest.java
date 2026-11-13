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

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.SubNode;
import jdk.vm.ci.meta.JavaKind;

/**
 * Constant short range: a substring/subSequence site that would be admitted as {@code STRING_VIEW STORED} is refused for SV
 * ({@code SV_CONST_SHORT_RANGE}) when its range length is a compile-time constant {@code <= 4}; a run-time length is still
 * admitted, and the same site stays a SingleByte admit (only SV refuses it).
 */
public class StringViewConstShortRangeTest {

    private static ValueNode param(int index) {
        return new ParameterNode(index, StampPair.createSingle(StampFactory.forKind(JavaKind.Int)));
    }

    private static ValueNode c(int value) {
        return ConstantNode.forInt(value);
    }

    // ---- the capture fact --------------------------------------------------------------------------------------

    @Test
    public void constRangeLengthOfTheCapturedBounds() {
        ValueNode i = param(1);
        ValueNode j = param(2);
        Assert.assertEquals("substring(i, i + 1)", 1, StringAnalysisCapturePlugin.constRangeLength(i, new AddNode(i, c(1)), false));
        Assert.assertEquals("substring(i, 4 + i)", 4, StringAnalysisCapturePlugin.constRangeLength(i, new AddNode(c(4), i), false));
        Assert.assertEquals("substring(j - 2, j) as parsed: j + (-2)", 2, StringAnalysisCapturePlugin.constRangeLength(new AddNode(j, c(-2)), j, false));
        Assert.assertEquals("substring(-2 + j, j)", 2, StringAnalysisCapturePlugin.constRangeLength(new AddNode(c(-2), j), j, false));
        Assert.assertEquals("substring(j - 2, j) raw SubNode form", 2, StringAnalysisCapturePlugin.constRangeLength(new SubNode(j, c(2)), j, false));
        Assert.assertEquals("substring(j + 2, j): positive offset, not a length", -1, StringAnalysisCapturePlugin.constRangeLength(new AddNode(j, c(2)), j, false));
        Assert.assertEquals("substring(i - 2, j): different values", -1, StringAnalysisCapturePlugin.constRangeLength(new AddNode(i, c(-2)), j, false));
        Assert.assertEquals("substring(2, 5)", 3, StringAnalysisCapturePlugin.constRangeLength(c(2), c(5), false));
        Assert.assertEquals("substring(i, i + 9): constant, not short", 9, StringAnalysisCapturePlugin.constRangeLength(i, new AddNode(i, c(9)), false));
        Assert.assertEquals("substring(i, j): run-time length", -1, StringAnalysisCapturePlugin.constRangeLength(i, j, false));
        Assert.assertEquals("substring(i, j + 1): different values", -1, StringAnalysisCapturePlugin.constRangeLength(i, new AddNode(j, c(1)), false));
        Assert.assertEquals("substring(5, 2): negative, not a length", -1, StringAnalysisCapturePlugin.constRangeLength(c(5), c(2), false));
        Assert.assertTrue("the unit-range proof agrees on c = 1", StringAnalysisCapturePlugin.isUnitRange(i, new AddNode(i, c(1)), false));
    }

    // ---- the pure rule -----------------------------------------------------------------------------------------

    @Test
    public void refusesOnlyAStoredViewOfAConstantShortRange() {
        String stored = StringViewHeuristic.STORED;
        Assert.assertTrue(StringViewHeuristic.refusesConstShortRange(stored, 0));
        Assert.assertTrue(StringViewHeuristic.refusesConstShortRange(stored, 1));
        Assert.assertTrue(StringViewHeuristic.refusesConstShortRange(stored, 4));
        Assert.assertFalse(StringViewHeuristic.refusesConstShortRange(stored, 5));
        Assert.assertFalse("a run-time length is never refused", StringViewHeuristic.refusesConstShortRange(stored, SugVertex.UNKNOWN_LENGTH));
        Assert.assertFalse("a confined (unchecked) view is not touched", StringViewHeuristic.refusesConstShortRange(null, 1));
    }

    // ---- the heuristics on a SUG -------------------------------------------------------------------------------

    /** A user-code {@code substring(II)} with one {@code length()} usage; stored, with the given constant range length. */
    private static SugVertex storedSubstring(StringUtilizationGraph graph, String loc, int constRange) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("substring");
        v.setMethodSignature("I,I");
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        v.setEnclosingClassName("TestUserClass");
        v.setConstRangeLength(constRange);
        v.markStored();
        SugVertex length = graph.newVertex();
        length.setNodeType(SugNodeType.STRING_METHOD_CALL);
        length.setMethodName("length");
        length.setMethodSignature("");
        length.setDeclaringClass("java.lang.String");
        length.setSourceLocation(loc + "#len");
        length.setEnclosingClassName("TestUserClass");
        graph.addEdge(v, length, SugEdgeType.DATAFLOW, 0);
        return v;
    }

    @Test
    public void unitRangeIsRefusedForSvWithTheNamedReason() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        storedSubstring(graph, "A#read()V@67", 1); // substring(i, i + 1)
        StringViewHeuristic sv = new StringViewHeuristic();
        Assert.assertTrue(sv.apply(graph).isEmpty());
        Assert.assertEquals(1, sv.getRejections().size());
        Assert.assertTrue(sv.getRejections().get(0), sv.getRejections().get(0).contains(StringViewHeuristic.SV_CONST_SHORT_RANGE));
    }

    @Test
    public void constantBoundsAreRefusedForSv() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        storedSubstring(graph, "A#m()V@3", 3); // substring(2, 5)
        StringViewHeuristic sv = new StringViewHeuristic();
        Assert.assertTrue(sv.apply(graph).isEmpty());
        Assert.assertTrue(sv.getRejections().get(0).contains(StringViewHeuristic.SV_CONST_SHORT_RANGE));
    }

    @Test
    public void runTimeAndLongConstantLengthsStayStoredViews() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex runTime = storedSubstring(graph, "A#endCapture()V@44", SugVertex.UNKNOWN_LENGTH); // substring(i, j)
        SugVertex five = storedSubstring(graph, "A#m()V@9", 5); // substring(i, i + 5)
        StringViewHeuristic sv = new StringViewHeuristic();
        List<InstrumentationDecision> d = sv.apply(graph);
        Assert.assertEquals(2, d.size());
        Assert.assertSame(runTime, d.get(0).getCandidate());
        Assert.assertSame(five, d.get(1).getCandidate());
        for (InstrumentationDecision x : d) {
            Assert.assertEquals(OptimizationType.STRING_VIEW, x.getType());
            Assert.assertEquals(StringViewHeuristic.STORED, x.getVariant());
        }
        Assert.assertTrue(sv.getRejections().isEmpty());
    }

    @Test
    public void aConfinedDuplicateAtARefusedKeyIsDroppedToo() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        storedSubstring(graph, "A#read()V@67", 1);
        SugVertex confined = graph.newVertex();
        confined.setNodeType(SugNodeType.STRING_METHOD_CALL);
        confined.setMethodName("substring");
        confined.setMethodSignature("I,I");
        confined.setDeclaringClass("java.lang.String");
        confined.setSourceLocation("A#read()V@67");
        confined.setEnclosingClassName("TestUserClass");
        confined.setConstRangeLength(1);
        StringViewHeuristic sv = new StringViewHeuristic();
        Assert.assertTrue("no unchecked view at a key whose stored vertex was refused", sv.apply(graph).isEmpty());
        Assert.assertEquals(2, sv.getRejections().size());
    }

    @Test
    public void theSameSiteIsStillASingleByteAdmit() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = storedSubstring(graph, "A#read()V@67", 1);
        sub.setLength(1); // E3: the unit-range proof
        StringViewHeuristic sv = new StringViewHeuristic();
        Assert.assertTrue(sv.apply(graph).isEmpty());
        List<InstrumentationDecision> sbs = new SingleByteHeuristic().apply(graph);
        Assert.assertEquals(1, sbs.size());
        Assert.assertEquals(OptimizationType.SINGLE_BYTE, sbs.get(0).getType());
        Assert.assertSame(sub, sbs.get(0).getCandidate());
    }
}
