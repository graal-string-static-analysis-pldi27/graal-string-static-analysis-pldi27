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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

public class CrossRepConflictTest {

    @Test
    public void crossRepPrioritySingleByte() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.SINGLE_BYTE, null);
        assertEquals(1, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityStringView() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.STRING_VIEW, null);
        assertEquals(2, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatRope() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ROPE");
        assertEquals(3, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatThreeWay() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "THREE_WAY");
        assertEquals(4, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatFixed4() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "FIXED4");
        assertEquals(5, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatArrayLazy() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ARRAY_LAZY");
        assertEquals(6, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatInterleaved() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "INTERLEAVED");
        assertEquals(7, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityLazyConcatNullVariantDefaultsToRope() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, null);
        assertEquals(3, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityEqualsMatrix() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.EQUALS_MATRIX, null);
        assertEquals(8, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void crossRepPriorityUnknownVariantDefaultsToRope() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "UNKNOWN");
        assertEquals(3, HeuristicOrchestrator.crossRepPriority(d));
    }

    @Test
    public void repTypeOfSingleByte() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.SINGLE_BYTE, null);
        assertEquals("SBS", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfStringView() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.STRING_VIEW, null);
        assertEquals("SV", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatRope() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ROPE");
        assertEquals("ROPE", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatThreeWay() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "THREE_WAY");
        assertEquals("THREE_WAY", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatFixed4() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "FIXED4");
        assertEquals("FIXED4", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatArrayLazy() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "ARRAY_LAZY");
        assertEquals("ARRAY_LAZY", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatInterleaved() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, "INTERLEAVED");
        assertEquals("INTERLEAVED", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfLazyConcatNullVariantDefaultsToRope() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, null);
        assertEquals("ROPE", HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repTypeOfEqualsMatrixIsNull() {
        SugVertex v = newVertex();
        InstrumentationDecision d = new InstrumentationDecision(v, OptimizationType.EQUALS_MATRIX, null);
        assertNull(HeuristicOrchestrator.repTypeOf(d));
    }

    @Test
    public void repClassOfFqnSingleByteString() {
        assertEquals("SBS", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.SingleByteString"));
    }

    @Test
    public void repClassOfFqnTrivialString() {
        assertEquals("SBS", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.TrivialString"));
    }

    @Test
    public void repClassOfFqnStringView() {
        assertEquals("SV", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.StringView"));
    }

    @Test
    public void repClassOfFqnRopeString() {
        assertEquals("ROPE", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.RopeString"));
    }

    @Test
    public void repClassOfFqnThreeWayString() {
        assertEquals("THREE_WAY", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.ThreeWayString"));
    }

    @Test
    public void repClassOfFqnFixedConcat4() {
        assertEquals("FIXED4", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.FixedConcat4"));
    }

    @Test
    public void repClassOfFqnArrayLazyString() {
        assertEquals("ARRAY_LAZY", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.ArrayLazyString"));
    }

    @Test
    public void repClassOfFqnInterleavedStringArray() {
        assertEquals("INTERLEAVED", HeuristicOrchestrator.repClassOfFqn("com.oracle.svm.core.stringrep.InterleavedStringArray"));
    }

    @Test
    public void repClassOfFqnUnknownReturnsInput() {
        assertEquals("java.lang.String", HeuristicOrchestrator.repClassOfFqn("java.lang.String"));
    }

    // ---- the tag rule

    @Test
    public void tagRuleSameRepIsNoConflict() {
        assertFalse(HeuristicOrchestrator.isCrossRepEqualsConflict("SV", "SV"));
        assertFalse(HeuristicOrchestrator.isCrossRepEqualsConflict("ROPE", "ROPE"));
        assertFalse(HeuristicOrchestrator.isCrossRepEqualsConflict("SBS", "SBS"));
    }

    @Test
    public void tagRuleDifferentRepsConflictBothWays() {
        assertTrue(HeuristicOrchestrator.isCrossRepEqualsConflict("SV", "ROPE"));
        assertTrue(HeuristicOrchestrator.isCrossRepEqualsConflict("ROPE", "SV"));
        assertTrue(HeuristicOrchestrator.isCrossRepEqualsConflict("ROPE", "THREE_WAY"));
    }

    /** SB as the RECEIVER is no conflict (the deflection reaches the fixed paths). */
    @Test
    public void tagRuleSbReceiverIsNoConflict() {
        assertFalse("sb.equals(sv)", HeuristicOrchestrator.isCrossRepEqualsConflict("SBS", "SV"));
        assertFalse("sb.equals(rope)", HeuristicOrchestrator.isCrossRepEqualsConflict("SBS", "ROPE"));
        assertFalse("sb.equals(three-way)", HeuristicOrchestrator.isCrossRepEqualsConflict("SBS", "THREE_WAY"));
    }

    /**
     * Every rep's equals path compares a flat SB argument by content, pinned by {@code RepEqualsMatrixTest}: SB as the
     * argument is no conflict.
     */
    @Test
    public void tagRuleSbArgumentIsNoConflict() {
        assertFalse(HeuristicOrchestrator.isCrossRepEqualsConflict("SV", "SBS"));
        assertFalse(HeuristicOrchestrator.isCrossRepEqualsConflict("ROPE", "SBS"));
    }

    @Test
    public void tagRuleSvReceiverRopeArgumentKeepsSv() {
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:1");
        InstrumentationDecision rope = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2");
        assertEquals(List.of(rope), HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv), List.of(rope)));
        assertEquals(List.of(rope), HeuristicOrchestrator.crossRepEqualsReverts(List.of(rope), List.of(sv)));
    }

    @Test
    public void tagRuleSbReceiverSvArgumentKeepsSb() {
        InstrumentationDecision sb = decision(OptimizationType.SINGLE_BYTE, null, "A.java:1");
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:2");
        assertTrue("SB as the receiver is no conflict", HeuristicOrchestrator.crossRepEqualsReverts(List.of(sb), List.of(sv)).isEmpty());
    }

    @Test
    public void tagRuleSvReceiverSbArgument() {
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:1");
        InstrumentationDecision sb = decision(OptimizationType.SINGLE_BYTE, null, "A.java:2");
        assertTrue("no conflict", HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv), List.of(sb)).isEmpty());
    }

    @Test
    public void tagRuleNeedsBothRoles() {
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:1");
        InstrumentationDecision rope = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2");
        assertTrue(HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv, rope), List.of()).isEmpty());
        assertTrue(HeuristicOrchestrator.crossRepEqualsReverts(List.of(), List.of(sv, rope)).isEmpty());
    }

    @Test
    public void tagRuleRevertsEveryOtherRepAndKeepsSameRepPartners() {
        InstrumentationDecision rope = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:1");
        InstrumentationDecision threeWay = decision(OptimizationType.LAZY_CONCAT, "THREE_WAY", "A.java:3");
        InstrumentationDecision rope2 = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2");
        // receivers rope, three-way; argument rope2: only (three-way, rope2) conflicts; ROPE kept, THREE_WAY reverted
        assertEquals(List.of(threeWay), HeuristicOrchestrator.crossRepEqualsReverts(List.of(rope, threeWay), List.of(rope2)));
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:4");
        InstrumentationDecision fixed4 = decision(OptimizationType.LAZY_CONCAT, "FIXED4", "A.java:5");
        // SV receiver, two lazy arguments: SV kept, both lazy decisions reverted, in source-location order
        assertEquals(List.of(rope2, fixed4), HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv), List.of(fixed4, rope2)));
    }

    private static InstrumentationDecision decision(OptimizationType t, String variant, String loc) {
        SugVertex v = newVertex();
        v.setSourceLocation(loc);
        return new InstrumentationDecision(v, t, variant);
    }

    private static SugVertex newVertex() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex v = graph.newVertex();
        v.setSourceLocation("X.java:1");
        v.setEnclosingClassName("TestUserClass");
        return v;
    }
}