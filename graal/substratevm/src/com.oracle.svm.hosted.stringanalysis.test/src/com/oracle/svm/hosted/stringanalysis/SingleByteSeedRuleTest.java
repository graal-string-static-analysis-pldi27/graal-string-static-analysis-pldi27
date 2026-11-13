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

/**
 * Pins of the Single Byte creation-site seed rule ({@link ForwardFixpoint#isSbCreationSeed}). The seeds are minted
 * inside the SUG build, before {@link LengthPropagator} assigns substring/{@code valueOf(char)} lengths, so the rule must
 * accept {@code UNKNOWN_LENGTH} (a clause that required 1 would seed nothing in SBS mode); the length filter is
 * {@link SingleByteHeuristic}'s post-propagator {@code getLength() == 1} check.
 */
public class SingleByteSeedRuleTest {

    private static SugVertex call(StringUtilizationGraph g, String name, String sig) {
        SugVertex v = g.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName("TestUserClass");
        return v;
    }

    /** The premise: a creation-site vertex is UNKNOWN_LENGTH until the propagator runs ({@code valueOf(char)} gets 1 there). */
    @Test
    public void seedTimeLengthIsUnknownUntilPropagation() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex voc = call(g, "valueOf", "char");
        Assert.assertEquals(SugVertex.UNKNOWN_LENGTH, voc.getLength());
        Assert.assertTrue(ForwardFixpoint.isSbCreationSeed(voc));
        new LengthPropagator(g).propagate();
        Assert.assertEquals(1, voc.getLength());
    }

    @Test
    public void seedsLengthOneOrUnknownSubstringAndValueOfChar() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        Assert.assertTrue(ForwardFixpoint.isSbCreationSeed(call(g, "substring", "int,int")));
        SugVertex one = call(g, "substring", "int,int");
        one.setLength(1);
        Assert.assertTrue(ForwardFixpoint.isSbCreationSeed(one));
        Assert.assertTrue(ForwardFixpoint.isSbCreationSeed(call(g, "valueOf", "char")));
        Assert.assertTrue(ForwardFixpoint.isSbCreationSeed(call(g, "valueOf", "C")));
    }

    @Test
    public void doesNotSeedOtherKnownLengthsOrKinds() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex three = call(g, "substring", "int,int");
        three.setLength(3);
        Assert.assertFalse(ForwardFixpoint.isSbCreationSeed(three));
        Assert.assertFalse(ForwardFixpoint.isSbCreationSeed(call(g, "subSequence", "int,int")));
        Assert.assertFalse(ForwardFixpoint.isSbCreationSeed(call(g, "valueOf", "java.lang.Object")));
        Assert.assertFalse(ForwardFixpoint.isSbCreationSeed(call(g, "valueOf", "int")));
        SugVertex lit = g.newVertex();
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("a");
        lit.setLength(1);
        Assert.assertFalse(ForwardFixpoint.isSbCreationSeed(lit)); // literals have their own seed rule
    }

    /** The filter: a seeded substring whose post-propagator length is not 1 (unknown or 3) is never an SB decision. */
    @Test
    public void heuristicLengthFilterRejectsNonLengthOne() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        call(g, "substring", "int,int"); // stays UNKNOWN_LENGTH
        call(g, "substring", "int,int").setLength(3);
        List<InstrumentationDecision> decisions = new SingleByteHeuristic().apply(g);
        Assert.assertTrue(decisions.isEmpty());
    }
}
