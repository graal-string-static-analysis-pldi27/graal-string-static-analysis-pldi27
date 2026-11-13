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

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * Flat delivery: the flat hand-off set the walk enters for an
 * SB atom ({@link StringTerminalHandList#isFlatHandOff}, {@code RecursiveTracking.flatHandOffEnters}).
 */
public class FlatHandOffTest {

    /** The leak-marked String entries deliberately not entered (and why: see FLAT_HANDOFF_NAMES). */
    static final Set<String> NOT_ENTERED = Set.of("intern", "equals", "compareToIgnoreCase");

    /** Every leak-marked String entry is either a flat hand-off or one of the pinned exclusions: a new leak entry decides. */
    @Test
    public void everyLeakMarkedEntryIsDecided() {
        Set<String> undecided = new TreeSet<>();
        for (StringTerminalHandList.Entry e : StringTerminalHandList.leakMarked()) {
            boolean handOff = StringTerminalHandList.isFlatHandOff(e.declaringClass(), e.name(), e.signature());
            if (handOff == NOT_ENTERED.contains(e.name())) {
                undecided.add(e.name() + "(" + e.signature() + ") handOff=" + handOff);
            }
        }
        Assert.assertEquals(Set.of(), undecided);
    }

    @Test
    public void theHandOffsAndTheExclusions() {
        String s = StringTerminalHandList.STRING;
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "transform", "Ljava/util/function/Function;"));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "formatted", "[Ljava/lang/Object;"));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "describeConstable", ""));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "split", "Ljava/lang/String;"));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "split", "Ljava/lang/String;,I"));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "split", "Ljava/lang/String;,I,Z"));
        Assert.assertTrue(StringTerminalHandList.isFlatHandOff(s, "split", "C,I,Z"));
        for (String n : NOT_ENTERED) {
            for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
                if (e.name().equals(n)) {
                    Assert.assertFalse(n, StringTerminalHandList.isFlatHandOff(s, n, e.signature()));
                }
            }
        }
        Assert.assertFalse("a return-this terminal without a leak is continued, not entered", StringTerminalHandList.isFlatHandOff(s, "substring", "I,I"));
        Assert.assertFalse("only java.lang.String", StringTerminalHandList.isFlatHandOff("java.lang.StringBuilder", "split", "C,I,Z"));
    }

    /** JDK drift: the private split helpers named in FLAT_HANDOFF_PRIVATE exist in the builder JDK's String. */
    @Test
    public void thePrivateSplitHelpersExist() {
        Set<String> found = new TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            if (Modifier.isPrivate(m.getModifiers()) && !Modifier.isStatic(m.getModifiers()) && m.getName().equals("split")) {
                found.add(m.getName() + "(" + RepPinSupport.signature(m) + ")");
            }
        }
        Assert.assertTrue(found + " contains " + StringTerminalHandList.FLAT_HANDOFF_PRIVATE, found.containsAll(StringTerminalHandList.FLAT_HANDOFF_PRIVATE));
    }

    /**
     * An SB-only seed enters every hand-off; a seed also seeded for a value-null kind enters only where that
     * kind's whitelist does not admit the member (its verdict already rejects there, so it cannot change).
     */
    @Test
    public void theGateSparesWhitelistedMembersOfSharedSeeds() {
        String s = StringTerminalHandList.STRING;
        Assert.assertTrue(RecursiveTracking.flatHandOffGate("SB", s, "toLowerCase", "Ljava/util/Locale;"));
        Assert.assertTrue(RecursiveTracking.flatHandOffGate("SB", s, "transform", "Ljava/util/function/Function;"));
        Assert.assertFalse("no SB seed", RecursiveTracking.flatHandOffGate("SV", s, "transform", "Ljava/util/function/Function;"));
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            if (!StringTerminalHandList.isFlatHandOff(s, e.name(), e.signature())) {
                continue;
            }
            boolean sv = StringViewWhitelist.isWhitelistedUsage(e.name(), s, e.signature());
            boolean lc = LazyConcatWhitelist.isWhitelisted(e.name(), s, e.signature());
            Assert.assertEquals(e.name() + "(" + e.signature() + ") SV+SB", !sv, RecursiveTracking.flatHandOffGate("SV+SB", s, e.name(), e.signature()));
            Assert.assertEquals(e.name() + "(" + e.signature() + ") LC+SB", !lc, RecursiveTracking.flatHandOffGate("LC+SB", s, e.name(), e.signature()));
        }
        Assert.assertTrue(RecursiveTracking.flatHandOffGate("SV+SB", s, "transform", "Ljava/util/function/Function;"));
        Assert.assertFalse("SV whitelists the case mapping (StringView overrides it)", RecursiveTracking.flatHandOffGate("SV+SB", s, "toLowerCase", "Ljava/util/Locale;"));
    }

    /**
     * The walk-side decision (RecursiveTracking.flatHandOffEnters minus the knob) over the seed kinds and
     * the member, and the receiver slot row it implies (entered instead of a terminal exactly on ENTER).
     */
    @Test
    public void theWalkSideDecisionAndTheReceiverSlotRow() {
        String s = StringTerminalHandList.STRING;
        String fn = "Ljava/util/function/Function;";
        Assert.assertEquals(RecursiveTracking.FH_ENTER, RecursiveTracking.flatHandOffDecision("SB", s, "transform", fn));
        Assert.assertEquals("SingleByteString declares the case mapping", RecursiveTracking.FH_NONE,
                        RecursiveTracking.flatHandOffDecision("SB", s, "toLowerCase", "Ljava/util/Locale;"));
        Assert.assertEquals(RecursiveTracking.FH_ENTER, RecursiveTracking.flatHandOffDecision("SV+SB", s, "transform", fn));
        Assert.assertEquals(RecursiveTracking.FH_ENTER, RecursiveTracking.flatHandOffDecision("LC+SB", s, "split", "Ljava/lang/String;"));
        Assert.assertEquals("SV whitelists the case mapping, SBS declares it", RecursiveTracking.FH_NONE,
                        RecursiveTracking.flatHandOffDecision("SV+SB", s, "toLowerCase", "Ljava/util/Locale;"));
        Assert.assertEquals("SV whitelists offsetByCodePoints, SBS declares it", RecursiveTracking.FH_NONE,
                        RecursiveTracking.flatHandOffDecision("SV+SB", s, "offsetByCodePoints", "I,I"));
        for (String h : new String[]{"SB", "SV+SB", "LC+SB"}) {
            for (String[] m : new String[][]{{"toUpperCase", ""}, {"toUpperCase", "Ljava/util/Locale;"}, {"toLowerCase", ""}, {"toLowerCase", "Ljava/util/Locale;"},
                            {"offsetByCodePoints", "I,I"}}) {
                Assert.assertTrue(m[0] + "(" + m[1] + ") declared by SBS", RecursiveTracking.sbsDeclares(m[0], m[1]));
                Assert.assertEquals(h + " " + m[0] + "(" + m[1] + ")", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision(h, s, m[0], m[1]));
            }
        }
        Assert.assertFalse("transform stays a hand-off", RecursiveTracking.sbsDeclares("transform", fn));
        Assert.assertEquals("no SB seed", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision("SV", s, "transform", fn));
        Assert.assertEquals("no SB seed", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision("LC", s, "split", "Ljava/lang/String;"));
        Assert.assertEquals("not a hand-off", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision("SB", s, "length", ""));
        Assert.assertEquals("not a hand-off", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision("SB", s, "intern", ""));
        Assert.assertEquals("only java.lang.String", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision("SB", "java.lang.StringBuilder", "split", "C,I,Z"));
        Assert.assertEquals("no seed kinds", RecursiveTracking.FH_NONE, RecursiveTracking.flatHandOffDecision(null, s, "transform", fn));
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            for (String h : new String[]{"SB", "SV+SB", "LC+SB", "SV", "LC"}) {
                int d = RecursiveTracking.flatHandOffDecision(h, s, e.name(), e.signature());
                boolean considered = h.contains("SB") && StringTerminalHandList.isFlatHandOff(s, e.name(), e.signature()) &&
                                !RecursiveTracking.sbsDeclares(e.name(), e.signature());
                int want = !considered ? RecursiveTracking.FH_NONE
                                : RecursiveTracking.flatHandOffGate(h, s, e.name(), e.signature()) ? RecursiveTracking.FH_ENTER : RecursiveTracking.FH_UNDELIVERED;
                Assert.assertEquals(h + " " + e.name() + "(" + e.signature() + ")", want, d);
            }
        }
        Assert.assertEquals(StringAtoms.SlotRow.TERMINAL, RecursiveTracking.flatSlotRow(0, true, false, false));
        Assert.assertEquals("an entered hand-off's receiver", StringAtoms.SlotRow.ENTER, RecursiveTracking.flatSlotRow(0, true, true, false));
        Assert.assertEquals(StringAtoms.SlotRow.ENTER, RecursiveTracking.flatSlotRow(0, false, false, false));
        Assert.assertEquals(StringAtoms.SlotRow.ENTER, RecursiveTracking.flatSlotRow(1, true, true, false));
        Assert.assertEquals(StringAtoms.SlotRow.CONCAT_OPERAND, RecursiveTracking.flatSlotRow(1, true, true, true));
    }

    @Test
    public void undeliveredLinesNameOnlyAdmittedSeeds() {
        RecursiveTracking.FLAT_UNDELIVERED.clear();
        try {
            RecursiveTracking.FLAT_UNDELIVERED.computeIfAbsent("toLowerCase(Ljava/util/Locale;)", k -> new java.util.HashSet<>()).addAll(Set.of("A#m@1", "B#m@2"));
            RecursiveTracking.FLAT_UNDELIVERED.computeIfAbsent("toUpperCase(Ljava/util/Locale;)", k -> new java.util.HashSet<>()).add("C#m@3");
            Assert.assertEquals(java.util.List.of("# FLAT_HANDOFF_UNDELIVERED toLowerCase(Ljava/util/Locale;) 1"), RecursiveTracking.flatUndeliveredProfileLines(Set.of("A#m@1")));
        } finally {
            RecursiveTracking.FLAT_UNDELIVERED.clear();
        }
    }
}
