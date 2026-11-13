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

import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * The flat hand-off closure for the SB rep. A flat
 * hand-off an SB seed shares with a value-null kind is left unentered when that kind whitelists it
 * ({@code RecursiveTracking.flatHandOffGate}: FH_UNDELIVERED); it cannot happen when SingleByteString declares the member
 * itself ({@code RecursiveTracking.sbsDeclares}: FH_NONE). This pins that every flat hand-off SV or LC whitelists is
 * declared by SingleByteString, so FH_UNDELIVERED is unreachable; a new whitelist row (or hand-off) without a matching
 * SBS override fails here.
 */
public class SingleByteHandOffClosureTest {

    @Test
    public void everyWhitelistedHandOffIsDeclaredBySbs() {
        String s = StringTerminalHandList.STRING;
        Set<String> members = new TreeSet<>();
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            members.add(e.name() + "\t" + e.signature());
        }
        for (String p : StringTerminalHandList.FLAT_HANDOFF_PRIVATE) {
            members.add(p.substring(0, p.indexOf('(')) + "\t" + p.substring(p.indexOf('(') + 1, p.length() - 1));
        }
        Set<String> whitelisted = new TreeSet<>();
        Set<String> missing = new TreeSet<>();
        for (String m : members) {
            String name = m.substring(0, m.indexOf('\t'));
            String sig = m.substring(m.indexOf('\t') + 1);
            if (!StringTerminalHandList.isFlatHandOff(s, name, sig)) {
                continue;
            }
            boolean sv = StringViewWhitelist.isWhitelistedUsage(name, s, sig);
            boolean lc = LazyConcatWhitelist.isWhitelisted(name, s, sig);
            if (sv || lc) {
                whitelisted.add(name + "(" + sig + ")");
                if (!RecursiveTracking.sbsDeclares(name, sig)) {
                    missing.add(name + "(" + sig + ")" + (sv ? " SV" : "") + (lc ? " LC" : ""));
                }
            }
            for (String h : new String[]{"SV+SB", "LC+SB", "SV+LC+SB", "SB"}) {
                Assert.assertNotEquals(h + " " + name + "(" + sig + ")", RecursiveTracking.FH_UNDELIVERED, RecursiveTracking.flatHandOffDecision(h, s, name, sig));
            }
        }
        Assert.assertEquals("flat hand-offs a value-null kind whitelists without a SingleByteString override", Set.of(), missing);
        /* Non-vacuous: today's set (the five members SV whitelists). */
        Assert.assertEquals(Set.of("offsetByCodePoints(I,I)", "toLowerCase()", "toLowerCase(Ljava/util/Locale;)", "toUpperCase()", "toUpperCase(Ljava/util/Locale;)"), whitelisted);
    }

    /** The derived rule reads the rep class: a member SBS does not declare stays a hand-off (entered for an SB seed). */
    @Test
    public void undeclaredHandOffsStayEntered() {
        String s = StringTerminalHandList.STRING;
        Assert.assertFalse(RecursiveTracking.sbsDeclares("transform", "Ljava/util/function/Function;"));
        Assert.assertFalse(RecursiveTracking.sbsDeclares("split", "Ljava/lang/String;"));
        Assert.assertFalse(RecursiveTracking.sbsDeclares("split", "C,I,Z"));
        Assert.assertTrue(RecursiveTracking.sbsDeclares("equals", "Ljava/lang/Object;"));
        Assert.assertEquals(RecursiveTracking.FH_ENTER, RecursiveTracking.flatHandOffDecision("SV+SB", s, "transform", "Ljava/util/function/Function;"));
    }
}
