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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * The child's EXACT_RECV proof predicate, its profile line, the knob defaults and the hidden-sink
 * key rule. The lowering shapes are pinned by {@code RepDispatchAccountingTest#exactFirstIfIsDispatch} (accounting)
 * and checked in images (function diff vs stock).
 */
public class ExactRecvProofTest {

    private static final String CS = "java.lang.CharSequence";

    private static ExactReceiverSites.Facts facts(List<String> types, List<String> callees) {
        return new ExactReceiverSites.Facts(CS, true, true, true, true, 1, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", false, true, false, false, false, types, callees);
    }

    @Test
    public void proofNeedsExactlyStringAndOneStringCallee() {
        List<String> one = List.of("java.lang.String#charAt(I)C");
        Assert.assertEquals(ExactReceiverSites.Verdict.PROVEN, ExactReceiverSites.verdict(facts(List.of("java.lang.String"), one)));
        Assert.assertEquals("the scan leaves out String subtypes; any other listed type is a foreign type", ExactReceiverSites.Verdict.OTHER_TYPES,
                        ExactReceiverSites.verdict(facts(List.of("com.oracle.svm.core.stringrep.SomeHelper", "java.lang.String"), one)));
        Assert.assertEquals("another CharSequence: stock stays virtual", ExactReceiverSites.Verdict.OTHER_TYPES,
                        ExactReceiverSites.verdict(facts(List.of("java.lang.String", "java.lang.StringBuilder"), one)));
        Assert.assertEquals(ExactReceiverSites.Verdict.EMPTY_STATE, ExactReceiverSites.verdict(facts(List.of(), one)));
        Assert.assertEquals(ExactReceiverSites.Verdict.SATURATED, ExactReceiverSites.verdict(facts(null, one)));
        Assert.assertEquals(ExactReceiverSites.Verdict.CALLEES_NOT_ONE_STRING,
                        ExactReceiverSites.verdict(facts(List.of("java.lang.String"), List.of("java.lang.String#charAt(I)C", "java.lang.StringBuilder#charAt(I)C"))));
        Assert.assertEquals(ExactReceiverSites.Verdict.CALLEES_NOT_ONE_STRING, ExactReceiverSites.verdict(facts(List.of("java.lang.String"), List.of())));
    }

    @Test
    public void proofNeedsTheParentsKey() {
        List<String> t = List.of("java.lang.String");
        List<String> c = List.of("java.lang.String#charAt(I)C");
        Assert.assertEquals(ExactReceiverSites.Verdict.HIDDEN_CLASS,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, true, true, 1, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", true, true, false, false, false, t,
                                        c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.INLINED_BEFORE_ANALYSIS,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, true, true, 1, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", false, true, false, true, false, t,
                                        c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.KEY_NOT_UNIQUE,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, true, true, 2, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", false, true, false, false, false,
                                        t, c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.BC_TARGET_MISMATCH,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, true, true, 1, new String[]{"java.lang.String", "charAt", "(I)C"}, "charAt", "(I)C", false, true, false,
                                        false, false, t,
                                        c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.CUSTOM_GRAPH,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, true, true, 1, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", false, true, true, false, false, t,
                                        c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.NOT_VIRTUAL,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts(CS, true, true, false, true, 1, new String[]{CS, "charAt", "(I)C"}, "charAt", "(I)C", false, true, false, false, false,
                                        t, c)));
        Assert.assertEquals(ExactReceiverSites.Verdict.NOT_SUPER_OWNER,
                        ExactReceiverSites.verdict(new ExactReceiverSites.Facts("java.lang.String", false, true, true, true, 1, null, "charAt", "(I)C", false, true, false, false, false, t, c)));
    }

    @Test
    public void liveRepArmIsTheParentsOverrideRule() {
        Assert.assertTrue("StringView overrides charAt: a live arm (super-chain)", ExactReceiverSites.hasLiveRepArm("SV", "charAt(I)C"));
        Assert.assertTrue(ExactReceiverSites.hasLiveRepArm("EXACT,SBS,SV", "charAt(I)C"));
        Assert.assertFalse("SingleByteString inherits length(): no arm (super-collapsed)", ExactReceiverSites.hasLiveRepArm("SBS", "length()I"));
        Assert.assertFalse(ExactReceiverSites.hasLiveRepArm("EXACT,SBS", "length()I"));
        Assert.assertTrue("unknown rep: conservative", ExactReceiverSites.hasLiveRepArm("NO_SUCH_REP", "length()I"));
        Assert.assertTrue("not a member: conservative", ExactReceiverSites.hasLiveRepArm("SBS", "noSuchMethod()V"));
        Assert.assertTrue(ExactReceiverSites.hasLiveRepArm("", "length()I"));
    }

    @Test
    public void repListKeysSkipUnknownKtAndRedirect() {
        List<InstrumentationDecision> d = List.of(
                        dec("a#m()V@1", OptimizationType.INLINE_CACHE, "SV"),
                        dec("a#m()V@2", OptimizationType.INLINE_CACHE, "UNKNOWN"),
                        dec("a#m()V@3", OptimizationType.INLINE_CACHE, "UNPROVEN"),
                        dec("a#m()V@4", OptimizationType.INLINE_CACHE, "KT:SV"),
                        dec("a#m()V@5", OptimizationType.INLINE_CACHE, "EXACT,SV"),
                        dec("a#m()V@5", OptimizationType.EQUALS_MATRIX, "REDIRECT"),
                        dec("a#m()V@6", OptimizationType.INLINE_CACHE, "EXACT,SBS,SV"));
        Assert.assertEquals(java.util.Set.of("a#m()V@1", "a#m()V@6"), ExactReceiverSites.repListKeys(d));
    }

    private static InstrumentationDecision dec(String key, OptimizationType t, String v) {
        SugVertex sv = new SugVertex(1);
        sv.setSourceLocation(key);
        return new InstrumentationDecision(sv, t, v);
    }

    @Test
    public void loaderReadsExactRecvLines() throws IOException {
        Path p = Files.createTempFile("c98xd-s2", ".txt");
        try {
            Files.writeString(p, "a.B#m(Ljava/lang/CharSequence;)C@3 INLINE_CACHE SV\na.B#m(Ljava/lang/CharSequence;)C@3 EXACT_RECV STRING\n");
            RepresentationProfile prof = RepresentationProfileLoader.load(p.toString());
            Assert.assertTrue(prof.hasExactReceiver("a.B#m(Ljava/lang/CharSequence;)C@3"));
            Assert.assertFalse(prof.hasExactReceiver("a.B#m(Ljava/lang/CharSequence;)C@4"));
            Assert.assertEquals("SV", prof.getEntry("a.B#m(Ljava/lang/CharSequence;)C@3", OptimizationType.INLINE_CACHE).getVariant());
            Files.writeString(p, "a.B#m()C@3 EXACT_RECV SV\n");
            Assert.assertThrows(IllegalArgumentException.class, () -> RepresentationProfileLoader.load(p.toString()));
        } finally {
            Files.deleteIfExists(p);
        }
    }

    @Test
    public void knobDefaults() {
        Assert.assertEquals("the original IC chain form (no exact-first test)", 0, InlineCacheTrivialMethodNodePlugin.EXACT_FIRST);
        Assert.assertEquals("the exact-receiver CHECK probe is debug only", 0, InlineCacheTrivialMethodNodePlugin.EXACT_FIRST_SUPER_CHECK);
    }

    @Test
    public void hiddenSinkKeys() {
        Assert.assertTrue(ForwardFixpoint.isHiddenSinkKey("io.quarkus.qute.SectionBlock$$Lambda/0x0000000801234#apply(Ljava/lang/Object;)Ljava/lang/Object;@5"));
        Assert.assertTrue(ForwardFixpoint.isHiddenSinkKey("a.B$$Lambda#run()V@1"));
        Assert.assertFalse(ForwardFixpoint.isHiddenSinkKey("io.quarkus.qute.SectionBlock#collapseGroup(Ljava/util/List;)V@67"));
        Assert.assertFalse(ForwardFixpoint.isHiddenSinkKey(null));
        Assert.assertEquals("appended last (MIRROR_ARG_NO_SITE after it)", ContainerTables.RTrackRefusal.values().length - 2, ContainerTables.RTrackRefusal.HIDDEN_SINK.ordinal());
    }
}
