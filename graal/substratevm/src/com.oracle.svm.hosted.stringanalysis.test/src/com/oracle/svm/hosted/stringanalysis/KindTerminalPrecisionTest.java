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

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

/**
 * Kind-terminal precision ({@link LazyOperandPairing}): the concat group lists a lazy-operand kind only when one of its outers
 * stays stock; the pairs of the unlisted inners round-trip through the profile and the parent's two contract checks.
 */
public class KindTerminalPrecisionTest {

    private static SugVertex concat(StringUtilizationGraph g, String key, int dyn) {
        SugVertex v = g.newVertex();
        v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        v.setSourceLocation(key);
        v.setEnclosingClassName("TestUserClass");
        v.setDynamicOperandCount(dyn);
        return v;
    }

    private static InstrumentationDecision lc(SugVertex v, String variant) {
        return new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, variant);
    }

    /** concatMix4String's shape: the inners' only outer is an admitted lazy concat -> no listing, one pair per inner. */
    @Test
    public void allOutersLazyUnlistsAndPairs() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in1 = concat(g, "T#m@16", 5);
        SugVertex in2 = concat(g, "T#m@38", 5);
        SugVertex outer = concat(g, "T#m@94", 4);
        in1.addLazyOperandSite("T#m@94");
        in2.addLazyOperandSite("T#m@94");
        List<InstrumentationDecision> v = List.of(lc(in1, "ARRAY_LAZY"), lc(in2, "ARRAY_LAZY"), lc(outer, "FIXED4"));
        LazyOperandPairing.Result r = LazyOperandPairing.compute(v, true, false);
        Assert.assertEquals(Set.of(), r.listedKinds());
        Assert.assertEquals(Set.of("ARRAY_LAZY"), r.pairedOnlyKinds());
        Assert.assertEquals(Map.of("T#m@16", Set.of("T#m@94"), "T#m@38", Set.of("T#m@94")), r.pairs());
        Assert.assertEquals(List.of("T#m@16 LAZY_PAIR T#m@94", "T#m@38 LAZY_PAIR T#m@94"), LazyOperandPairing.profileLines(r));
        Assert.assertEquals("precise", r.mode());
    }

    /** One stock outer (not a validated lazy decision) lists the kind; a listed kind writes no pair, even for a fully-lazy inner. */
    @Test
    public void stockOuterListsKindAndDropsItsPairs() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex inLazy = concat(g, "T#a@1", 3);
        SugVertex inMixed = concat(g, "T#b@1", 3);
        SugVertex outer = concat(g, "T#o@1", 2);
        inLazy.addLazyOperandSite("T#o@1");
        inMixed.addLazyOperandSite("T#o@1");
        inMixed.addLazyOperandSite("T#stock@1"); // no decision: the outer stays stock
        List<InstrumentationDecision> v = List.of(lc(inLazy, "THREE_WAY"), lc(inMixed, "THREE_WAY"), lc(outer, "ROPE"));
        LazyOperandPairing.Result r = LazyOperandPairing.compute(v, true, false);
        Assert.assertEquals(Set.of("THREE_WAY"), r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
        Assert.assertTrue(r.pairedOnlyKinds().isEmpty());

        // another kind paired next to the listed one
        SugVertex inF4 = concat(g, "T#c@1", 4);
        inF4.addLazyOperandSite("T#o@1");
        List<InstrumentationDecision> v2 = new ArrayList<>(v);
        v2.add(lc(inF4, "FIXED4"));
        LazyOperandPairing.Result r2 = LazyOperandPairing.compute(v2, true, false);
        Assert.assertEquals(Set.of("THREE_WAY"), r2.listedKinds());
        Assert.assertEquals(Map.of("T#c@1", Set.of("T#o@1")), r2.pairs());
    }

    /** An outer the parent would not lower lazily (no shape, a non-minting variant, a String.concat call) is not kept. */
    @Test
    public void keptOuterPredictsTheParentLowering() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        Assert.assertTrue(LazyOperandPairing.isKeptLazyOuter(lc(concat(g, "T#k@1", 2), "ROPE")));
        Assert.assertFalse(LazyOperandPairing.isKeptLazyOuter(lc(concat(g, "T#k@2", 0), "ROPE"))); // invoke-based: never replaced
        Assert.assertFalse(LazyOperandPairing.isKeptLazyOuter(lc(concat(g, "T#k@3", 1), "ROPE"))); // one part: no lazy shape
        Assert.assertFalse(LazyOperandPairing.isKeptLazyOuter(lc(concat(g, "T#k@4", 2), "NOT_A_REP")));
        Assert.assertFalse(LazyOperandPairing.isKeptLazyOuter(null));
        SugVertex sc = g.newVertex();
        sc.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sc.setSourceLocation("T#k@5");
        Assert.assertFalse(LazyOperandPairing.isKeptLazyOuter(lc(sc, "ROPE")));

        // an inner whose outer does not mint is listed
        SugVertex in = concat(g, "T#i@1", 3);
        SugVertex bad = concat(g, "T#bad@1", 1);
        in.addLazyOperandSite("T#bad@1");
        LazyOperandPairing.Result r = LazyOperandPairing.compute(List.of(lc(in, "THREE_WAY"), lc(bad, "ROPE")), true, false);
        Assert.assertEquals(Set.of("THREE_WAY"), r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
    }

    /** The revert (ktprecise=0) and an image with deoptimization support: image-wide listing, no pairs. */
    @Test
    public void revertAndDeoptListImageWide() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in = concat(g, "T#m@16", 5);
        SugVertex outer = concat(g, "T#m@94", 4);
        in.addLazyOperandSite("T#m@94");
        List<InstrumentationDecision> v = List.of(lc(in, "ARRAY_LAZY"), lc(outer, "FIXED4"));
        for (boolean[] pd : new boolean[][]{{false, false}, {true, true}, {false, true}}) {
            LazyOperandPairing.Result r = LazyOperandPairing.compute(v, pd[0], pd[1]);
            Assert.assertEquals(Set.of("ARRAY_LAZY"), r.listedKinds());
            Assert.assertTrue(r.pairs().isEmpty());
            Assert.assertTrue(r.mode().startsWith("image-wide"));
        }
        // no lazy operand at all: nothing listed, nothing paired
        Assert.assertTrue(LazyOperandPairing.compute(List.of(lc(outer, "FIXED4")), true, false).listedKinds().isEmpty());
    }

    /** The pairs round-trip through dumpProfile + the loader; the parent's checks read only the profile. */
    @Test
    public void pairsRoundTripAndParentContract() throws Exception {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in = concat(g, "T#m@16", 5);
        SugVertex mid = concat(g, "T#m@60", 3);
        SugVertex outer = concat(g, "T#m@94", 4);
        in.addLazyOperandSite("T#m@60");
        mid.addLazyOperandSite("T#m@94");
        List<InstrumentationDecision> v = List.of(lc(in, "ARRAY_LAZY"), lc(mid, "THREE_WAY"), lc(outer, "FIXED4"));
        LazyOperandPairing.Result r = LazyOperandPairing.compute(v, true, false);
        Assert.assertEquals(Map.of("T#m@16", Set.of("T#m@60"), "T#m@60", Set.of("T#m@94")), r.pairs());
        Path p = Files.createTempFile("kt-precision", ".txt");
        try {
            StringAnalysisFeature.dumpProfile(v, p.toString(), LazyOperandPairing.profileLines(r));
            RepresentationProfile prof = RepresentationProfileLoader.load(p.toString());
            Assert.assertEquals(3, prof.getTotalCount()); // the pair lines are not entries
            Assert.assertTrue(prof.pairedOutersLowered("T#m@16"));
            Assert.assertTrue(prof.pairedOutersLowered("T#m@60"));
            Assert.assertTrue(prof.pairedOutersLowered("T#m@94")); // no pair: unconstrained
            Assert.assertTrue(prof.isPairedOuter("T#m@60"));
            Assert.assertTrue(prof.isPairedOuter("T#m@94"));
            Assert.assertFalse(prof.isPairedOuter("T#m@16"));

            // an outer missing from the profile (e.g. a hand-edited profile): its inner is lowered stock
            List<String> lines = new ArrayList<>(Files.readAllLines(p));
            lines.removeIf(l -> l.startsWith("T#m@94 LAZY_CONCAT"));
            Files.write(p, lines);
            RepresentationProfile cut = RepresentationProfileLoader.load(p.toString());
            Assert.assertFalse(cut.pairedOutersLowered("T#m@60"));
            Assert.assertTrue(cut.pairedOutersLowered("T#m@16"));
            Assert.assertTrue(cut.isPairedOuter("T#m@60")); // and the plugin then fails the build at @60 (contract 2)
        } finally {
            Files.deleteIfExists(p);
        }
    }

    /** The two constructors without pairs: unconstrained. */
    @Test
    public void profileWithoutPairs() {
        RepresentationProfile prof = new RepresentationProfile(Map.of("T#m@1", new ProfileEntry("T#m@1", OptimizationType.LAZY_CONCAT, "ROPE")));
        Assert.assertTrue(prof.pairedOutersLowered("T#m@1"));
        Assert.assertFalse(prof.isPairedOuter("T#m@1"));
        Assert.assertTrue(Arrays.asList(LazyOperandPairing.PAIR_TYPE).contains("LAZY_PAIR"));
    }

    /** A self-loop ({@code s = s + x}: the inner's outer is its own key) lists the kind and writes no pair. */
    @Test
    public void selfLoopListsKind() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex loop = concat(g, "T#m@5", 3);
        loop.addLazyOperandSite("T#m@5");
        InstrumentationDecision loopD = lc(loop, "THREE_WAY");
        Set<String> kind = Set.of(HeuristicOrchestrator.repTypeOf(loopD));
        LazyOperandPairing.Result r = LazyOperandPairing.compute(List.of(loopD), true, false);
        Assert.assertEquals(kind, r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
        // also next to a kept lazy outer
        SugVertex outer = concat(g, "T#m@9", 2);
        loop.addLazyOperandSite("T#m@9");
        r = LazyOperandPairing.compute(List.of(loopD, lc(outer, "ROPE")), true, false);
        Assert.assertEquals(kind, r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
    }

    /**
     * Two LAZY_CONCAT decisions of one key: only the first (the one dumpProfile writes) counts. A second
     * inner decision is not the dumped one, so it lists its kind; a second outer decision does not change the kept outer.
     */
    @Test
    public void sameKeyFirstDecisionCounts() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex outer = concat(g, "T#o@1", 2);
        SugVertex outerDup = concat(g, "T#o@1", 1); // a non-minting second decision of the outer's key
        SugVertex in = concat(g, "T#i@1", 4);
        in.addLazyOperandSite("T#o@1");
        LazyOperandPairing.Result r = LazyOperandPairing.compute(List.of(lc(outer, "ROPE"), lc(outerDup, "ROPE"), lc(in, "FIXED4")), true, false);
        Assert.assertEquals(Set.of(), r.listedKinds());
        Assert.assertEquals(Map.of("T#i@1", Set.of("T#o@1")), r.pairs());
        // the order flipped: the first decision of the outer's key does not mint -> not kept -> listed
        r = LazyOperandPairing.compute(List.of(lc(outerDup, "ROPE"), lc(outer, "ROPE"), lc(in, "FIXED4")), true, false);
        Assert.assertEquals(Set.of("FIXED4"), r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
        // a second inner decision of one key (not the dumped one) lists its kind, and the listed kind drops the first's pair
        SugVertex inDup = concat(g, "T#i@1", 4);
        inDup.addLazyOperandSite("T#o@1");
        r = LazyOperandPairing.compute(List.of(lc(outer, "ROPE"), lc(in, "FIXED4"), lc(inDup, "FIXED4")), true, false);
        Assert.assertEquals(Set.of("FIXED4"), r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
    }

    /**
     * A lazy-operand site reached only through an internal call (candidate -> {@code <init>} -> a
     * non-copying concat) is recorded on the candidate (LazyConcatHeuristic.validateUsages). Recorded on the
     * {@code <init>} vertex instead, the candidate would have no site and its kind would stay unlisted at a stock outer.
     */
    @Test
    public void internalCallSiteRecordedOnCandidate() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        List<UsageTag> tags = new ArrayList<>();
        SugVertex in = concat(g, "T#m@2", 2);
        in.setMethodName("makeConcatWithConstants");
        in.setConcatRecipe("string\u0001\u0001");
        in.setConcatOperandKinds("PP");
        String[] texts = {"string", null, null};
        for (int i = 0; i < texts.length; i++) {
            SugVertex op = g.newVertex();
            op.setNodeType(texts[i] == null ? SugNodeType.VARIABLE : SugNodeType.STRING_LITERAL);
            if (texts[i] != null) {
                op.setLiteralText(texts[i]);
                op.setLength(texts[i].length());
            }
            g.addEdge(op, in, i % 2 == 0 ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT, i);
        }
        SugVertex init = g.newVertex();
        init.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        init.setMethodName("<init>");
        init.setDeclaringClass("java.lang.Object");
        init.setSourceLocation("T#m@7");
        SugVertex outer = concat(g, "T#stock@9", 0);
        outer.markScfNoCopy();
        tags.add(new UsageTag(init, UsageRole.RECEIVER, -1));
        tags.add(new UsageTag(outer, UsageRole.NONE, -1));
        for (SugVertex v : g.getVertices()) {
            v.setUsageTags(new BitSet());
        }
        in.getUsageTags().set(0);
        init.getUsageTags().set(1);
        g.setUsageTags(tags);
        g.setUsageSourceBuilt();

        List<InstrumentationDecision> ds = new LazyConcatHeuristic().apply(g);
        List<InstrumentationDecision> inner = ds.stream().filter(d -> d.getCandidate() == in).collect(Collectors.toList());
        Assert.assertEquals(1, inner.size());
        Assert.assertEquals("THREE_WAY", inner.get(0).getVariant());
        Assert.assertEquals(Set.of("T#stock@9"), in.getLazyOperandSites());
        Assert.assertTrue(init.getLazyOperandSites().isEmpty());
        // the outer stays stock (no lazy decision): the kind is listed, no pair
        LazyOperandPairing.Result r = LazyOperandPairing.compute(inner, true, false);
        Assert.assertEquals(Set.of("THREE_WAY"), r.listedKinds());
        Assert.assertTrue(r.pairs().isEmpty());
    }

    /**
     * The dump writes the IC-time pairs (one computation); an SV-only or SB-only dump (no LAZY_CONCAT
     * decision) writes no pair; no IC-time result (kind-terminal off) writes no pair.
     */
    @Test
    public void dumpLinesFromTheOneComputation() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in = concat(g, "T#m@16", 5);
        SugVertex outer = concat(g, "T#m@94", 4);
        in.addLazyOperandSite("T#m@94");
        SugVertex sv = g.newVertex();
        sv.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sv.setSourceLocation("T#m@3");
        InstrumentationDecision svD = new InstrumentationDecision(sv, OptimizationType.STRING_VIEW, null);
        InstrumentationDecision sbD = new InstrumentationDecision(sv, OptimizationType.SINGLE_BYTE, null);
        List<InstrumentationDecision> v = List.of(lc(in, "ARRAY_LAZY"), lc(outer, "FIXED4"), svD, sbD);
        LazyOperandPairing.Result r = LazyOperandPairing.compute(v, true, false);
        Assert.assertEquals(LazyOperandPairing.profileLines(r), LazyOperandPairing.dumpLines(r, v));
        Assert.assertEquals(List.of("T#m@16 LAZY_PAIR T#m@94"), LazyOperandPairing.dumpLines(r, v));
        Assert.assertTrue(LazyOperandPairing.dumpLines(r, List.of(svD)).isEmpty()); // StringViewOnly dump
        Assert.assertTrue(LazyOperandPairing.dumpLines(r, List.of(sbD)).isEmpty()); // SingleByteOnly dump
        Assert.assertTrue(LazyOperandPairing.dumpLines(null, v).isEmpty());
        // SV-only / SB-only orchestrator inputs carry no LAZY_CONCAT decision: the IC-time computation has no pair either
        Assert.assertTrue(LazyOperandPairing.compute(List.of(svD), true, false).pairs().isEmpty());
        Assert.assertTrue(LazyOperandPairing.compute(List.of(sbD), true, false).pairs().isEmpty());
    }
}
