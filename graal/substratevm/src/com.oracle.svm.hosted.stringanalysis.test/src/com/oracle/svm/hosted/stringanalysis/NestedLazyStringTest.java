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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

/**
 * Nested lazy strings: {@code lc.lazyoperand} 2 (LS_NESTED_INNER) and 3 (LS_NESTED_OUTER) refuse an LS value as an operand of
 * another LS site ({@code HeuristicOrchestrator.nestedLsRefusals}); an LS operand of a stock concat stays admitted.
 */
public class NestedLazyStringTest {

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

    /** The refused keys with the refusal name (the reason's first word). */
    private static Map<String, String> refused(List<InstrumentationDecision> ds, int mode) {
        return HeuristicOrchestrator.nestedLsRefusals(ds, mode).entrySet().stream().collect(Collectors.toMap(e -> e.getKey().getSourceLocation(), e -> e.getValue().split(" ")[0]));
    }

    private static List<InstrumentationDecision> kept(List<InstrumentationDecision> ds, int mode) {
        Map<InstrumentationDecision, String> r = HeuristicOrchestrator.nestedLsRefusals(ds, mode);
        List<InstrumentationDecision> out = new ArrayList<>();
        for (InstrumentationDecision d : ds) {
            if (!r.containsKey(d)) {
                out.add(d);
            }
        }
        return out;
    }

    private static final String IN = LazyConcatHeuristic.LS_NESTED_INNER;
    private static final String OUT = LazyConcatHeuristic.LS_NESTED_OUTER;

    /** concatMix4String: four ARRAY_LAZY inners of one FIXED4 outer. */
    private static List<InstrumentationDecision> mix4(StringUtilizationGraph g) {
        List<InstrumentationDecision> ds = new ArrayList<>();
        for (int bci : new int[]{16, 38, 60, 82}) {
            SugVertex in = concat(g, "SC#concatMix4String@" + bci, 5);
            in.addLazyOperandSite("SC#concatMix4String@94");
            ds.add(lc(in, "ARRAY_LAZY"));
        }
        ds.add(lc(concat(g, "SC#concatMix4String@94", 4), "FIXED4"));
        return ds;
    }

    @Test
    public void mix4PerMode() {
        List<InstrumentationDecision> ds = mix4(new StringUtilizationGraph());
        Assert.assertEquals(Map.of(), refused(ds, 0));
        Assert.assertEquals(Map.of(), refused(ds, 1));
        Assert.assertEquals(Map.of("SC#concatMix4String@16", IN, "SC#concatMix4String@38", IN, "SC#concatMix4String@60", IN, "SC#concatMix4String@82", IN), refused(ds, 2));
        Assert.assertEquals(Map.of("SC#concatMix4String@94", OUT), refused(ds, 3));
        // the KT concat group then has no pair: mode 2 keeps only the outer (no lazy operand at all), mode 3 keeps the
        // inners as operands of a stock concat (their kind is listed, as for any stock outer)
        LazyOperandPairing.Result r2 = LazyOperandPairing.compute(kept(ds, 2), true, false);
        Assert.assertTrue(r2.pairs().isEmpty());
        Assert.assertEquals(Set.of(), r2.listedKinds());
        LazyOperandPairing.Result r3 = LazyOperandPairing.compute(kept(ds, 3), true, false);
        Assert.assertTrue(r3.pairs().isEmpty());
        Assert.assertEquals(Set.of("ARRAY_LAZY"), r3.listedKinds());
        // mode 1: paired
        Assert.assertEquals(4, LazyOperandPairing.compute(ds, true, false).pairs().size());
    }

    /** A lazy operand of an ordinary (stock) concat stays admitted in every mode. */
    @Test
    public void stockOuterKeepsInner() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in = concat(g, "T#m@1", 3);
        in.addLazyOperandSite("T#stock@9"); // no LAZY_CONCAT decision at the outer
        SugVertex nonMinting = concat(g, "T#n@1", 3);
        nonMinting.addLazyOperandSite("T#nm@9");
        SugVertex nm = concat(g, "T#nm@9", 0); // a LAZY_CONCAT decision the parent does not lower lazily (dyn 0)
        List<InstrumentationDecision> ds = List.of(lc(in, "THREE_WAY"), lc(nonMinting, "THREE_WAY"), lc(nm, "ROPE"));
        for (int mode = 0; mode <= 3; mode++) {
            Assert.assertEquals("mode " + mode, Map.of(), refused(ds, mode));
        }
    }

    /** Multi-level chains: no LS-in-LS edge is left, and an inner whose outer was refused stays (an operand of a stock concat). */
    @Test
    public void chains() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex a = concat(g, "T#a@1", 3);
        SugVertex b = concat(g, "T#b@1", 3);
        SugVertex c = concat(g, "T#c@1", 3);
        SugVertex d = concat(g, "T#d@1", 3);
        a.addLazyOperandSite("T#b@1");
        b.addLazyOperandSite("T#c@1");
        List<InstrumentationDecision> abc = List.of(lc(c, "THREE_WAY"), lc(a, "THREE_WAY"), lc(b, "THREE_WAY"));
        Assert.assertEquals(Map.of("T#b@1", IN), refused(abc, 2));
        Assert.assertEquals(Map.of("T#b@1", OUT), refused(abc, 3));
        c.addLazyOperandSite("T#d@1");
        List<InstrumentationDecision> abcd = List.of(lc(d, "THREE_WAY"), lc(b, "THREE_WAY"), lc(c, "THREE_WAY"), lc(a, "THREE_WAY"));
        Assert.assertEquals(Map.of("T#c@1", IN, "T#a@1", IN), refused(abcd, 2));
        Assert.assertEquals(Map.of("T#b@1", OUT, "T#d@1", OUT), refused(abcd, 3));
        // order-independent
        List<InstrumentationDecision> rev = new ArrayList<>(abcd);
        java.util.Collections.reverse(rev);
        Assert.assertEquals(refused(abcd, 2), refused(rev, 2));
        Assert.assertEquals(refused(abcd, 3), refused(rev, 3));
    }

    /** The self-loop (s = s + "," + x: the site is its own outer) and a two-site loop are refused in modes 2 and 3. */
    @Test
    public void loopsRefused() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex loop = concat(g, "T#m@5", 3);
        loop.addLazyOperandSite("T#m@5");
        SugVertex x = concat(g, "T#x@1", 3);
        SugVertex y = concat(g, "T#y@1", 3);
        x.addLazyOperandSite("T#y@1");
        y.addLazyOperandSite("T#x@1");
        SugVertex z = concat(g, "T#z@1", 3); // a plain inner of the loop site
        z.addLazyOperandSite("T#m@5");
        List<InstrumentationDecision> ds = List.of(lc(loop, "THREE_WAY"), lc(x, "THREE_WAY"), lc(y, "THREE_WAY"), lc(z, "THREE_WAY"));
        Assert.assertEquals(Map.of(), refused(ds, 1));
        Assert.assertEquals(Map.of("T#m@5", IN, "T#x@1", IN, "T#y@1", IN), refused(ds, 2));
        Assert.assertEquals(Map.of("T#m@5", OUT, "T#x@1", OUT, "T#y@1", OUT), refused(ds, 3));
        Assert.assertTrue(HeuristicOrchestrator.nestedLsRefusals(ds, 2).entrySet().stream().anyMatch(e -> e.getKey().getCandidate() == loop && e.getValue().contains("self-loop")));
    }

    /** Every lazy kind as an inner (ROPE, INTERLEAVED for String.join / StringJoiner), and an inner with a stock and an LS outer. */
    @Test
    public void allKindsAndMixedOuters() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex outer = concat(g, "T#o@1", 4);
        List<InstrumentationDecision> ds = new ArrayList<>();
        String[] kinds = {"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"};
        for (int i = 0; i < kinds.length; i++) {
            SugVertex in = g.newVertex(); // hand-built (no operand shape): its rep is the variant's
            in.setNodeType(SugNodeType.STRING_METHOD_CALL);
            in.setSourceLocation("T#k@" + i);
            in.addLazyOperandSite("T#o@1");
            if (i == 0) {
                in.addLazyOperandSite("T#stock@3");
            }
            ds.add(lc(in, kinds[i]));
        }
        ds.add(lc(outer, "FIXED4"));
        Map<String, String> r2 = refused(ds, 2);
        Assert.assertEquals(kinds.length, r2.size());
        Assert.assertTrue(r2.values().stream().allMatch(IN::equals));
        Assert.assertEquals(Map.of("T#o@1", OUT), refused(ds, 3));
    }

    /** The orchestrator step: a NESTED-CONCAT-CONFLICT line with the refusal name; the decision is conflict-suppressed. */
    @Test
    public void orchestratorStep() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        List<InstrumentationDecision> ds = mix4(g);
        HeuristicOrchestrator o2 = new HeuristicOrchestrator(g);
        List<InstrumentationDecision> k2 = o2.applyNestedLsRule(ds, 2);
        Assert.assertEquals(1, k2.size());
        Assert.assertEquals(4, o2.getConflictSuppressed().size());
        Assert.assertEquals(4, o2.getConflicts().stream().filter(c -> c.startsWith("NESTED-CONCAT-CONFLICT: disabled LS arg") && c.contains(": " + IN + " (lazy operand of the LS site")).count());
        HeuristicOrchestrator o3 = new HeuristicOrchestrator(g);
        List<InstrumentationDecision> k3 = o3.applyNestedLsRule(ds, 3);
        Assert.assertEquals(4, k3.size());
        Assert.assertEquals(List.of("SC#concatMix4String@94"), o3.getConflictSuppressed().stream().map(InstrumentationDecision::getSourceLocation).toList());
        Assert.assertTrue(o3.getConflicts().get(0).contains(": " + OUT + " (has the LS operand"));
        HeuristicOrchestrator o1 = new HeuristicOrchestrator(g);
        Assert.assertSame(ds, o1.applyNestedLsRule(ds, 1));
        Assert.assertTrue(o1.getConflicts().isEmpty());
    }

    /**
     * Two SUG vertices at one site key. The edge exists when any decision at the outer key is a kept lazy
     * outer (here the first one in the list does not mint); a refused key refuses every LAZY_CONCAT decision at it, as
     * outer (mode 3) and as inner (mode 2); the result and the reason text do not depend on the input order.
     */
    @Test
    public void duplicateKeys() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex oNm = concat(g, "T#o@9", 0); // non-minting (dyn 0) decision at the outer key
        SugVertex oM = concat(g, "T#o@9", 4); // minting sibling at the same key
        SugVertex i1 = concat(g, "T#i@1", 3);
        i1.addLazyOperandSite("T#o@9");
        SugVertex i2 = concat(g, "T#i@1", 3); // sibling at the inner key without the recorded outer
        InstrumentationDecision dNm = lc(oNm, "ROPE");
        InstrumentationDecision dM = lc(oM, "FIXED4");
        InstrumentationDecision d1 = lc(i1, "THREE_WAY");
        InstrumentationDecision d2 = lc(i2, "THREE_WAY");
        List<InstrumentationDecision> ds = List.of(dNm, d2, dM, d1);
        Map<InstrumentationDecision, String> r2 = HeuristicOrchestrator.nestedLsRefusals(ds, 2);
        Assert.assertEquals(Set.of(d1, d2), r2.keySet());
        Map<InstrumentationDecision, String> r3 = HeuristicOrchestrator.nestedLsRefusals(ds, 3);
        Assert.assertEquals(Set.of(dNm, dM), r3.keySet());
        Assert.assertTrue(r3.values().stream().allMatch(v -> v.startsWith(OUT + " (has the LS operand V" + Math.min(i1.getId(), i2.getId()) + " @ T#i@1)")));
        List<InstrumentationDecision> rev = new ArrayList<>(ds);
        java.util.Collections.reverse(rev);
        Assert.assertEquals(r2, HeuristicOrchestrator.nestedLsRefusals(rev, 2));
        Assert.assertEquals(r3, HeuristicOrchestrator.nestedLsRefusals(rev, 3));
        // mode 3 then leaves no LAZY_CONCAT decision at the outer key: no pair with the refused outer
        Assert.assertTrue(LazyOperandPairing.compute(kept(ds, 3), true, false).pairs().isEmpty());
    }

    /** The reason names the smallest kept partner key, whatever the input order. */
    @Test
    public void deterministicReason() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex in = concat(g, "T#i@1", 3);
        in.addLazyOperandSite("T#z@1");
        in.addLazyOperandSite("T#a@1");
        InstrumentationDecision di = lc(in, "THREE_WAY");
        SugVertex z = concat(g, "T#z@1", 4);
        SugVertex a = concat(g, "T#a@1", 4);
        List<InstrumentationDecision> ds = List.of(lc(z, "FIXED4"), di, lc(a, "FIXED4"));
        String why = HeuristicOrchestrator.nestedLsRefusals(ds, 2).get(di);
        Assert.assertEquals(IN + " (lazy operand of the LS site V" + a.getId() + " @ T#a@1)", why);
        List<InstrumentationDecision> rev = new ArrayList<>(ds);
        java.util.Collections.reverse(rev);
        Assert.assertEquals(why, HeuristicOrchestrator.nestedLsRefusals(rev, 2).get(di));
    }

    /** A very long LS chain is evaluated without deep recursion. */
    @Test
    public void longChain() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        int n = 20000;
        List<InstrumentationDecision> ds = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            SugVertex v = concat(g, String.format("T#c@%06d", i), 3);
            if (i + 1 < n) {
                v.addLazyOperandSite(String.format("T#c@%06d", i + 1));
            }
            ds.add(lc(v, "THREE_WAY"));
        }
        java.util.Collections.reverse(ds);
        // chain c0 in c1 in ... in c(n-1): mode 2 keeps the outermost and refuses every other one below it; mode 3 the same from the innermost
        Assert.assertEquals(n / 2, HeuristicOrchestrator.nestedLsRefusals(ds, 2).size());
        Assert.assertEquals(n / 2, HeuristicOrchestrator.nestedLsRefusals(ds, 3).size());
    }

    @Test
    public void knobRange() {
        Assert.assertThrows(com.oracle.svm.core.util.UserError.UserException.class, () -> StringAnalysisFeature.requireLazyOperandMode(4));
        StringAnalysisFeature.requireLazyOperandMode(3);
        for (int v = 0; v <= 3; v++) {
            Assert.assertEquals(v, LazyConcatHeuristic.lazyOperandMode(v));
        }
        Assert.assertThrows(IllegalArgumentException.class, () -> LazyConcatHeuristic.lazyOperandMode(4));
        Assert.assertThrows(IllegalArgumentException.class, () -> LazyConcatHeuristic.lazyOperandMode(-1));
    }
}
