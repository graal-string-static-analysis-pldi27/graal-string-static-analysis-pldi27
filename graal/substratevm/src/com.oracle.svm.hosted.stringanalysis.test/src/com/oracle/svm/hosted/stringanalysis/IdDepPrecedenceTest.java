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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

/**
 * ID-DEP precedence at the cross-rep compareTo conflict (incl. the image-wide bridge site and its receiver-family cap),
 * the wildcard set closed under inlining, the ACC receiver sinks as an audited ID-DEP reader, the nested-concat and
 * receiver-cap ID-DEP branches as truth tables, and the monotonicity of every precedence pass: the non-ID-DEP outcome
 * equals the outcome without the ID-DEP decisions (the objret=0 outcome).
 */
public class IdDepPrecedenceTest {

    private static SugVertex substring(StringUtilizationGraph g, String loc) {
        SugVertex v = g.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("substring");
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName("TestUserClass");
        v.setLength(5);
        v.setSourceLocation(loc);
        return v;
    }

    private static SugVertex concat(StringUtilizationGraph g, String loc) {
        SugVertex v = g.newVertex();
        v.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        v.setLength(10);
        v.setEnclosingClassName("TestUserClass");
        v.setSourceLocation(loc);
        return v;
    }

    private static SugVertex cmpVertex(StringUtilizationGraph g, SugNodeType type, String enclosing, String loc) {
        SugVertex v = g.newVertex();
        v.setNodeType(type);
        v.setMethodName("compareTo");
        v.setMethodSignature("Ljava/lang/String;");
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName(enclosing);
        v.setSourceLocation(loc);
        return v;
    }

    private static InstrumentationDecision decision(OptimizationType t, String variant, String loc, boolean idDep) {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex v = g.newVertex();
        v.setEnclosingClassName("TestUserClass");
        v.setSourceLocation(loc);
        if (idDep) {
            v.markIdDep();
        }
        return new InstrumentationDecision(v, t, variant);
    }

    private static List<InstrumentationDecision> nonDep(List<InstrumentationDecision> ds) {
        return ds.stream().filter(d -> !d.getCandidate().isIdDep()).toList();
    }

    // ------------------------------------------------------------------ ID-DEP x compareTo (end to end on the orchestrator)

    /** One compareTo site: an SV receiver and a ROPE argument, each optionally ID-DEP. */
    private static HeuristicOrchestrator cmpConflict(boolean recvDep, boolean argDep, List<SugVertex> out) {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex recv = substring(g, "R.java:1");
        SugVertex arg = concat(g, "A.java:1");
        SugVertex c = cmpVertex(g, SugNodeType.STRING_METHOD_CALL, "TestUserClass", "K.java:1");
        g.addEdge(recv, c, SugEdgeType.QUALIFIER, -1);
        g.addEdge(arg, c, SugEdgeType.PARAMETER, 1);
        UsageSourceBuilder.build(g);
        if (recvDep) {
            recv.markIdDep();
        }
        if (argDep) {
            arg.markIdDep();
        }
        HeuristicOrchestrator o = new HeuristicOrchestrator(g);
        o.run(Collections.emptyList(), new ArrayList<>(List.of(new InstrumentationDecision(recv, OptimizationType.STRING_VIEW, null))),
                        new ArrayList<>(List.of(new InstrumentationDecision(arg, OptimizationType.LAZY_CONCAT, "ROPE"))), Collections.emptyList(), Collections.emptyList());
        out.add(recv);
        out.add(arg);
        return o;
    }

    private static Set<SugVertex> kept(HeuristicOrchestrator o) {
        Set<SugVertex> s = new LinkedHashSet<>();
        for (InstrumentationDecision d : o.getValidatedDecisions()) {
            s.add(d.getCandidate());
        }
        return s;
    }

    @Test
    public void idDepAdmitNeverSurvivesACompareToConflictItCaused() {
        // no ID-DEP (objret=0): the base rule, the SV (higher priority) is kept, the ROPE reverted
        List<SugVertex> vs = new ArrayList<>();
        HeuristicOrchestrator o = cmpConflict(false, false, vs);
        Assert.assertEquals(Set.of(vs.get(0)), kept(o));
        // the SV receiver is ID-DEP, the ROPE argument is not: the ID-DEP SV is reverted, the ROPE (the knob-0 admit) stays
        vs.clear();
        o = cmpConflict(true, false, vs);
        Assert.assertEquals(Set.of(vs.get(1)), kept(o));
        Assert.assertEquals(1, o.getConflicts().size());
        Assert.assertTrue(o.getConflicts().get(0), o.getConflicts().get(0).contains("cross-rep compareTo conflict at K.java:1 (SV reverted, ROPE kept)"));
        // the ROPE argument is ID-DEP: it is reverted (as without the flag)
        vs.clear();
        o = cmpConflict(false, true, vs);
        Assert.assertEquals(Set.of(vs.get(0)), kept(o));
        // both ID-DEP: the normal rule among them
        vs.clear();
        o = cmpConflict(true, true, vs);
        Assert.assertEquals(Set.of(vs.get(0)), kept(o));
    }

    @Test
    public void bridgeSiteIdDepReceiversLoseTheConflictAndTheFamilyCap() {
        // the bridge's internal String#compareTo(Object)@5: one image-wide JDK vertex; receivers tagged by cmpBridgeReceiver
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex bridge = cmpVertex(g, SugNodeType.JDK_LIBRARY_CALL, "java.lang.String", "java.lang.String#compareTo(Ljava/lang/Object;)I@5");
        String[] reps = {"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"};
        List<InstrumentationDecision> lc = new ArrayList<>();
        Map<String, SugVertex> byRep = new java.util.LinkedHashMap<>();
        for (int i = 0; i < reps.length; i++) {
            SugVertex v = concat(g, "L.java:" + (i + 1));
            g.addEdge(v, bridge, SugEdgeType.QUALIFIER, -1);
            lc.add(new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, reps[i]));
            byRep.put(reps[i], v);
        }
        SugVertex sv = substring(g, "S.java:1");
        g.addEdge(sv, bridge, SugEdgeType.QUALIFIER, -1);
        UsageSourceBuilder.build(g);
        // six receiver families at the bridge (> the cap 5); the SV is ID-DEP: it is the one disabled, not INTERLEAVED
        sv.markIdDep();
        HeuristicOrchestrator o = new HeuristicOrchestrator(g);
        o.run(Collections.emptyList(), new ArrayList<>(List.of(new InstrumentationDecision(sv, OptimizationType.STRING_VIEW, null))), lc, Collections.emptyList(), Collections.emptyList());
        Set<SugVertex> k = kept(o);
        Assert.assertFalse("the ID-DEP SV loses the receiver-family cap", k.contains(sv));
        Assert.assertTrue(k.containsAll(byRep.values()));
    }

    /**
     * A call site reached (no RECEIVER tag) by six non-ID-DEP LS families (> the cap 5) takes the
     * reachability fallback. A delivery's RECEIVER tag (an ID-DEP SV) must not switch the counted set to the tags: the
     * non-ID-DEP outcome stays the objret=0 one (one LS family disabled).
     */
    private static Set<SugVertex> receiverFallbackRun(boolean withIdDepSv, List<SugVertex> lsOut) {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex call = g.newVertex();
        call.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        call.setMethodName("indexOf");
        call.setDeclaringClass("java.lang.String");
        call.setEnclosingClassName("java.lang.String");
        call.setSourceLocation("java.lang.String#x@1");
        String[] reps = {"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED", "FIXED2"};
        List<InstrumentationDecision> lc = new ArrayList<>();
        for (int i = 0; i < reps.length; i++) {
            SugVertex v = concat(g, "L.java:" + (i + 1));
            g.addEdge(v, call, SugEdgeType.PARAMETER, 1);
            lc.add(new InstrumentationDecision(v, OptimizationType.LAZY_CONCAT, reps[i]));
            lsOut.add(v);
        }
        List<InstrumentationDecision> svs = new ArrayList<>();
        SugVertex sv = null;
        if (withIdDepSv) {
            sv = substring(g, "S.java:1");
            g.addEdge(sv, call, SugEdgeType.QUALIFIER, -1);
            svs.add(new InstrumentationDecision(sv, OptimizationType.STRING_VIEW, null));
        }
        UsageSourceBuilder.build(g);
        if (sv != null) {
            sv.markIdDep();
        }
        HeuristicOrchestrator o = new HeuristicOrchestrator(g);
        o.run(Collections.emptyList(), svs, lc, Collections.emptyList(), Collections.emptyList());
        return kept(o);
    }

    @Test
    public void receiverCapFallbackIgnoresIdDepTags() {
        List<SugVertex> ls0 = new ArrayList<>();
        Set<SugVertex> k0 = receiverFallbackRun(false, ls0);
        Assert.assertEquals("objret=0: the fallback counts six families, one is disabled", 5, k0.size());
        int disabled0 = -1;
        for (int i = 0; i < ls0.size(); i++) {
            if (!k0.contains(ls0.get(i))) {
                disabled0 = i;
            }
        }
        List<SugVertex> ls1 = new ArrayList<>();
        Set<SugVertex> k1 = receiverFallbackRun(true, ls1);
        for (int i = 0; i < ls1.size(); i++) {
            Assert.assertEquals("LS family " + i + " keeps its objret=0 fate", i != disabled0, k1.contains(ls1.get(i)));
        }
        Assert.assertEquals("the ID-DEP SV is counted and sorted last", 5, k1.size());
    }

    // ------------------------------------------------------------------ monotonicity of every precedence pass (property)

    private static final OptimizationType[] TYPES = {OptimizationType.SINGLE_BYTE, OptimizationType.STRING_VIEW, OptimizationType.LAZY_CONCAT};
    private static final String[] VARIANTS = {"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"};

    private static List<InstrumentationDecision> random(Random r, String prefix, int n) {
        List<InstrumentationDecision> out = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            OptimizationType t = TYPES[r.nextInt(TYPES.length)];
            out.add(decision(t, t == OptimizationType.LAZY_CONCAT ? VARIANTS[r.nextInt(VARIANTS.length)] : null, prefix + ".java:" + i, r.nextInt(3) == 0));
        }
        return out;
    }

    @Test
    public void everyPrecedencePassIsMonotone() {
        Random r = new Random(96);
        for (int round = 0; round < 3000; round++) {
            List<InstrumentationDecision> recv = random(r, "R" + round, r.nextInt(5));
            List<InstrumentationDecision> arg = random(r, "A" + round, r.nextInt(5));
            // equals / compareTo conflict: the non-ID-DEP reverts are exactly the reverts without the ID-DEP decisions,
            // and every involved ID-DEP decision of a mixed site is reverted
            List<InstrumentationDecision> rev = HeuristicOrchestrator.crossRepEqualsRevertsIdDep(recv, arg);
            Assert.assertEquals(new LinkedHashSet<>(HeuristicOrchestrator.crossRepEqualsReverts(nonDep(recv), nonDep(arg))), new LinkedHashSet<>(nonDep(rev)));
            Set<InstrumentationDecision> inv = HeuristicOrchestrator.crossRepEqualsInvolved(recv, arg);
            if (HeuristicOrchestrator.idDepMixed(inv)) {
                for (InstrumentationDecision d : inv) {
                    Assert.assertTrue(!d.getCandidate().isIdDep() || rev.contains(d));
                }
            }
            // the result is conflict-free
            List<InstrumentationDecision> recvLeft = recv.stream().filter(d -> !rev.contains(d)).toList();
            List<InstrumentationDecision> argLeft = arg.stream().filter(d -> !rev.contains(d)).toList();
            Assert.assertTrue(HeuristicOrchestrator.crossRepEqualsInvolved(recvLeft, argLeft).isEmpty());
            // without any ID-DEP flag: the base rule exactly (the objret=0 identity)
            if (nonDep(recv).size() == recv.size() && nonDep(arg).size() == arg.size()) {
                Assert.assertEquals(HeuristicOrchestrator.crossRepEqualsReverts(recv, arg), rev);
            }
            // the receiver-family cap
            List<InstrumentationDecision> all = new ArrayList<>(recv);
            all.addAll(arg);
            for (int max = 1; max <= 5; max++) {
                Set<InstrumentationDecision> dis = HeuristicOrchestrator.receiverCapDisabled(all, max, new LinkedHashSet<>());
                Set<InstrumentationDecision> dis0 = HeuristicOrchestrator.receiverCapDisabled(nonDep(all), max, new LinkedHashSet<>());
                Assert.assertEquals(dis0, new LinkedHashSet<>(nonDep(new ArrayList<>(dis))));
            }
        }
    }

    // ------------------------------------------------------------------ the nested-concat branches (truth tables)

    @Test
    public void svReachTruthTable() {
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.NONE, HeuristicOrchestrator.svReachOutcome(false, false, List.of()));
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.NONE, HeuristicOrchestrator.svReachOutcome(true, false, List.of()));
        // no ID-DEP anywhere (objret=0): the base rule, the site is disabled
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(false, false, List.of(false)));
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(false, false, List.of(false, false)));
        // only ID-DEP Views reach a non-ID-DEP site: the Views go
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_ID_DEP_SVS, HeuristicOrchestrator.svReachOutcome(false, false, List.of(true)));
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_ID_DEP_SVS, HeuristicOrchestrator.svReachOutcome(false, false, List.of(true, true)));
        // mixed: a non-ID-DEP View disables the site (the knob-0 outcome)
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(false, false, List.of(true, false)));
        // an ID-DEP site: the base rule (it is the ID-DEP one)
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(true, false, List.of(true)));
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(true, false, List.of(false)));
        // an already disabled site: no View is dropped for it
        Assert.assertEquals(HeuristicOrchestrator.SvReachOutcome.DROP_SITE, HeuristicOrchestrator.svReachOutcome(false, true, List.of(true)));
    }

    @Test
    public void operandTruthTable() {
        List<Boolean> none = List.of();
        // no ID-DEP (objret=0): the base rule
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.NONE, HeuristicOrchestrator.operandOutcome(false, none, none));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_OUTER, HeuristicOrchestrator.operandOutcome(false, List.of(false), none));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_OUTER, HeuristicOrchestrator.operandOutcome(false, List.of(false), List.of(false)));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_INNER, HeuristicOrchestrator.operandOutcome(false, none, List.of(false)));
        // only ID-DEP SB/SV operands of a non-ID-DEP outer: the operands go
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OPERANDS, HeuristicOrchestrator.operandOutcome(false, List.of(true), none));
        // ... and a conflicting inner LS still conflicts with the outer: the inner rule applies too
        // (a) a non-ID-DEP inner: disabled, as at objret=0 (operandOutcome(false, [], [false]) = DROP_INNER)
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER, HeuristicOrchestrator.operandOutcome(false, List.of(true, true), List.of(false)));
        // (b) an ID-DEP inner: disabled (it conflicts with the non-ID-DEP outer)
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER, HeuristicOrchestrator.operandOutcome(false, List.of(true), List.of(true)));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER, HeuristicOrchestrator.operandOutcome(false, List.of(true), List.of(true, false)));
        // mixed operands: the knob-0 outcome (the outer goes)
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_OUTER, HeuristicOrchestrator.operandOutcome(false, List.of(true, false), none));
        // an ID-DEP outer with SB/SV operands: it goes (the base rule; it is the ID-DEP one)
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_OUTER, HeuristicOrchestrator.operandOutcome(true, List.of(false), none));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_OUTER, HeuristicOrchestrator.operandOutcome(true, List.of(true), none));
        // an ID-DEP outer over a non-ID-DEP inner LS: the outer goes instead of the inner
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OUTER, HeuristicOrchestrator.operandOutcome(true, none, List.of(false)));
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_ID_DEP_OUTER, HeuristicOrchestrator.operandOutcome(true, none, List.of(true, false)));
        // an ID-DEP outer over ID-DEP inners only: the base rule among them
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_INNER, HeuristicOrchestrator.operandOutcome(true, none, List.of(true)));
        // a non-ID-DEP outer over ID-DEP inners: the inners go (they are the ID-DEP ones)
        Assert.assertEquals(HeuristicOrchestrator.OperandOutcome.DROP_INNER, HeuristicOrchestrator.operandOutcome(false, none, List.of(true)));
    }

    /** Which inputs an outcome disables: [outer, customs..., inners...]. */
    private static boolean[] operandEffect(HeuristicOrchestrator.OperandOutcome o, int nCustom, int nInner) {
        boolean[] dis = new boolean[1 + nCustom + nInner];
        switch (o) {
            case DROP_ID_DEP_OUTER, DROP_OUTER -> dis[0] = true;
            case DROP_ID_DEP_OPERANDS -> java.util.Arrays.fill(dis, 1, 1 + nCustom, true);
            case DROP_ID_DEP_OPERANDS_AND_INNER -> java.util.Arrays.fill(dis, 1, 1 + nCustom + nInner, true);
            case DROP_INNER -> java.util.Arrays.fill(dis, 1 + nCustom, 1 + nCustom + nInner, true);
            case NONE -> {
            }
        }
        return dis;
    }

    private static List<Boolean> randomFlags(Random r, int max) {
        List<Boolean> l = new ArrayList<>();
        int n = r.nextInt(max + 1);
        for (int i = 0; i < n; i++) {
            l.add(r.nextInt(3) == 0);
        }
        return l;
    }

    /**
     * The nested-concat branches are monotone and conflict-free. For random ID-DEP flags of the outer LS,
     * its SB/SV operands and its conflicting inner LS operands: (1) the result is conflict-free (a kept outer has no kept
     * SB/SV operand and no kept conflicting inner); (2) every non-ID-DEP input's fate equals its fate in the objret=0
     * outcome, i.e. {@code operandOutcome} over the non-ID-DEP inputs only (an ID-DEP outer does not exist there: its
     * non-ID-DEP operands keep their admits). The same for {@code svReachOutcome}.
     */
    @Test
    public void nestedConcatBranchesAreMonotoneAndConflictFree() {
        Random r = new Random(1196);
        for (int round = 0; round < 5000; round++) {
            boolean outerDep = r.nextInt(3) == 0;
            List<Boolean> cust = randomFlags(r, 3);
            List<Boolean> inner = randomFlags(r, 3);
            HeuristicOrchestrator.OperandOutcome o = HeuristicOrchestrator.operandOutcome(outerDep, cust, inner);
            boolean[] dis = operandEffect(o, cust.size(), inner.size());
            String ctx = "outerDep=" + outerDep + " custom=" + cust + " inner=" + inner + " -> " + o;
            if (!dis[0]) {
                for (int i = 1; i < dis.length; i++) {
                    Assert.assertTrue("conflict-free: " + ctx, dis[i]);
                }
            }
            // the objret=0 outcome over the non-ID-DEP inputs
            List<Integer> custIdx = new ArrayList<>();
            List<Integer> innerIdx = new ArrayList<>();
            for (int i = 0; i < cust.size(); i++) {
                if (!cust.get(i)) {
                    custIdx.add(i);
                }
            }
            for (int i = 0; i < inner.size(); i++) {
                if (!inner.get(i)) {
                    innerIdx.add(i);
                }
            }
            boolean[] dis0 = outerDep ? new boolean[1 + custIdx.size() + innerIdx.size()]
                            : operandEffect(HeuristicOrchestrator.operandOutcome(false, java.util.Collections.nCopies(custIdx.size(), false), java.util.Collections.nCopies(innerIdx.size(), false)),
                                            custIdx.size(), innerIdx.size());
            if (!outerDep) {
                Assert.assertEquals("outer: " + ctx, dis0[0], dis[0]);
            }
            for (int k = 0; k < custIdx.size(); k++) {
                Assert.assertEquals("custom " + custIdx.get(k) + ": " + ctx, dis0[1 + k], dis[1 + custIdx.get(k)]);
            }
            for (int k = 0; k < innerIdx.size(); k++) {
                Assert.assertEquals("inner " + innerIdx.get(k) + ": " + ctx, dis0[1 + custIdx.size() + k], dis[1 + cust.size() + innerIdx.get(k)]);
            }
            // no flag at all (objret=0): the base rule exactly
            if (!outerDep && !cust.contains(true) && !inner.contains(true)) {
                Assert.assertTrue(ctx, o == (cust.isEmpty() ? (inner.isEmpty() ? HeuristicOrchestrator.OperandOutcome.NONE : HeuristicOrchestrator.OperandOutcome.DROP_INNER)
                                : HeuristicOrchestrator.OperandOutcome.DROP_OUTER));
            }

            // svReachOutcome: [site, svs...]
            boolean siteDep = r.nextInt(3) == 0;
            boolean siteDisabled = r.nextInt(4) == 0;
            List<Boolean> svs = randomFlags(r, 3);
            HeuristicOrchestrator.SvReachOutcome so = HeuristicOrchestrator.svReachOutcome(siteDep, siteDisabled, svs);
            boolean siteOff = siteDisabled || so == HeuristicOrchestrator.SvReachOutcome.DROP_SITE;
            boolean svsOff = so == HeuristicOrchestrator.SvReachOutcome.DROP_ID_DEP_SVS;
            String sctx = "siteDep=" + siteDep + " disabled=" + siteDisabled + " svs=" + svs + " -> " + so;
            Assert.assertTrue("conflict-free: " + sctx, siteOff || svs.isEmpty() || svsOff);
            Assert.assertTrue("only ID-DEP Views are dropped: " + sctx, !svsOff || !svs.contains(false));
            if (!siteDep) {
                long nonDepSvs = svs.stream().filter(b -> !b).count();
                HeuristicOrchestrator.SvReachOutcome so0 = HeuristicOrchestrator.svReachOutcome(false, siteDisabled, java.util.Collections.nCopies((int) nonDepSvs, false));
                Assert.assertEquals("site: " + sctx, siteDisabled || so0 == HeuristicOrchestrator.SvReachOutcome.DROP_SITE, siteOff);
            }
            // the non-ID-DEP Views are never dropped by this rule (at objret=0 neither)
        }
    }

    /** End to end: a non-ID-DEP outer LS with an ID-DEP SB operand and an inner LS (both flag states). */
    @Test
    public void idDepOperandDropStillAppliesTheInnerRule() {
        for (boolean innerDep : new boolean[]{false, true}) {
            StringUtilizationGraph g = new StringUtilizationGraph();
            SugVertex inner = concat(g, "Inner.java:1");
            inner.setDynamicOperandCount(2);
            SugVertex sb = g.newVertex();
            sb.setNodeType(SugNodeType.STRING_LITERAL);
            sb.setLiteralText("k");
            sb.setLength(1);
            sb.setEnclosingClassName("TestUserClass");
            sb.setSourceLocation("SB.java:1");
            SugVertex outer = concat(g, "Outer.java:1");
            outer.setDynamicOperandCount(2);
            outer.setOperandSourceLocations(List.of("Inner.java:1", "SB.java:1"));
            sb.markIdDep();
            if (innerDep) {
                inner.markIdDep();
            }
            HeuristicOrchestrator o = new HeuristicOrchestrator(g);
            o.run(new ArrayList<>(List.of(new InstrumentationDecision(sb, OptimizationType.SINGLE_BYTE, null))), Collections.emptyList(),
                            new ArrayList<>(List.of(new InstrumentationDecision(inner, OptimizationType.LAZY_CONCAT, "ROPE"), new InstrumentationDecision(outer, OptimizationType.LAZY_CONCAT,
                                            "ROPE"))),
                            Collections.emptyList(), Collections.emptyList());
            Assert.assertEquals("innerDep=" + innerDep + " " + o.getConflicts(), Set.of(outer), kept(o));
            Assert.assertTrue(o.getConflicts().stream().anyMatch(c -> c.contains("disabled LS arg V" + inner.getId())));
        }
    }

    @Test
    public void receiverCapOrdersIdDepLast() {
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:1", false);
        InstrumentationDecision ropeDep = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2", true);
        InstrumentationDecision three = decision(OptimizationType.LAZY_CONCAT, "THREE_WAY", "A.java:3", false);
        InstrumentationDecision fixed = decision(OptimizationType.LAZY_CONCAT, "FIXED4", "A.java:4", false);
        // without the flag (objret=0) the priority order retains SV, ROPE and disables THREE_WAY, FIXED4
        InstrumentationDecision rope = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2", false);
        Set<String> ret = new LinkedHashSet<>();
        Assert.assertEquals(new LinkedHashSet<>(List.of(three, fixed)), HeuristicOrchestrator.receiverCapDisabled(List.of(sv, rope, three, fixed), 2, ret));
        Assert.assertEquals(new LinkedHashSet<>(List.of("SV", "ROPE")), ret);
        // the ROPE is ID-DEP: it is sorted last and disabled; THREE_WAY is retained (the knob-0 outcome without the ROPE)
        ret.clear();
        Assert.assertEquals(new LinkedHashSet<>(List.of(fixed, ropeDep)), HeuristicOrchestrator.receiverCapDisabled(List.of(sv, ropeDep, three, fixed), 2, ret));
        Assert.assertEquals(new LinkedHashSet<>(List.of("SV", "THREE_WAY")), ret);
        // all ID-DEP: the priority order among them
        InstrumentationDecision svDep = decision(OptimizationType.STRING_VIEW, null, "A.java:5", true);
        InstrumentationDecision threeDep = decision(OptimizationType.LAZY_CONCAT, "THREE_WAY", "A.java:6", true);
        ret.clear();
        Assert.assertEquals(new LinkedHashSet<>(List.of(threeDep)), HeuristicOrchestrator.receiverCapDisabled(List.of(threeDep, ropeDep, svDep), 2, ret));
    }

    // ------------------------------------------------------------------ the wildcard set closed under inlining

    @Test
    public void wildcardClosureTruthTable() {
        // H holds mh.invokeExact (a wildcard) and is inlined into F (unframed) and G; F is inlined into E
        Map<String, List<String>> callers = Map.of("H", List.of("F", "G"), "F", List.of("E"), "G", List.of(), "E", List.of("D"), "D", List.of("C"), "C", List.of());
        // nothing inlined: the seeds only
        Assert.assertEquals(Set.of("H"), ObjRetRules.wildcardClosure(List.of("H"), m -> false, callers::get, 3));
        // H inlined: its bytecode callers are wildcards too
        Assert.assertEquals(Set.of("H", "F", "G"), ObjRetRules.wildcardClosure(List.of("H"), "H"::equals, callers::get, 3));
        // H and F inlined: transitively
        Assert.assertEquals(Set.of("H", "F", "G", "E"), ObjRetRules.wildcardClosure(List.of("H"), m -> m.equals("H") || m.equals("F"), callers::get, 3));
        // a chain at the bound (H, F, E, D all inlined; depth 3): fail closed
        Assert.assertNull(ObjRetRules.wildcardClosure(List.of("H"), m -> !m.equals("C"), callers::get, 3));
        Assert.assertEquals(Set.of("H", "F", "G", "E", "D", "C"), ObjRetRules.wildcardClosure(List.of("H"), m -> !m.equals("C") && !m.equals("G"), callers::get, 4));
        // unknown callers of an inlined wildcard: fail closed
        Assert.assertNull(ObjRetRules.wildcardClosure(List.of("H"), m -> true, m -> null, 3));
        // an inlined wildcard with no bytecode caller (a host the index cannot name): fail closed, as
        // inlinedOnlyOk does with empty callers; a non-inlined member without callers is fine
        Assert.assertNull(ObjRetRules.wildcardClosure(List.of("G"), "G"::equals, callers::get, 3));
        Assert.assertNull(ObjRetRules.wildcardClosure(List.of("H"), m -> m.equals("H") || m.equals("G"), callers::get, 3));
        Assert.assertEquals(Set.of("G"), ObjRetRules.wildcardClosure(List.of("G"), m -> false, callers::get, 3));
        // a cycle terminates
        Map<String, List<String>> cyc = Map.of("A", List.of("B"), "B", List.of("A"));
        Assert.assertEquals(Set.of("A", "B"), ObjRetRules.wildcardClosure(List.of("A"), m -> true, cyc::get, 3));
    }

    @Test
    public void closedWildcardFailsTheRouteReview9Describes() {
        // H (framed, a wildcard) inlined into F (unframed: CLINIT_RUNTIME); X is INLINED_ONLY with framed
        // bytecode callers. Without the closure wildcardOk(H) passes; with it F is a wildcard and fails.
        Map<String, ObjRetRules.UnframedCause> cause = Map.of("F", ObjRetRules.UnframedCause.CLINIT_RUNTIME);
        ObjRetRules.InlinedFacts<String> facts = new ObjRetRules.InlinedFacts<>() {
            @Override
            public ObjRetRules.UnframedCause causeOf(String m) {
                return cause.get(m);
            }

            @Override
            public boolean excluded(String m) {
                return false;
            }

            @Override
            public java.util.Collection<String> callers(String m) {
                return m.equals("H") ? List.of("F") : List.of();
            }
        };
        Assert.assertTrue("H alone passes (framed)", ObjRetRules.wildcardOk("H", facts));
        Set<String> closed = ObjRetRules.wildcardClosure(List.of("H"), "H"::equals, facts::callers, ObjRetRules.INLINED_ONLY_DEPTH);
        Assert.assertEquals(Set.of("H", "F"), closed);
        Assert.assertFalse("the host F fails the closed conjunction", closed.stream().allMatch(w -> ObjRetRules.wildcardOk(w, facts)));
    }

    // ------------------------------------------------------------------ the ACC receiver sink is an audited reader

    @Test
    public void accReceiverSinkMarksItsDepFlag() {
        ContainerTables.DEFER = Runnable::run;
        ContainerTables.Sink sink = new ContainerTables.Sink("accrecv-sink", 100, 100);
        ContainerTables.DepFlag flag = new ContainerTables.DepFlag();
        sink.addListener(new ContainerTables.Listener(List.of("accrecv", "r"), a -> {
        }, r -> {
        }, null, flag));
        long untargeted = ContainerTables.ID_DEP_UNTARGETED.sum();
        Assert.assertFalse(flag.idDep());
        ContainerTables.markIdDep(sink);
        Assert.assertTrue("the extraction's flag is set", flag.idDep());
        Assert.assertEquals("no unaudited reader", untargeted, ContainerTables.ID_DEP_UNTARGETED.sum());
        Assert.assertFalse(flag.hasAnyRefusal());
        Assert.assertTrue(flag.setIdDep().isEmpty());
    }
}
