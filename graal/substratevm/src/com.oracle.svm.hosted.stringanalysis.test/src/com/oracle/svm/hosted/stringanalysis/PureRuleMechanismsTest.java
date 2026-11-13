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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;

/**
 * Pins of rules that are pure functions:
 * <ul>
 * <li>the backward path bound: a backward invoke-result push keeps up to {@link ContextPolicy#PATHK_BACKWARD} links (default =
 * PATHK; set {@code fwd.rtrack.pathk.bwd} deeper to extend only the backward descent), every other push keeps
 * {@link ContextPolicy#PATHK}; both keep the most recent links;</li>
 * <li>the owner-merge deferral ({@link RecursiveTracking#OD_DEFER}): the boundary loop
 * {@link RecursiveTracking#decideBoundary} over model resolutions using the production
 * {@link RecursiveTracking#ownerDecision}. Pinned: an owner that arrives while other decisions progress is minted, not
 * merged; the quiet merge; termination by the round budget; determinism over every order of the pending list.</li>
 * </ul>
 */
public class PureRuleMechanismsTest {

    // ------------------------------------------------------------------
    // The backward path bound.
    // ------------------------------------------------------------------

    @Test
    public void backwardBoundFollowsPathkByDefault() {
        // The default context is (ctxk, pathk, pathk.bwd) = (1,1,1); pathk.bwd defaults to pathk. The JUnit JVM sets no
        // knob, so the defaults apply.
        Assert.assertEquals("ctxk default", 1, ContextPolicy.CTXK);
        Assert.assertEquals("pathk default", 1, ContextPolicy.PATHK);
        Assert.assertEquals("pathk.bwd defaults to pathk (symmetric)", ContextPolicy.PATHK, ContextPolicy.PATHK_BACKWARD);
    }

    @Test
    public void boundedPushKeepsTheMostRecentLinks() {
        // the default bounds
        Object[] calls = new Object[ContextPolicy.PATHK_BACKWARD + 3];
        CallPath back = null;
        CallPath fwd = null;
        for (int i = 0; i < calls.length; i++) {
            calls[i] = new Object();
            back = CallPath.pushBackward(null, calls[i], null, back);
            fwd = CallPath.push(null, calls[i], null, fwd);
        }
        Assert.assertEquals("a backward push truncates at PATHK_BACKWARD", ContextPolicy.PATHK_BACKWARD, back.depth());
        Assert.assertEquals("every other push keeps PATHK", ContextPolicy.PATHK, fwd.depth());
        assertMostRecentLinks(calls, back, ContextPolicy.PATHK_BACKWARD);
        // an explicit deeper bound: the k most recent links, head first, in order
        for (int k : new int[]{6, 8}) {
            Object[] deep = new Object[k + 3];
            CallPath p = null;
            for (int i = 0; i < deep.length; i++) {
                deep[i] = new Object();
                p = CallPath.push(null, deep[i], null, p, k);
            }
            Assert.assertEquals("a push truncates at its bound " + k, k, p.depth());
            assertMostRecentLinks(deep, p, k);
        }
    }

    private static void assertMostRecentLinks(Object[] calls, CallPath path, int k) {
        CallPath p = path;
        for (int i = calls.length - 1; i >= calls.length - k; i--) {
            Assert.assertSame("the most recent links are kept, head first (k=" + k + ")", calls[i], p.call);
            p = p.next;
        }
        Assert.assertNull(p);
    }

    @Test
    public void backwardPushWithinTheBoundIsExactAndCounted() {
        // A backward bound deeper than pathk (-J-D...pathk.bwd=8), passed explicitly: the default bound equals PATHK.
        int bound = Math.max(ContextPolicy.PATHK, 8);
        CallPath p = null;
        for (int i = 0; i < ContextPolicy.PATHK; i++) {
            p = CallPath.push(null, new Object(), null, p, bound);
        }
        long before = CallPath.BACKWARD_DEEP_PUSHES.get();
        Object deep = new Object();
        CallPath q = CallPath.push(null, deep, null, p, bound);
        Assert.assertEquals("PATHK + 1 links survive a backward push", ContextPolicy.PATHK + 1, q.depth());
        Assert.assertSame(deep, q.call);
        Assert.assertSame("nothing is rebuilt within the bound", p, q.next);
        Assert.assertTrue("a push the forward bound would have truncated is counted", CallPath.BACKWARD_DEEP_PUSHES.get() > before);
    }

    // ------------------------------------------------------------------
    // The owner-merge deferral: a model of the round loop around the production decision and boundary functions.
    // ------------------------------------------------------------------

    private static final int CAP = 32;

    /**
     * One owner resolution: its owner sink exists, and owners arrive at the boundaries listed in {@code arrivals}
     * (boundary index -> number of owners present from then on). The decision is {@link RecursiveTracking#ownerDecision}
     * on that state, as {@code OwnerResolution.decide} takes it; the trace records every outcome.
     */
    private static final class Model implements RecursiveTracking.BoundaryDecision {
        final String name;
        final int[] ownersAt;
        final List<String> trace;
        int boundary;
        int minted;
        boolean merged;
        boolean deferred;

        Model(String name, List<String> trace, int... ownersAt) {
            this.name = name;
            this.trace = trace;
            this.ownersAt = ownersAt;
        }

        int owners() {
            return ownersAt[Math.min(boundary, ownersAt.length - 1)];
        }

        @Override
        public boolean decide(boolean budgetExhausted) {
            int owners = owners();
            int fresh = owners - minted;
            int d = RecursiveTracking.ownerDecision(merged, true, false, owners, fresh, minted, budgetExhausted, CAP);
            deferred = d == RecursiveTracking.OD_DEFER;
            if (d == RecursiveTracking.OD_NONE || deferred) {
                return false;
            }
            if (d == RecursiveTracking.OD_MINT_FIRST || d == RecursiveTracking.OD_MINT_LATER) {
                minted = owners;
                trace.add(boundary + ":" + name + ":mint" + owners);
            } else {
                merged = true;
                trace.add(boundary + ":" + name + ":merge" + d);
            }
            return true;
        }

        @Override
        public boolean deferred() {
            return deferred;
        }

        @Override
        public void keepPending() {
            deferred = false;
            trace.add(boundary + ":" + name + ":defer");
        }

        @Override
        public void mergeDeferred() {
            deferred = false;
            merged = true;
            trace.add(boundary + ":" + name + ":quietMerge");
        }
    }

    /** The round loop (RecursiveTracking.roundBoundaryImpl's shape): boundaries until one decides nothing; the round budget. */
    private static int run(List<Model> pending, int budget, long[] census) {
        int rounds = 0;
        for (int boundary = 0; boundary < 1000; boundary++) {
            for (Model m : pending) {
                m.boundary = boundary;
            }
            int decided = RecursiveTracking.decideBoundary(pending, rounds >= budget, census);
            pending.removeIf(m -> m.merged);
            if (decided == 0) {
                return boundary;
            }
            rounds++;
        }
        throw new AssertionError("the round loop did not terminate");
    }

    @Test
    public void ownerDecisionDefersOnlyAnExistingEmptySinkWithinTheBudget() {
        Assert.assertEquals(RecursiveTracking.OD_DEFER, RecursiveTracking.ownerDecision(false, true, false, 0, 0, 0, false, CAP));
        Assert.assertEquals("the budget used up: merged at once (the termination argument)", RecursiveTracking.OD_MERGE_UNRESOLVABLE,
                        RecursiveTracking.ownerDecision(false, true, false, 0, 0, 0, true, CAP));
        Assert.assertEquals("no owner sink at all: merged at once", RecursiveTracking.OD_MERGE_UNRESOLVABLE,
                        RecursiveTracking.ownerDecision(false, false, false, 0, 0, 0, false, CAP));
        Assert.assertEquals("a refused owner sink is never deferred", RecursiveTracking.OD_MERGE_REFUSED,
                        RecursiveTracking.ownerDecision(false, true, true, 0, 0, 0, false, CAP));
        Assert.assertEquals("an owner minted earlier: not pending", RecursiveTracking.OD_NONE,
                        RecursiveTracking.ownerDecision(false, true, false, 1, 0, 1, false, CAP));
        Assert.assertEquals("merged is sticky", RecursiveTracking.OD_NONE, RecursiveTracking.ownerDecision(true, true, false, 0, 0, 0, false, CAP));
    }

    /** The gain: the owner of `late` arrives at boundary 2 while `busy` mints at 0 and 1; `late` is minted, never merged. */
    @Test
    public void anOwnerArrivingWhileOthersProgressIsMintedNotMerged() {
        List<String> trace = new ArrayList<>();
        List<Model> pending = new ArrayList<>(List.of(new Model("late", trace, 0, 0, 1), new Model("busy", trace, 1, 2, 2)));
        long[] census = new long[2];
        run(pending, RecursiveTracking.OWNER_ROUND_BUDGET, census);
        Assert.assertEquals(List.of("0:busy:mint1", "0:late:defer", "1:busy:mint2", "1:late:defer", "2:late:mint1"), sorted(trace));
        Assert.assertEquals("two deferrals, no quiet merge", 2, census[0]);
        Assert.assertEquals(0, census[1]);
    }

    /** A lone empty sink merges at the first boundary: nothing else progressed (the plain merge, not delayed). */
    @Test
    public void aLoneEmptySinkMergesAtTheFirstQuietBoundary() {
        List<String> trace = new ArrayList<>();
        List<Model> pending = new ArrayList<>(List.of(new Model("empty", trace, 0)));
        long[] census = new long[2];
        Assert.assertEquals("the boundary after the merge decides nothing", 1, run(pending, RecursiveTracking.OWNER_ROUND_BUDGET, census));
        Assert.assertEquals(List.of("0:empty:quietMerge"), trace);
        Assert.assertEquals(1, census[1]);
    }

    /** Several deferred sinks at a quiet boundary merge together (the rule defers; it does not order the merges). */
    @Test
    public void allDeferredSinksOfAQuietBoundaryMergeTogether() {
        List<String> trace = new ArrayList<>();
        List<Model> pending = new ArrayList<>(List.of(new Model("a", trace, 0), new Model("b", trace, 0), new Model("busy", trace, 1)));
        run(pending, RecursiveTracking.OWNER_ROUND_BUDGET, new long[2]);
        Assert.assertEquals(List.of("0:a:defer", "0:b:defer", "0:busy:mint1", "1:a:quietMerge", "1:b:quietMerge"), sorted(trace));
    }

    /** Termination: a source that progresses at every boundary keeps an empty sink pending only until the round budget is used up. */
    @Test
    public void theRoundBudgetEndsTheDeferral() {
        int budget = 5;
        List<String> trace = new ArrayList<>();
        int[] growing = new int[budget + 20];
        for (int i = 0; i < growing.length; i++) {
            growing[i] = i + 1;
        }
        List<Model> pending = new ArrayList<>(List.of(new Model("empty", trace, 0), new Model("grow", trace, growing)));
        int last = run(pending, budget, new long[2]);
        Assert.assertTrue("the empty sink merges once the budget is exhausted", trace.contains(budget + ":empty:merge" + RecursiveTracking.OD_MERGE_UNRESOLVABLE));
        Assert.assertFalse(trace.contains(budget + ":empty:defer"));
        Assert.assertTrue("the loop ends (the growing source merges by budget too)", last <= budget + 1);
    }

    /** Determinism: every order of the pending list gives the same set of outcomes per boundary. */
    @Test
    public void theBoundaryIsIndependentOfThePendingOrder() {
        List<String> reference = null;
        List<Integer> order = new ArrayList<>(List.of(0, 1, 2, 3));
        for (List<Integer> perm : permutations(order)) {
            List<String> trace = new ArrayList<>();
            Model[] ms = {new Model("late", trace, 0, 0, 2), new Model("busy", trace, 1, 2, 3), new Model("empty", trace, 0), new Model("never", trace, 0, 0, 0, 0)};
            List<Model> pending = new ArrayList<>();
            for (int i : perm) {
                pending.add(ms[i]);
            }
            run(pending, RecursiveTracking.OWNER_ROUND_BUDGET, new long[2]);
            List<String> s = sorted(trace);
            if (reference == null) {
                reference = s;
            } else {
                Assert.assertEquals("order " + perm, reference, s);
            }
        }
        Assert.assertTrue("the deferral delayed both empty sinks past the busy rounds", reference.contains("3:empty:quietMerge") && reference.contains("3:never:quietMerge"));
    }

    private static List<String> sorted(List<String> trace) {
        List<String> s = new ArrayList<>(trace);
        Collections.sort(s);
        return s;
    }

    private static List<List<Integer>> permutations(List<Integer> xs) {
        List<List<Integer>> out = new ArrayList<>();
        permute(xs, new ArrayList<>(), new HashSet<>(), out);
        return out;
    }

    private static void permute(List<Integer> xs, List<Integer> cur, Set<Integer> used, List<List<Integer>> out) {
        if (cur.size() == xs.size()) {
            out.add(new ArrayList<>(cur));
            return;
        }
        for (int x : xs) {
            if (used.add(x)) {
                cur.add(x);
                permute(xs, cur, used, out);
                cur.remove(cur.size() - 1);
                used.remove(x);
            }
        }
    }
}
