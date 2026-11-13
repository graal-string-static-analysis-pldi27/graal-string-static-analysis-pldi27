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

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.ContextElement;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.HeapContext;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.FrameCfg;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.FramePools;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.PoolAccess;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.DefaultContextPolicy;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;

import jdk.graal.compiler.nodes.ConstantNode;

/**
 * Recursive-tracking pins: the owner decision (staged in rounds), the context policy's
 * arithmetic, the path shapes incl. the EXHAUSTED lineage marker, the length-0 stamp
 * proof, and the `[]` never-kill rule of the pools.
 */
public class RecursiveTrackingRulesTest {

    private static final int CAP = 32;

    // ------------------------------------------------------------------
    // The owner decision at a round boundary (a pure function).
    // ------------------------------------------------------------------
    @Test
    public void dl42UnrefusedWithinCapMintsOnePerOwnerAtTheBoundary() {
        Assert.assertEquals(RecursiveTracking.OD_MINT_FIRST,
                        RecursiveTracking.ownerDecision(false, true, false, 3, 3, 0, false, CAP));
    }

    @Test
    public void dl42RefusedOrOverCapOrUnresolvableMerges() {
        Assert.assertEquals(RecursiveTracking.OD_MERGE_REFUSED,
                        RecursiveTracking.ownerDecision(false, true, true, 0, 0, 0, false, CAP));
        Assert.assertEquals(RecursiveTracking.OD_MERGE_CAP,
                        RecursiveTracking.ownerDecision(false, true, false, CAP + 1, CAP + 1, 0, false, CAP));
        Assert.assertEquals("no owner at quiescence (deferred to a quiet boundary)", RecursiveTracking.OD_DEFER,
                        RecursiveTracking.ownerDecision(false, true, false, 0, 0, 0, false, CAP));
        Assert.assertEquals("no owner at quiescence, the round budget used up: merged at once", RecursiveTracking.OD_MERGE_UNRESOLVABLE,
                        RecursiveTracking.ownerDecision(false, true, false, 0, 0, 0, true, CAP));
        Assert.assertEquals("no owner tracking at all", RecursiveTracking.OD_MERGE_UNRESOLVABLE,
                        RecursiveTracking.ownerDecision(false, false, false, 0, 0, 0, false, CAP));
    }

    @Test
    public void dl42LaterRoundGrowthMintsTheNewOwnersOrMerges() {
        Assert.assertEquals("decided earlier, unchanged: not pending", RecursiveTracking.OD_NONE,
                        RecursiveTracking.ownerDecision(false, true, false, 2, 0, 2, false, CAP));
        Assert.assertEquals("grown within the cap: the new owners' atoms (earlier ones stay)", RecursiveTracking.OD_MINT_LATER,
                        RecursiveTracking.ownerDecision(false, true, false, 3, 1, 2, false, CAP));
        Assert.assertEquals("grown past the cap: the MERGED atom is added", RecursiveTracking.OD_MERGE_CAP,
                        RecursiveTracking.ownerDecision(false, true, false, CAP + 1, CAP - 1, 2, false, CAP));
        Assert.assertEquals("refused in a later round: the MERGED atom is added", RecursiveTracking.OD_MERGE_REFUSED,
                        RecursiveTracking.ownerDecision(false, true, true, 0, 0, 2, false, CAP));
        Assert.assertEquals("merged is sticky", RecursiveTracking.OD_NONE,
                        RecursiveTracking.ownerDecision(true, true, false, 5, 5, 0, false, CAP));
    }

    @Test
    public void dl42RoundBudgetMergesOnlyPendingDecisions() {
        Assert.assertEquals(RecursiveTracking.OD_MERGE_BUDGET,
                        RecursiveTracking.ownerDecision(false, true, false, 2, 2, 0, true, CAP));
        Assert.assertEquals("a decided, unchanged resolution is not pending: the budget does not touch it", RecursiveTracking.OD_NONE,
                        RecursiveTracking.ownerDecision(false, true, false, 2, 0, 2, true, CAP));
    }

    // ------------------------------------------------------------------
    // The context policy — pure context arithmetic.
    // ------------------------------------------------------------------
    @Test
    public void ownerMethodContextIsStructural() {
        // OWNER(Y) is keyed by Y's identity (site + context) — two owners never share it.
        Object ownerSite = new Object();
        HeapContext ownerCtx = HeapContext.of(List.of(ContextElement.ofOwner(new Object(), "outer")));
        MethodContext m = MethodContext.owner(ownerSite, ownerCtx);
        Assert.assertTrue(m.isOwner());
        Assert.assertFalse(m.isStatic());
        Assert.assertEquals(MethodContext.owner(ownerSite, ownerCtx), m);
        Assert.assertNotEquals(MethodContext.owner(new Object(), ownerCtx), m);
        Assert.assertNotEquals(MethodContext.owner(ownerSite, HeapContext.EMPTY), m);
    }

    @Test
    public void staticChainIsBoundedAtCtxk() {
        // the default bound, then an explicit bound k=6 (the nested callers are kept)
        for (int k : new int[]{ContextPolicy.CTXK, 6}) {
            MethodContext c = MethodContext.UNKNOWN;
            for (int i = 0; i < k + 3; i++) {
                c = MethodContext.staticCtx(new ContextElement(null, i), c, k);
            }
            int depth = 0;
            int expectBci = k + 2;
            for (MethodContext p = c; p != null && p.isStatic(); p = p.caller) {
                Assert.assertEquals("the nearest elements, newest first (k=" + k + ")", expectBci--, p.call.bci);
                depth++;
            }
            Assert.assertEquals("only the nearest k elements can enter a context", k, depth);
        }
        Assert.assertEquals("the default overload uses CTXK", MethodContext.staticCtx(new ContextElement(null, 1), MethodContext.UNKNOWN),
                        MethodContext.staticCtx(new ContextElement(null, 1), MethodContext.UNKNOWN, ContextPolicy.CTXK));
    }

    @Test
    public void staticAllocationContextKeepsTheNearestKElements() {
        // the default bound, then an explicit bound k=6 (the k-suffix order beyond one element)
        for (int k : new int[]{ContextPolicy.CTXK, 6}) {
            MethodContext c = MethodContext.UNKNOWN;
            for (int i = 0; i < k + 2; i++) {
                c = MethodContext.staticCtx(new ContextElement(null, 100 + i), c, k);
            }
            long[] counters = new long[ContextPolicy.CIDX_COUNT];
            HeapContext ctx = k == ContextPolicy.CTXK
                            ? DefaultContextPolicy.contextForAllocation(null, c, null, null, new ContextElement(null, 7), counters)
                            : DefaultContextPolicy.contextForAllocation(null, c, null, null, new ContextElement(null, 7), counters, k);
            List<ContextElement> el = ctx.elements();
            Assert.assertEquals(k, el.size());
            Assert.assertEquals("k-suffix = the MOST RECENT elements: the entering call first", 7, el.get(0).bci);
            for (int j = 1; j < k; j++) {
                Assert.assertEquals("then the static callers, newest first (k=" + k + ")", 100 + k + 1 - (j - 1), el.get(j).bci);
            }
            Assert.assertEquals(1, counters[ContextPolicy.CIDX_CTX_TRUNCATED]);
        }
    }

    @Test
    public void ownerContextRecursionIsCutAtTheRepeat() {
        // a recursive same-site owner chain (e.g. `new Scope(this, ...)`) does not
        // extend the context: [elem] ++ ctx(owner) is cut just before elem's repeat — a counted MERGE.
        Object a = new Object();
        Object b = new Object();
        Object c = new Object();
        ContextElement ea = ContextElement.ofOwner(a, "A");
        ContextElement eb = ContextElement.ofOwner(b, "B");
        ContextElement ec = ContextElement.ofOwner(c, "C");
        long[] counters = new long[ContextPolicy.CIDX_COUNT];
        // the default ctxk=1 keeps only [elem], so a repeat never changes the context: no cut, not counted
        if (ContextPolicy.CTXK == 1) {
            List<ContextElement> t0 = List.of(ea, ec);
            Assert.assertSame(t0, DefaultContextPolicy.recursionCutTail(ea, t0, counters));
            Assert.assertEquals(0, counters[ContextPolicy.CIDX_CTX_RECURSION_CUT]);
        }
        // the cut itself at an explicit bound k=6
        final int k = 6;
        // direct self-recursion: ctx(owner) = [A, C] and the new element is A -> tail []
        Assert.assertEquals(List.of(), DefaultContextPolicy.recursionCutTail(ea, List.of(ea, ec), counters, k));
        // mutual recursion: ctx(owner) = [B, A, C] and the new element is A -> tail [B]
        Assert.assertEquals(List.of(eb), DefaultContextPolicy.recursionCutTail(ea, List.of(eb, ea, ec), counters, k));
        Assert.assertEquals(2, counters[ContextPolicy.CIDX_CTX_RECURSION_CUT]);
        // one more cut along an A -> B chain: ctx(owner) = [A, B] and the new element is B -> tail [A]
        List<ContextElement> t1 = DefaultContextPolicy.recursionCutTail(eb, List.of(ea, eb), counters, k);
        Assert.assertEquals(List.of(ea), t1);
        Assert.assertEquals(3, counters[ContextPolicy.CIDX_CTX_RECURSION_CUT]);
        // a repeat at j = k - 1 is left to k-suffix truncation (same kept elements): not cut, not counted
        ContextElement[] deep = new ContextElement[k];
        for (int i = 0; i < deep.length - 1; i++) {
            deep[i] = ContextElement.ofOwner(new Object(), "D" + i);
        }
        deep[deep.length - 1] = ea;
        List<ContextElement> deepTail = List.of(deep);
        Assert.assertSame(deepTail, DefaultContextPolicy.recursionCutTail(ea, deepTail, counters, k));
        Assert.assertEquals(3, counters[ContextPolicy.CIDX_CTX_RECURSION_CUT]);
    }

    @Test
    public void ownerContextWithoutRecursionIsUnchanged() {
        Object a = new Object();
        ContextElement ea = ContextElement.ofOwner(a, "A");
        ContextElement eb = ContextElement.ofOwner(new Object(), "B");
        ContextElement call = new ContextElement(null, 5);
        long[] counters = new long[ContextPolicy.CIDX_COUNT];
        List<ContextElement> tail = List.of(eb, call);
        Assert.assertSame("no repeat: the owner's context is kept as-is", tail, DefaultContextPolicy.recursionCutTail(ea, tail, counters));
        List<ContextElement> empty = List.of();
        Assert.assertSame(empty, DefaultContextPolicy.recursionCutTail(ea, empty, counters));
        // a different site element with an equal printed key is not a repeat (identity = the site object)
        List<ContextElement> sameKey = List.of(ContextElement.ofOwner(new Object(), "A"));
        Assert.assertSame(sameKey, DefaultContextPolicy.recursionCutTail(ea, sameKey, counters));
        Assert.assertEquals(0, counters[ContextPolicy.CIDX_CTX_RECURSION_CUT]);
    }

    @Test
    public void mergedContextsAreDistinguishedFromEmptyAndFromOwnerSpecific() {
        List<ContextElement> els = List.of(new ContextElement(null, 1), new ContextElement(null, 2));
        Assert.assertNotEquals("MERGED is not EMPTY", HeapContext.MERGED, HeapContext.EMPTY);
        Assert.assertNotEquals("the chain-MERGED identity never collides with an owner-specific key", HeapContext.mergedOf(els),
                        HeapContext.of(els));
    }

    @Test
    public void dl34bStaticNoEnteringCallFansThenMerges() {
        // fan first (one call-site context per candidate entering call)...
        Assert.assertEquals(RecursiveTracking.SF_FAN, RecursiveTracking.staticFanDecision(false, 3, false, CAP));
        Assert.assertEquals("at the cap: still the fan", RecursiveTracking.SF_FAN, RecursiveTracking.staticFanDecision(false, CAP, false, CAP));
        // ...MERGE only when the fan is unresolvable or over its cap — never a refusal
        Assert.assertEquals("over the cap", RecursiveTracking.SF_MERGE, RecursiveTracking.staticFanDecision(false, CAP + 1, false, CAP));
        Assert.assertEquals("an unenumerable caller set", RecursiveTracking.SF_MERGE, RecursiveTracking.staticFanDecision(true, 3, false, CAP));
        Assert.assertEquals("no caller, not a world-top entry", RecursiveTracking.SF_MERGE, RecursiveTracking.staticFanDecision(false, 0, false, CAP));
        // a world-top static method has no entering call by construction
        Assert.assertEquals(RecursiveTracking.SF_EMPTY, RecursiveTracking.staticFanDecision(false, 0, true, CAP));
    }

    // ------------------------------------------------------------------
    // The IR ⇄ LFG identity joint: an IR node maps to one LFG vertex; a later (lazy, mid-solve) mint never re-maps it.

    // ------------------------------------------------------------------
    @Test
    public void irLfgJointNeverRemapsANode() {
        LocalFlowGraph frame = new LocalFlowGraph(null);
        Object irNode = new Object();
        Assert.assertNull("an unvisited node has no vertex (the lazy-mint case)", frame.vertexForNode(irNode));
        LocalFlowGraph.LocalVertex first = frame.newVertex(LocalFlowGraph.VertexKind.LOAD);
        frame.registerNodeVertex(irNode, first);
        LocalFlowGraph.LocalVertex late = frame.newVertex(LocalFlowGraph.VertexKind.LOAD);
        frame.registerNodeVertex(irNode, late);
        Assert.assertSame("registration is putIfAbsent: the first identity stays", first, frame.vertexForNode(irNode));
        Assert.assertNotSame(first, late);
        Assert.assertNull(frame.vertexForNode(null));
    }

    // ------------------------------------------------------------------
    // Paths + the EXHAUSTED lineage marker.
    // ------------------------------------------------------------------
    @Test
    public void pathTruncationKeepsTheMostRecentLinks() {
        CallPath p = null;
        Object[] calls = new Object[ContextPolicy.PATHK + 2];
        for (int i = 0; i < calls.length; i++) {
            calls[i] = new Object();
            p = CallPath.push(null, calls[i], p);
        }
        Assert.assertEquals(ContextPolicy.PATHK, p.depth());
        Assert.assertSame("the head is the call that entered the current frame", calls[calls.length - 1], p.call);
    }

    @Test
    public void exhaustedMarkerIsStrippedAtTheRtrackBoundary() {
        Assert.assertNull(CallPath.stripExhausted(CallPath.EXHAUSTED));
        Assert.assertNull(CallPath.stripExhausted(null));
        Object c1 = new Object();
        CallPath withMarker = CallPath.linkOf(null, c1, CallPath.EXHAUSTED);
        CallPath stripped = CallPath.stripExhausted(withMarker);
        Assert.assertNotNull(stripped);
        Assert.assertSame(c1, stripped.call);
        Assert.assertNull("the marker never enters an rtrack path", stripped.next);
        CallPath plain = CallPath.linkOf(null, c1, null);
        Assert.assertSame("a path without the marker is returned as is", plain, CallPath.stripExhausted(plain));
        Assert.assertNotEquals("EXHAUSTED is a path, distinct from the path-free (null) key", null, CallPath.EXHAUSTED);
    }

    // ------------------------------------------------------------------
    // The length-0 proof reads the length stamp — exactly [0,0].
    // ------------------------------------------------------------------
    @Test
    public void lengthZeroProofNeedsTheStampExactlyZero() {
        Assert.assertTrue(RecursiveTracking.stampExactlyZero(ConstantNode.forInt(0)));
        Assert.assertFalse("a non-empty array never gets the proof", RecursiveTracking.stampExactlyZero(ConstantNode.forInt(1)));
    }

    // ------------------------------------------------------------------
    // Soundness: `[]` element stores never kill (index-insensitive member).
    // arr[0] = s1; y = arr[0]; arr[1] = s2; x = arr[0]; — s1 must reach x.
    // ------------------------------------------------------------------
    @Test
    public void arrayElementStoresNeverKill() {
        Object arr = new Object();
        List<PoolAccess> acc = new ArrayList<>();
        PoolAccess s1 = new PoolAccess(0, true, arr, 0, 0, new Object());
        PoolAccess y = new PoolAccess(1, false, arr, 0, 2, new Object());
        PoolAccess s2 = new PoolAccess(2, true, arr, 0, 4, new Object());
        PoolAccess x = new PoolAccess(3, false, arr, 0, 6, new Object());
        acc.add(s1);
        acc.add(y);
        acc.add(s2);
        acc.add(x);
        FramePools killing = FramePools.compute(new FrameCfg(1, new int[][]{new int[0]}, List.copyOf(acc), 0, List.of(), java.util.Set.of()));
        Assert.assertFalse("(the abstract same-receiver kill — correct for a FIELD, the `[]` hole)", killing.connects(s1, x));
        FramePools fp = FramePools.compute(new FrameCfg(1, new int[][]{new int[0]}, List.copyOf(acc), 0, List.of(), java.util.Set.of(arr)));
        Assert.assertTrue("an element store proves no overwrite of another element: s1 reaches x", fp.connects(s1, x));
        Assert.assertTrue(fp.connects(s1, y));
        Assert.assertTrue(fp.connects(s2, x));
    }
}
