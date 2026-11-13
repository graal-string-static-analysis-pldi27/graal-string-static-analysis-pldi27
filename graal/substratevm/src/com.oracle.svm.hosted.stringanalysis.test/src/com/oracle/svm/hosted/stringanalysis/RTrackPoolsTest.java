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
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.FrameCfg;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.FramePools;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.MemberPools;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.PoolAccess;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.Table;

/**
 * Reaching-version pool pins of the recursive tracking (including the
 * single-store sub-case): the per-frame reaching-definitions dataflow, its both-direction temporal exactness, the
 * join/loop merge semantics, the receiver-aliasing asymmetry, the desugared
 * copy pair's order, and the cross-frame MERGE. Plus the append/register
 * protocol pins: exactly-once delivery and the refusal rule (a waiter on any
 * list receives the table's refusals).
 */
public class RTrackPoolsTest {

    /**
     * Every ForwardFixpoint solve constructs the recursive engine, which installs its
     * queue as the process-wide {@link ContainerTables#DEFER} hook; these unit tests run the
     * substrate standalone, so they reinstall the inline form (the class's own default).
     */
    @Before
    public void inlineDeferral() {
        ContainerTables.DEFER = Runnable::run;
    }

    private static final Object R1 = new Object();
    private static final Object R2 = new Object();

    private static final class CfgBuilder {
        final int nBlocks;
        final List<int[]> predList = new ArrayList<>();
        final List<PoolAccess> accesses = new ArrayList<>();
        int seq = 0;

        CfgBuilder(int nBlocks) {
            this.nBlocks = nBlocks;
            for (int i = 0; i < nBlocks; i++) {
                predList.add(new int[0]);
            }
        }

        CfgBuilder edge(int from, int to) {
            int[] old = predList.get(to);
            int[] neu = new int[old.length + 1];
            System.arraycopy(old, 0, neu, 0, old.length);
            neu[old.length] = from;
            predList.set(to, neu);
            return this;
        }

        PoolAccess store(int block, int order, Object receiver) {
            return store(block, order, receiver, new Object());
        }

        PoolAccess store(int block, int order, Object receiver, Object node) {
            PoolAccess a = new PoolAccess(seq++, true, receiver, block, order, node);
            accesses.add(a);
            return a;
        }

        PoolAccess load(int block, int order, Object receiver) {
            return load(block, order, receiver, new Object());
        }

        PoolAccess load(int block, int order, Object receiver, Object node) {
            PoolAccess a = new PoolAccess(seq++, false, receiver, block, order, node);
            accesses.add(a);
            return a;
        }

        final List<ContainerTables.PoolEvent> events = new ArrayList<>();

        CfgBuilder invoke(int block, int order) {
            events.add(ContainerTables.PoolEvent.invoke(block, order));
            return this;
        }

        CfgBuilder def(Object receiver, int block, int order) {
            events.add(ContainerTables.PoolEvent.def(receiver, block, order));
            return this;
        }

        FrameCfg build() {
            return new FrameCfg(nBlocks, predList.toArray(new int[0][]), List.copyOf(accesses), 0, List.copyOf(events),
                            java.util.Set.of());
        }

        /** The production adapter's `[]` form — the given receivers are NEVER-KILL. */
        FrameCfg buildNeverKill(Object... receivers) {
            return new FrameCfg(nBlocks, predList.toArray(new int[0][]), List.copyOf(accesses), 0, List.copyOf(events),
                            java.util.Set.of(receivers));
        }
    }

    // ------------------------------------------------------------------
    // (a) the linear example — both temporal directions exact.
    // ------------------------------------------------------------------
    @Test
    public void linearExampleSeparatesBothDirections() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess s1 = b.store(0, 0, R1);
        PoolAccess l1 = b.load(0, 2, R1);
        PoolAccess s2 = b.store(0, 4, R1);
        PoolAccess l2 = b.load(0, 6, R1);
        FramePools fp = FramePools.compute(b.build());
        Assert.assertTrue("S1 reaches L1", fp.reaches(s1, l1));
        Assert.assertFalse("S1 must NOT reach L2 (overwritten direction — the old kill's half)",
                        fp.reaches(s1, l2));
        Assert.assertFalse("S2 must NOT reach L1 (not-yet-stored direction — the direction the kill never could)",
                        fp.reaches(s2, l1));
        Assert.assertTrue("S2 reaches L2", fp.reaches(s2, l2));
        // also separated for connects(): each load follows a same-receiver store with no invoke in between (E_w killed)
        Assert.assertFalse("S1 still does not connect to L2", fp.connects(s1, l2));
        Assert.assertFalse("S2 still does not connect to L1", fp.connects(s2, l1));
        Assert.assertTrue(fp.connects(s1, l1));
        Assert.assertTrue(fp.connects(s2, l2));
    }

    // ------------------------------------------------------------------
    // The same frame runs again on the same object.
    // class Box { String s; String swap(String n) { String old = this.s; this.s = n; return old; } }
    // b.swap(a); r = b.swap(c); — r == a at runtime: the load L (before S) must
    // connect to S (another invocation's S may be current at L).
    // ------------------------------------------------------------------
    @Test
    public void dl36SwapLoadBeforeStoreSeesAnotherInvocationsStore() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess l = b.load(0, 0, R1); // String old = this.s
        PoolAccess st = b.store(0, 2, R1); // this.s = n
        FramePools fp = FramePools.compute(b.build());
        Assert.assertFalse("the in-frame dataflow alone: S does not reach L", fp.reaches(st, l));
        Assert.assertTrue("E_this reaches L (frame entry)", fp.otherInvocationReaches(l));
        Assert.assertTrue("the swap pair connects (a's replace usage is found)", fp.connects(st, l));
    }

    // m(c) { if (c) { this.s = b; return; } this.s = a; m(true); use(this.s); }
    // use reads b, written by the nested invocation of the same frame.
    @Test
    public void dl36NestedReentryAfterInvoke() {
        CfgBuilder b = new CfgBuilder(3);
        b.edge(0, 1).edge(0, 2); // 1: then-arm (returns), 2: else-arm
        PoolAccess sb = b.store(1, 0, R1);
        PoolAccess sa = b.store(2, 0, R1);
        b.invoke(2, 1); // m(true)
        PoolAccess l = b.load(2, 2, R1); // use(this.s)
        FramePools fp = FramePools.compute(b.build());
        Assert.assertFalse("dataflow: S_b (other arm, returns) does not reach L in this invocation", fp.reaches(sb, l));
        Assert.assertTrue("dataflow: S_a reaches L", fp.reaches(sa, l));
        Assert.assertTrue("E is re-generated after the invoke — S_b (nested invocation) connects", fp.connects(sb, l));
        // Control: without the invoke, S_a kills E_this — S_b is separated.
        CfgBuilder c = new CfgBuilder(3);
        c.edge(0, 1).edge(0, 2);
        PoolAccess sb2 = c.store(1, 0, R1);
        c.store(2, 0, R1);
        PoolAccess l2 = c.load(2, 2, R1);
        FramePools fp2 = FramePools.compute(c.build());
        Assert.assertFalse("no invoke between S_a and L: S_b stays separated", fp2.connects(sb2, l2));
    }

    // ------------------------------------------------------------------
    // A receiver redefined in a loop names a different object
    // per iteration — a store on it must not kill the previous iteration's store.
    // Box prev = null;
    // while (c) { Box box = new Box(); box.s = b; /*S2*/ if (prev != null) use(prev.s); /*L*/ box.s = a; /*S1*/ prev = box; }
    // At runtime prev.s is a (S1 of the previous iteration): a must reach L.
    // ------------------------------------------------------------------
    @Test
    public void dl37LoopRedefinedReceiverKeepsThePreviousIterationsStore() {
        Object box = new Object();
        Object prev = new Object();
        CfgBuilder b = new CfgBuilder(4);
        b.edge(0, 1).edge(1, 2).edge(2, 1).edge(1, 3); // 0 entry, 1 header, 2 body, 3 exit
        b.def(prev, 1, -1); // prev = phi(null, box) at the header merge
        b.def(box, 2, 1); // box = new Box()
        PoolAccess s2 = b.store(2, 2, box); // box.s = b
        PoolAccess l = b.load(2, 4, prev); // use(prev.s)
        PoolAccess s1 = b.store(2, 6, box); // box.s = a
        FramePools fp = FramePools.compute(b.build());
        Assert.assertTrue("S1 (previous iteration's object) reaches L", fp.reaches(s1, l));
        Assert.assertTrue("S2 may alias prev (different SSA values): reaches L", fp.reaches(s2, l));
        // The hole the def point closes: without it, S2 (same SSA value) would kill S1.
        CfgBuilder c = new CfgBuilder(4);
        c.edge(0, 1).edge(1, 2).edge(2, 1).edge(1, 3);
        c.store(2, 2, box);
        PoolAccess lc = c.load(2, 4, prev);
        PoolAccess s1c = c.store(2, 6, box);
        FramePools fpc = FramePools.compute(c.build());
        Assert.assertFalse("without the DEF point the same-SSA kill would drop S1", fpc.reaches(s1c, lc));
    }

    // A store whose receiver's definition cannot be located never kills (coarse form, per receiver).
    @Test
    public void dl37NeverKillReceiver() {
        List<PoolAccess> acc = new ArrayList<>();
        PoolAccess s1 = new PoolAccess(0, true, R1, 0, 0, new Object());
        PoolAccess s2 = new PoolAccess(1, true, R1, 0, 2, new Object());
        PoolAccess l = new PoolAccess(2, false, R1, 0, 4, new Object());
        acc.add(s1);
        acc.add(s2);
        acc.add(l);
        FrameCfg cfg = new FrameCfg(1, new int[][]{new int[0]}, acc, 0, List.of(), java.util.Set.of(R1));
        FramePools fp = FramePools.compute(cfg);
        Assert.assertTrue("a never-kill receiver: S1 survives S2", fp.reaches(s1, l));
        Assert.assertTrue(fp.reaches(s2, l));
        Assert.assertTrue("and E_w is never killed either", fp.otherInvocationReaches(l));
    }

    // ------------------------------------------------------------------
    // (b) the control-flow join merges the arms' versions.
    // ------------------------------------------------------------------
    @Test
    public void joinMergesBothArms() {
        CfgBuilder b = new CfgBuilder(4);
        b.edge(0, 1).edge(0, 2).edge(1, 3).edge(2, 3);
        PoolAccess sa = b.store(1, 0, R1);
        PoolAccess sb = b.store(2, 0, R1);
        PoolAccess l = b.load(3, 0, R1);
        PoolAccess sd = b.store(3, 2, R1);
        PoolAccess l2 = b.load(3, 4, R1);
        FramePools fp = FramePools.compute(b.build());
        Assert.assertTrue("S_a reaches the post-join load", fp.reaches(sa, l));
        Assert.assertTrue("S_b reaches the post-join load", fp.reaches(sb, l));
        Assert.assertFalse("S_d (after the load) does not reach it", fp.reaches(sd, l));
        Assert.assertTrue("S_d reaches the later load", fp.reaches(sd, l2));
        Assert.assertFalse("S_a is killed by the later same-receiver S_d", fp.reaches(sa, l2));
        Assert.assertFalse("S_b is killed by the later same-receiver S_d", fp.reaches(sb, l2));
    }

    // ------------------------------------------------------------------
    // (c) the loop — the back edge carries the store to the next
    // iteration's load; the pre-loop version survives too.
    // ------------------------------------------------------------------
    @Test
    public void loopBackEdgeCarriesTheStore() {
        CfgBuilder b = new CfgBuilder(4);
        b.edge(0, 1).edge(1, 2).edge(2, 1).edge(1, 3);
        PoolAccess sp = b.store(0, 0, R1);
        PoolAccess sa = b.store(2, 0, R1);
        PoolAccess l = b.load(1, 0, R1);
        FramePools fp = FramePools.compute(b.build());
        Assert.assertTrue("the loop-body store reaches the header load (back edge)", fp.reaches(sa, l));
        Assert.assertTrue("the pre-loop store still reaches (entry version)", fp.reaches(sp, l));
    }

    // ------------------------------------------------------------------
    // (d) aliasing within the frame — different receiver SSA values
    // never kill each other (aliases may-merge, never separate).
    // ------------------------------------------------------------------
    @Test
    public void aliasingDifferentReceiversMerge() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess sa = b.store(0, 0, R1);
        PoolAccess sb = b.store(0, 2, R2);
        PoolAccess l = b.load(0, 4, R1);
        FramePools fp = FramePools.compute(b.build());
        Assert.assertTrue("same-receiver store reaches", fp.reaches(sa, l));
        Assert.assertTrue("different-receiver store ALSO reaches (may-alias merge)", fp.reaches(sb, l));
    }

    // ------------------------------------------------------------------
    // The single-store sub-case: one store, one load before it, one load after it. The dataflow does not reach the
    // pre-store load (it reads the frame-entry version), but connects() joins it: the frame may run again.
    // ------------------------------------------------------------------
    @Test
    public void singleStoreSeparatesThePrecedingLoad() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess lBefore = b.load(0, 0, R1);
        PoolAccess s = b.store(0, 2, R1);
        PoolAccess lAfter = b.load(0, 4, R1);
        FramePools fp = FramePools.compute(b.build());
        Assert.assertFalse("the dataflow: the load BEFORE the only store is not reached by it", fp.reaches(s, lBefore));
        Assert.assertTrue("the load AFTER the store sees it", fp.reaches(s, lAfter));
        // a precision loss in the safe direction: the frame-entry E_w may hold another invocation's store
        Assert.assertTrue("the pre-store load now CONNECTS to the store", fp.connects(s, lBefore));
        Assert.assertTrue(fp.connects(s, lAfter));
    }

    // ------------------------------------------------------------------
    // The desugared copy pair sits load-before-store at the copy
    // node's position — an object stored before the copy reaches the copy's
    // load; one stored after does not reach it.
    // ------------------------------------------------------------------
    @Test
    public void desugaredCopyPairOrdersLoadBeforeStore() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess sPre = b.store(0, 0, R1);
        // the ArrayCopy node's slot: orders 2 (load) and 3 (store)
        PoolAccess copyLoad = b.load(0, 2, R1);
        PoolAccess copyStore = b.store(0, 3, R1);
        PoolAccess lAfter = b.load(0, 5, R1);
        // The production adapter marks every `[]` receiver never-kill (an index-insensitive element store, and a copy
        // writes a range, proves no overwrite): "the pre-copy store is killed by the copy's store" would be unsound.
        FramePools fp = FramePools.compute(b.buildNeverKill(R1));
        Assert.assertTrue("a store before the copy reaches the copy's desugared load", fp.reaches(sPre, copyLoad));
        Assert.assertFalse("the copy's own store does not reach ITS desugared load (load-before-store order)",
                        fp.reaches(copyStore, copyLoad));
        Assert.assertTrue("the copy's desugared store reaches later loads", fp.reaches(copyStore, lAfter));
        Assert.assertTrue("the pre-copy store SURVIVES the copy (a copy writes a range, never all elements)",
                        fp.reaches(sPre, lAfter));
    }

    // ------------------------------------------------------------------
    // The same-array shift (src == dst, ArrayList.add(int,E)'s
    // arraycopy) composes with the pools — a load-then-store pair at the copy's position,
    // no copy-specific rule. An object stored before the copy reaches the copy's load and,
    // through the desugared store, the post-copy loads; one stored after the copy does not
    // reach the copy's load in straight-line code; in a loop the back edge carries it
    // (loop-carried order from the dataflow, never textual order).
    // ------------------------------------------------------------------
    @Test
    public void selfLoopShiftComposesWithPools() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess sBefore = b.store(0, 0, R1);
        PoolAccess copyLoad = b.load(0, 2, R1);    // DesugaredLoad(src = C)
        PoolAccess copyStore = b.store(0, 3, R1);  // DesugaredStore(dst = C), value = copyLoad
        PoolAccess sAfter = b.store(0, 5, R1);
        PoolAccess lAfter = b.load(0, 7, R1);
        FramePools fp = FramePools.compute(b.buildNeverKill(R1));
        Assert.assertTrue("stored before the shift: read by the copy's load", fp.reaches(sBefore, copyLoad));
        Assert.assertTrue("the shifted copy reaches the later loads", fp.reaches(copyStore, lAfter));
        Assert.assertFalse("stored after the shift: not read by the copy's load (straight line)", fp.reaches(sAfter, copyLoad));
        Assert.assertFalse("the self-loop store does not feed its own load in straight-line code", fp.reaches(copyStore, copyLoad));
        Assert.assertTrue(fp.reaches(sAfter, lAfter));

        // the same shift inside a loop body: block 1 = header, 2 = body, 3 = exit
        CfgBuilder lb = new CfgBuilder(4);
        lb.edge(0, 1).edge(1, 2).edge(2, 1).edge(1, 3);
        PoolAccess lcopyLoad = lb.load(2, 2, R1);
        PoolAccess lcopyStore = lb.store(2, 3, R1);
        PoolAccess lsAfter = lb.store(2, 5, R1);
        FramePools lfp = FramePools.compute(lb.buildNeverKill(R1));
        Assert.assertTrue("loop: the back edge carries the shifted copy to the next iteration's copy load",
                        lfp.reaches(lcopyStore, lcopyLoad));
        Assert.assertTrue("loop: a store after the shift reaches the next iteration's copy load", lfp.reaches(lsAfter, lcopyLoad));
    }

    // ------------------------------------------------------------------
    // The cross-frame MERGE — different frames always connect;
    // same-frame pairs follow the dataflow.
    // ------------------------------------------------------------------
    @Test
    public void crossFrameAlwaysMerges() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess lBefore = b.load(0, 0, R1);
        PoolAccess s = b.store(0, 2, R1);
        PoolAccess lSame = b.load(0, 4, R1);
        FrameCfg cfg = b.build();
        LocalFlowGraph f1 = new LocalFlowGraph(null);
        LocalFlowGraph f2 = new LocalFlowGraph(null);
        Table t = new Table("owner", false);
        MemberPools.setCfgSource((frame, m) -> frame == f1 ? cfg : new FrameCfg(0, new int[0][], List.of()));
        MemberPools pools = new MemberPools("m");
        // connected() is keyed by the IR access node the table entries carry (a key on the PoolAccess record would make
        // every production lookup by node miss). The pre-store load reads E_w (the frame may run again): connected.
        Assert.assertTrue("same-frame pre-store load: connects it (another invocation)",
                        pools.connected(f1, s.node, f1, lBefore.node));
        Assert.assertTrue("same-frame: the reaching connection applies", pools.connected(f1, s.node, f1, lSame.node));
        Assert.assertTrue("cross-frame: v1 always MERGES", pools.connected(f1, s.node, f2, lSame.node));
        Assert.assertTrue("a build-time store (null frame) connects to everything", pools.connected(null, s.node, f1, lBefore.node));
        Assert.assertTrue("an access the scan did not see merges", pools.connected(f1, new Object(), f1, lBefore.node));
        Assert.assertNotNull(t);
    }

    // Through connected(): the linear example stays separated in production lookups.
    @Test
    public void connectedSeparatesTheLinearExample() {
        CfgBuilder b = new CfgBuilder(1);
        PoolAccess s1 = b.store(0, 0, R1);
        PoolAccess l1 = b.load(0, 2, R1);
        PoolAccess s2 = b.store(0, 4, R1);
        PoolAccess l2 = b.load(0, 6, R1);
        FrameCfg cfg = b.build();
        LocalFlowGraph f1 = new LocalFlowGraph(null);
        MemberPools.setCfgSource((frame, m) -> cfg);
        MemberPools pools = new MemberPools("m");
        Assert.assertTrue(pools.connected(f1, s1.node, f1, l1.node));
        Assert.assertFalse("overwritten direction", pools.connected(f1, s1.node, f1, l2.node));
        Assert.assertFalse("not-yet-stored direction", pools.connected(f1, s2.node, f1, l1.node));
        Assert.assertTrue(pools.connected(f1, s2.node, f1, l2.node));
    }

    // The desugared copy is one IR node that is both a load and a store:
    // the lookups by node must find the right half of the pair.
    @Test
    public void desugaredCopyNodeIsFoundAsBothHalves() {
        CfgBuilder b = new CfgBuilder(1);
        Object copyNode = new Object();
        PoolAccess sPre = b.store(0, 0, R1);
        b.load(0, 2, R1, copyNode);
        b.store(0, 3, R1, copyNode);
        PoolAccess lAfter = b.load(0, 5, R1);
        FrameCfg cfg = b.build();
        LocalFlowGraph f1 = new LocalFlowGraph(null);
        MemberPools.setCfgSource((frame, m) -> cfg);
        MemberPools pools = new MemberPools("m");
        Assert.assertTrue("pre-copy store reaches the copy's load half", pools.connected(f1, sPre.node, f1, copyNode));
        Assert.assertTrue("the copy's store half reaches the later load", pools.connected(f1, copyNode, f1, lAfter.node));
        Assert.assertFalse("the copy's store half does not reach its own load half", pools.connected(f1, copyNode, f1, copyNode));
    }

    // Interned sinks: every listener receives every atom/refusal exactly once,
    // whether it attached before or after the element arrived.
    @Test
    public void sinkListenersReceiveEverythingExactlyOnce() {
        ContainerTables.Sink sink = new ContainerTables.Sink("root", 64, 16);
        List<String> a = new ArrayList<>();
        List<String> b = new ArrayList<>();
        Assert.assertTrue(sink.addListener(new ContainerTables.Listener("A", x -> a.add("atom:" + x), r -> a.add("ref:" + r))));
        sink.addAtom("x1");
        sink.refuse(ContainerTables.RTrackRefusal.BACKWARD_BUDGET);
        Assert.assertTrue(sink.addListener(new ContainerTables.Listener("B", x -> b.add("atom:" + x), r -> b.add("ref:" + r))));
        Assert.assertFalse("an equal listener key is a no-op", sink.addListener(new ContainerTables.Listener("A", x -> a.add("dup"), null)));
        sink.addAtom("x2");
        sink.addAtom("x1"); // duplicate: nobody is woken
        Assert.assertEquals(List.of("atom:x1", "ref:BACKWARD_BUDGET", "atom:x2"), a);
        Assert.assertEquals(List.of("atom:x1", "ref:BACKWARD_BUDGET", "atom:x2"), b);
    }

    // ------------------------------------------------------------------
    // The protocols: exactly-once delivery; late registration delivers
    // the existing entries; the refusal rule (a waiter on any list receives the
    // table's refusals — minted before or after its registration).
    // ------------------------------------------------------------------
    @Test
    public void entryListDeliversExactlyOnceAndB1RefusalsReachEveryWaiter() {
        Table t = new Table("owner", false);
        ContainerTables.EntryList<ContainerTables.StoreEntry> list = t.stores("m");
        AtomicInteger delivered = new AtomicInteger();
        List<String> seen = new ArrayList<>();
        ContainerTables.Waiter w = new ContainerTables.Waiter("key1", idx -> {
            delivered.incrementAndGet();
            seen.add(String.valueOf(list.get(idx).node()));
        }, null, r -> seen.add("REFUSAL:" + r));
        list.register(w);
        Assert.assertEquals(0, delivered.get());
        list.append(new ContainerTables.StoreEntry(null, "e0", null, null, null), "k0");
        list.append(new ContainerTables.StoreEntry(null, "e1", null, null, null), "k1");
        Assert.assertEquals(2, delivered.get());
        list.append(new ContainerTables.StoreEntry(null, "e0-dup", null, null, null), "k0"); // dedup: no delivery
        Assert.assertEquals(2, delivered.get());
        // A late waiter receives the existing entries.
        List<String> late = new ArrayList<>();
        ContainerTables.Waiter w2 = new ContainerTables.Waiter("key2", idx -> late.add(String.valueOf(list.get(idx).node())), null,
                        r -> late.add("REFUSAL:" + r));
        list.register(w2);
        Assert.assertEquals(List.of("e0", "e1"), late);
        // a refusal appended after registration reaches waiters on any list.
        t.refuse(ContainerTables.RTrackRefusal.WALK_BUDGET);
        Assert.assertTrue(seen.contains("REFUSAL:WALK_BUDGET"));
        Assert.assertTrue(late.contains("REFUSAL:WALK_BUDGET"));
        // registering on a different list of the same table also delivers the existing refusal.
        ContainerTables.EntryList<ContainerTables.LoadEntry> other = t.loads("m");
        List<String> third = new ArrayList<>();
        ContainerTables.Waiter w3 = new ContainerTables.Waiter("key3", idx -> third.add(String.valueOf(other.get(idx).node())), null,
                        r -> third.add("REFUSAL:" + r));
        other.register(w3);
        Assert.assertEquals(List.of("REFUSAL:WALK_BUDGET"), third);
        // Registration dedup: the same semantic key registers once.
        ContainerTables.Waiter wDup = new ContainerTables.Waiter("key1", idx -> delivered.incrementAndGet(), null,
                        null);
        list.register(wDup); // key1 already present — a no-op registration
        Assert.assertEquals(2, delivered.get());
        Assert.assertEquals(2, list.size());
    }
}
