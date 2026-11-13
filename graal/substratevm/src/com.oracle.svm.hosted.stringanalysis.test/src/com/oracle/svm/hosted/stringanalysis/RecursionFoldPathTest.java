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

import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.ContextElement;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.CallPath;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.FoldEdge;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.FoldPush;
import com.oracle.svm.hosted.stringanalysis.ContextPolicy.MethodContext;

/**
 * Recursion folding: the pure arithmetic of {@link CallPath#foldPush} (cases A/B/C, direct recursion, barriers,
 * truncation keeping the fold, equality), the knob-0 identity (a disabled fold never applies, so the crossing keeps the
 * plain push), the edge registry
 * ({@code Table.foldEdges}: keyed (owner, root) and target, grow-only, deduped, independent of a fold's {@code next})
 * and the caller-cut static mctx {@code STATIC(c, null)} (= caller UNKNOWN).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode"})
public class RecursionFoldPathTest {

    private static LocalFlowGraph frame() {
        return new LocalFlowGraph(null);
    }

    private static int vid;

    /** A plain call identity (an LFG call vertex). */
    private static LocalFlowGraph.LocalVertex call() {
        return new LocalFlowGraph.LocalVertex(null, vid++, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
    }

    private static final ContainerTables.Table OWNER = new ContainerTables.Table("owner", false);

    /**
     * The path bound of these structural cases, passed explicitly: the default bound is 1, under which the multi-link
     * folds below would truncate to one link. {@link #truncationKeepsTheFold} runs at the default and at K.
     */
    private static final int K = 6;

    private static CallPath push(LocalFlowGraph callerFrame, Object call, Object callerMctx, CallPath path) {
        return CallPath.push(callerFrame, call, callerMctx, path, K);
    }

    private static FoldPush foldPush(LocalFlowGraph f, Object call, Object mctxF, CallPath path, LocalFlowGraph g, Object owner) {
        return CallPath.foldPush(f, call, mctxF, path, g, owner, K);
    }

    @Test
    public void nonRecursivePushDoesNotFold() {
        LocalFlowGraph a = frame();
        LocalFlowGraph f = frame();
        LocalFlowGraph g = frame();
        CallPath p = push(a, call(), "ma", null);
        Assert.assertNull(foldPush(f, call(), "mf", p, g, OWNER));
        Assert.assertNull("the empty path, f != g", foldPush(f, call(), "mf", null, g, OWNER));
    }

    @Test
    public void directRecursionCaseA() {
        LocalFlowGraph a = frame();
        LocalFlowGraph f = frame();
        CallPath p = push(a, call(), "ma", null);
        Object c = call();
        FoldPush fp = foldPush(f, c, "mf", p, f, OWNER);
        Assert.assertNotNull(fp);
        Assert.assertEquals('A', fp.kind());
        Assert.assertTrue(fp.path().isFold());
        Assert.assertNull("a fold link has no caller frame (fail-safe)", fp.path().callerFrame);
        Assert.assertNull(fp.path().callerMctx);
        Assert.assertSame(f, fp.fold().root);
        Assert.assertEquals("mf", fp.fold().rootMctx);
        Assert.assertSame(OWNER, fp.fold().owner);
        Assert.assertSame("F.next = the path entering the root", p, fp.path().next);
        Assert.assertEquals(List.of(new FoldEdge(f, c, "mf")), fp.edges());
        Assert.assertEquals(List.of(f), fp.targets());
    }

    @Test
    public void mutualRecursionCaseA() {
        // a -> g -> x -> f, then f calls g: the hit is the link whose caller frame is g (L[1])
        LocalFlowGraph a = frame();
        LocalFlowGraph g = frame();
        LocalFlowGraph x = frame();
        LocalFlowGraph f = frame();
        Object c3 = call();
        Object c2 = call();
        Object c1 = call();
        CallPath l3 = push(a, c3, "ma", null); // a -> g
        CallPath l2 = push(g, c2, "mg", l3); // g -> x
        CallPath l1 = push(x, c1, "mx", l2); // x -> f
        Object c = call();
        FoldPush fp = foldPush(f, c, "mf", l1, g, OWNER);
        Assert.assertEquals('A', fp.kind());
        Assert.assertSame(g, fp.fold().root);
        Assert.assertEquals("rootMctx = the root's outer invocation (L[i].callerMctx)", "mg", fp.fold().rootMctx);
        Assert.assertSame(l3, fp.path().next);
        Assert.assertEquals("registration order L[1], L[0], new", List.of(new FoldEdge(g, c2, "mg"), new FoldEdge(x, c1, "mx"), new FoldEdge(f, c, "mf")), fp.edges());
        Assert.assertEquals("targets: L[1] -> L[0].callerFrame, L[0] -> f, new -> g", List.of(x, f, g), fp.targets());
        Assert.assertEquals(2, fp.path().depth());
    }

    @Test
    public void mergeIntoTheFoldBelowCaseB() {
        LocalFlowGraph a = frame();
        LocalFlowGraph g = frame();
        LocalFlowGraph h = frame();
        CallPath entry = push(a, call(), "ma", null);
        CallPath fold = foldPush(g, call(), "mg", entry, g, OWNER).path(); // F(g)
        Object cgh = call();
        CallPath atH = push(g, cgh, "mg2", fold); // g -> h under F
        Object chg = call();
        FoldPush fp = foldPush(h, chg, "mh", atH, g, new ContainerTables.Table("walker", false) /* another walker: the fold keeps its owner */);
        Assert.assertEquals('B', fp.kind());
        Assert.assertSame(fold, fp.path());
        Assert.assertSame(OWNER, fp.fold().owner);
        Assert.assertEquals(List.of(new FoldEdge(g, cgh, "mg2"), new FoldEdge(h, chg, "mh")), fp.edges());
        Assert.assertEquals(List.of(h, g), fp.targets());
        // direct recursion of a member under F (f == g, the path top is F): Case B, registered into F
        FoldPush self = foldPush(h, call(), "mh", fold, h, OWNER);
        Assert.assertEquals('B', self.kind());
        Assert.assertSame(fold, self.path());
    }

    @Test
    public void barrierFoldWithTheRootCaseC() {
        LocalFlowGraph a = frame();
        LocalFlowGraph g = frame();
        LocalFlowGraph x = frame();
        LocalFlowGraph y = frame();
        CallPath fold = foldPush(g, call(), "mg", push(a, call(), "ma", null), g, OWNER).path();
        Object c = call();
        FoldPush fp = foldPush(x, c, "mx", fold, g, OWNER);
        Assert.assertEquals('C', fp.kind());
        Assert.assertSame(fold, fp.path());
        Assert.assertEquals(List.of(new FoldEdge(x, c, "mx")), fp.edges());
        Object cyx = call();
        CallPath atX = push(y, cyx, "my", fold); // y -> x under F
        FoldPush fp2 = foldPush(x, c, "mx", atX, g, OWNER);
        Assert.assertEquals('C', fp2.kind());
        Assert.assertEquals(List.of(new FoldEdge(y, cyx, "my"), new FoldEdge(x, c, "mx")), fp2.edges());
        Assert.assertEquals(List.of(x, g), fp2.targets());
    }

    @Test
    public void barriersStopTheScan() {
        LocalFlowGraph a = frame();
        LocalFlowGraph g = frame();
        LocalFlowGraph m = frame();
        LocalFlowGraph f = frame();
        CallPath below = push(g, call(), "mg", push(a, call(), "ma", null)); // g -> m
        // a model / desugared / thread-local link: a caller frame but no LFG call vertex or IR invoke
        CallPath model = push(m, new Object(), "mm", below);
        Assert.assertNull("a non-plain link is a barrier", foldPush(f, call(), "mf", model, g, OWNER));
        CallPath exhausted = CallPath.EXHAUSTED;
        Assert.assertFalse(exhausted.isFold());
        Assert.assertNull("EXHAUSTED is a barrier", foldPush(f, call(), "mf", push(m, call(), "mm", exhausted), g, OWNER));
        // a fold with another root is a barrier too, even when g is further down
        LocalFlowGraph r = frame();
        CallPath otherFold = foldPush(r, call(), "mr", below, r, OWNER).path();
        Assert.assertNull(foldPush(f, call(), "mf", otherFold, g, OWNER));
        // but the plain links above a barrier are scanned
        Assert.assertNotNull(foldPush(f, call(), "mf", push(g, call(), "mg", model), g, OWNER));
    }

    @Test
    public void truncationKeepsTheFold() {
        truncationKeepsTheFold(ContextPolicy.PATHK);
        truncationKeepsTheFold(K);
    }

    private static void truncationKeepsTheFold(int k) {
        LocalFlowGraph f = frame();
        CallPath p = null;
        for (int i = 0; i < k; i++) {
            p = CallPath.push(frame(), call(), "m" + i, p, k);
        }
        Assert.assertEquals(k, p.depth());
        FoldPush fp = CallPath.foldPush(f, call(), "mf", p, f, OWNER, k); // i = -1: F on top of a full path
        Assert.assertEquals("F counts as one link, truncated at the bound", k, fp.path().depth());
        Assert.assertTrue(fp.path().isFold());
        // plain links pushed above F: F drops at the bottom as the oldest link, but every surviving copy keeps it
        CallPath q = fp.path();
        for (int i = 0; i < k - 1; i++) {
            q = CallPath.push(frame(), call(), "n" + i, q, k);
        }
        Assert.assertEquals(k, q.depth());
        CallPath bottom = q;
        while (bottom.next != null) {
            bottom = bottom.next;
        }
        Assert.assertTrue("the rebuilt copy of F carries its FoldInfo (k=" + k + ")", bottom.isFold());
        Assert.assertSame(fp.fold(), bottom.fold());
        CallPath r = CallPath.push(frame(), call(), "z", q, k);
        for (CallPath x = r; x != null; x = x.next) {
            Assert.assertFalse("truncated away: the frame becomes path-less below (k=" + k + ")", x.isFold());
        }
    }

    @Test
    public void equalityIsStructuralOverTheFold() {
        LocalFlowGraph a = frame();
        LocalFlowGraph f = frame();
        CallPath p = push(a, call(), "ma", null);
        Object c = call();
        FoldPush x = foldPush(f, c, "mf", p, f, OWNER);
        FoldPush y = foldPush(f, call(), "mf", push(a, p.call, "ma", null), f, OWNER);
        Assert.assertSame("interned", x.fold(), y.fold());
        Assert.assertEquals(x.path(), y.path());
        Assert.assertEquals(x.path().hashCode(), y.path().hashCode());
        Assert.assertNotEquals("another owner", x.path(), foldPush(f, c, "mf", p, f, new ContainerTables.Table("other", false)).path());
        Assert.assertNotEquals("another root mctx", x.path(), foldPush(f, c, "mf2", p, f, OWNER).path());
        Assert.assertNotEquals("another next", x.path(), foldPush(f, c, "mf", null, f, OWNER).path());
    }

    @Test
    public void registryIsKeyedByOwnerRootAndTarget() {
        ContainerTables.Table t = new ContainerTables.Table("owner", false);
        LocalFlowGraph root = frame();
        LocalFlowGraph x = frame();
        ContainerTables.EntryList<FoldEdge> l = t.foldEdges(root, x);
        Assert.assertSame(l, t.foldEdges(root, x));
        Assert.assertNotSame(l, t.foldEdges(root, root));
        Assert.assertNotSame(l, new ContainerTables.Table("other", false).foldEdges(root, x));
        Object c = call();
        FoldEdge e = new FoldEdge(x, c, "m");
        Assert.assertEquals(0, l.append(e, e));
        Assert.assertEquals("deduped", -1, l.append(new FoldEdge(x, c, "m"), new FoldEdge(x, c, "m")));
        Assert.assertEquals(1, l.append(new FoldEdge(x, c, "m2"), new FoldEdge(x, c, "m2")));
        Assert.assertEquals(2, l.size());
        // two folds of one (owner, root) with different `next` (e.g. a truncated copy) share the registry
        LocalFlowGraph a = frame();
        FoldPush f1 = foldPush(root, call(), "mr", push(a, call(), "ma", null), root, t);
        FoldPush f2 = foldPush(root, call(), "mr", null, root, t);
        Assert.assertNotEquals(f1.path(), f2.path());
        Assert.assertSame(t.foldEdges(f1.fold().root, x), t.foldEdges(f2.fold().root, x));
    }

    @Test
    public void callerCutStaticContextIsCallerUnknown() {
        ContextElement e = new ContextElement(null, 7);
        MethodContext cut = MethodContext.staticCtx(e, null);
        Assert.assertTrue(cut.isStatic());
        Assert.assertNull(cut.caller);
        Assert.assertEquals("STATIC(c, null) = STATIC(c, UNKNOWN)", cut, MethodContext.staticCtx(e, MethodContext.UNKNOWN));
        MethodContext known = MethodContext.staticCtx(e, MethodContext.staticCtx(new ContextElement(null, 8), null));
        if (ContextPolicy.CTXK >= 2) {
            Assert.assertNotEquals(cut, known);
        } else {
            // ctxk=1: a static context keeps CTXK - 1 = 0 callers, so a known caller is cut as well
            Assert.assertEquals(cut, known);
        }
        // at an explicit bound K >= 2 the known caller is kept
        MethodContext cutK = MethodContext.staticCtx(e, null, K);
        Assert.assertNotEquals(cutK, MethodContext.staticCtx(e, MethodContext.staticCtx(new ContextElement(null, 8), null, K), K));
    }

    /**
     * The edges of one push are in registration order {@code L(last) … L0, new}: the target of every edge
     * is the caller frame of the edge after it (so delivering an edge inline never creates a position whose entering
     * edge is not registered yet), the last edge is {@code new} (target g, caller f), for cases A, B and C.
     */
    @Test
    public void registrationOrderIsOldestFirst() {
        // Case A over 4 removed links: a -> g -> x1 -> x2 -> x3 -> f, then f calls g
        LocalFlowGraph a = frame();
        LocalFlowGraph g = frame();
        LocalFlowGraph x1 = frame();
        LocalFlowGraph x2 = frame();
        LocalFlowGraph x3 = frame();
        LocalFlowGraph f = frame();
        CallPath p = push(a, call(), "ma", null);
        p = push(g, call(), "mg", p);
        p = push(x1, call(), "m1", p);
        p = push(x2, call(), "m2", p);
        p = push(x3, call(), "m3", p);
        Object c = call();
        FoldPush fa = foldPush(f, c, "mf", p, g, OWNER);
        Assert.assertEquals('A', fa.kind());
        assertOldestFirst(fa, f, c, g);
        Assert.assertSame("the oldest removed link (out of the root) goes first", g, fa.edges().get(0).callerFrame());
        // Case B: under F(g), g -> h -> k, then k calls g
        LocalFlowGraph h = frame();
        LocalFlowGraph k = frame();
        CallPath fold = fa.path();
        CallPath atK = push(h, call(), "mh", push(g, call(), "mg3", fold));
        Object ckg = call();
        FoldPush fb = foldPush(k, ckg, "mk", atK, g, OWNER);
        Assert.assertEquals('B', fb.kind());
        assertOldestFirst(fb, k, ckg, g);
        // Case C: under F(g), x1 -> y -> z, then z calls g (the barrier fold's root)
        LocalFlowGraph y = frame();
        LocalFlowGraph z = frame();
        CallPath atZ = push(y, call(), "my", push(x1, call(), "mx1", fold));
        Object czg = call();
        FoldPush fc = foldPush(z, czg, "mz", atZ, g, OWNER);
        Assert.assertEquals('C', fc.kind());
        assertOldestFirst(fc, z, czg, g);
    }

    private static void assertOldestFirst(FoldPush fp, LocalFlowGraph f, Object c, LocalFlowGraph g) {
        int n = fp.edges().size();
        Assert.assertEquals(n, fp.targets().size());
        Assert.assertTrue(n >= 2);
        for (int i = 0; i + 1 < n; i++) {
            Assert.assertSame("target of edge " + i + " = caller frame of edge " + (i + 1), fp.edges().get(i + 1).callerFrame(), fp.targets().get(i));
        }
        Assert.assertSame("the last edge is the new call", f, fp.edges().get(n - 1).callerFrame());
        Assert.assertSame(c, fp.edges().get(n - 1).call());
        Assert.assertSame("the new call enters g", g, fp.targets().get(n - 1));
    }
}
