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
import java.util.Objects;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.ContextElement;
import com.oracle.svm.hosted.stringanalysis.ContainerAtoms.HeapContext;

/**
 * The context policy of the recursive tracking: the one replaceable piece that decides heap contexts and birth-method
 * returns. The rest of the engine treats {@link HeapContext} as opaque.
 *
 * <p>Also home to the two carried path shapes: {@link CallPath} (the k-suffix of calls a forward position or a backward
 * arrival chain came in through) and {@link MethodContext} (the invocation context of a position: object-sensitive for
 * instance methods, call-site for static methods).
 */
final class ContextPolicy {

    private ContextPolicy() {
    }

    /**
     * The heap-context depth of an atom's identity. Default 1; deeper contexts separate more allocation
     * sites at a higher analysis cost.
     */
    static final int CTXK = Integer.getInteger("svm.stringanalysis.fwd.rtrack.ctxk", 1);
    /** How many calls a forward position / resumed string state remembers. Default 1. */
    static final int PATHK = Integer.getInteger("svm.stringanalysis.fwd.rtrack.pathk", 1);
    /**
     * The path bound of the backward invoke-result descent only ({@link CallPath#pushBackward}, used by
     * {@code RecursiveTracking.invokeResultCase} and {@code bridgedResultCase}); every other push keeps {@link #PATHK}.
     * Default {@link #PATHK}. A deeper bound (e.g. 8) keeps longer owner chains through nested returns
     * ({@code ArrayList.add -> grow -> ... -> newArray}); truncation stays the sound, counted merge.
     */
    static final int PATHK_BACKWARD = Integer.getInteger("svm.stringanalysis.fwd.rtrack.pathk.bwd", PATHK);

    // MethodContext: OWNER(atom) for an instance invocation whose receiver atom is known on the path,
    // STATIC(call, callerCtx) for a static invocation, UNKNOWN otherwise.
    static final class MethodContext {
        final Object ownerSite;            // OWNER: the owner atom's site (registry identity)
        final HeapContext ownerCtx;        // OWNER: the owner atom's context
        final ContextElement call;         // STATIC: the entering call site
        final MethodContext caller;        // STATIC: the caller invocation's context
        final boolean unknown;

        private MethodContext(Object ownerSite, HeapContext ownerCtx, ContextElement call, MethodContext caller,
                        boolean unknown) {
            this.ownerSite = ownerSite;
            this.ownerCtx = ownerCtx;
            this.call = call;
            this.caller = caller;
            this.unknown = unknown;
        }

        static final MethodContext UNKNOWN = new MethodContext(null, null, null, null, true);

        static MethodContext owner(Object ownerSite, HeapContext ownerCtx) {
            return new MethodContext(Objects.requireNonNull(ownerSite), Objects.requireNonNull(ownerCtx), null, null,
                            false);
        }

        /**
         * STATIC(call, caller). The caller chain keeps at most {@link #CTXK} static links: only the nearest CTXK
         * elements can enter a heap context (the k-suffix), so the cut loses nothing and keeps the value finite (it is
         * part of sink/walk keys).
         */
        static MethodContext staticCtx(ContextElement call, MethodContext caller) {
            return staticCtx(call, caller, CTXK);
        }

        /** {@link #staticCtx(ContextElement, MethodContext)} at the context bound {@code k} (production: {@link #CTXK}). */
        static MethodContext staticCtx(ContextElement call, MethodContext caller, int k) {
            return new MethodContext(null, null, Objects.requireNonNull(call), boundedCaller(caller, k - 1), false);
        }

        private static MethodContext boundedCaller(MethodContext caller, int keep) {
            if (caller == null || !caller.isStatic()) {
                return caller != null && caller.isOwner() ? caller : null;
            }
            if (keep <= 0) {
                return null;
            }
            return new MethodContext(null, null, caller.call, boundedCaller(caller.caller, keep - 1), false);
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof MethodContext o)) {
                return false;
            }
            return unknown == o.unknown && ownerSite == o.ownerSite && Objects.equals(ownerCtx, o.ownerCtx) &&
                            Objects.equals(call, o.call) && Objects.equals(caller, o.caller);
        }

        @Override
        public int hashCode() {
            int h = unknown ? 1 : 0;
            h = h * 31 + System.identityHashCode(ownerSite);
            h = h * 31 + (ownerCtx != null ? ownerCtx.hashCode() : 0);
            h = h * 31 + (call != null ? call.hashCode() : 0);
            return h * 31 + (caller != null ? caller.hashCode() : 0);
        }

        boolean isOwner() {
            return !unknown && ownerSite != null;
        }

        boolean isStatic() {
            return !unknown && call != null;
        }

        @Override
        public String toString() {
            if (unknown) {
                return "mctx[?]";
            }
            if (ownerSite != null) {
                return "mctx[obj@" + ownerSite + ownerCtx + "]";
            }
            return "mctx[" + call + (caller != null ? "," + caller : "") + "]";
        }
    }

    // CallPath: the immutable cons of (caller frame, entering call) links, head = the most recent call. Truncated at
    // PATHK on push: the oldest link drops (a sound, counted merge). Structural equality: two routes reaching a
    // position with equal truncated suffixes walk once (the visited key).
    static final class CallPath {
        final LocalFlowGraph callerFrame;
        final Object call;       // the call site identity (LocalVertex or IR invoke node)
        /** The caller invocation's method context (a forward walk's matched return restores it); null where unknown. */
        final Object callerMctx;
        final CallPath next;
        private final int hash;

        private CallPath(LocalFlowGraph callerFrame, Object call, Object callerMctx, CallPath next) {
            this.callerFrame = callerFrame;
            this.call = call;
            this.callerMctx = callerMctx;
            this.next = next;
            this.hash = System.identityHashCode(callerFrame) * 31 + System.identityHashCode(call) * 7 +
                            (callerMctx != null ? callerMctx.hashCode() * 13 : 0) + (next != null ? next.hash : 0);
        }

        static final CallPath EMPTY = null; // the empty path is null by convention

        /**
         * The path of a resumed string state whose recorded path is used up (or was never recorded). It keeps the
         * state in the resumed lineage, apart from the path-free ordinary states, because its "every caller" return
         * must be the true caller set: the LFG's caller index lists only call sites some Phase-A walk materialised,
         * which is complete for a value that entered the frame through a call, not for a value resumed at a load
         * inside it. A marker link (no frame, no call); never pushed into rtrack ({@link #stripExhausted} removes it
         * where the path reaches rtrack).
         */
        static final CallPath EXHAUSTED = new CallPath(null, "EXHAUSTED", null, null);

        /** The path with a terminal EXHAUSTED marker removed (rtrack's own paths never carry it). */
        static CallPath stripExhausted(CallPath p) {
            if (p == null || p == EXHAUSTED) {
                return null;
            }
            CallPath rest = stripExhausted(p.next);
            return rest == p.next ? p : new CallPath(p.callerFrame, p.call, p.callerMctx, rest);
        }

        /** The pathTruncated counter: every push that dropped an old link. */
        static final AtomicLong PATH_TRUNCATED = new AtomicLong();

        /**
         * A link without truncation or counting (the caller guarantees the depth does not grow, e.g. rebuilding an
         * existing path with its method contexts dropped).
         */
        static CallPath linkOf(LocalFlowGraph callerFrame, Object call, CallPath next) {
            return new CallPath(callerFrame, call, null, next);
        }

        /** Push one link, truncating past {@link ContextPolicy#PATHK} (a merge, counted in {@link #PATH_TRUNCATED}). */
        static CallPath push(LocalFlowGraph callerFrame, Object call, CallPath path) {
            return push(callerFrame, call, null, path);
        }

        static CallPath push(LocalFlowGraph callerFrame, Object call, Object callerMctx, CallPath path) {
            return push(callerFrame, call, callerMctx, path, PATHK);
        }

        /** A push of the backward invoke-result descent, truncated at {@link ContextPolicy#PATHK_BACKWARD}. */
        static CallPath pushBackward(LocalFlowGraph callerFrame, Object call, Object callerMctx, CallPath path) {
            return push(callerFrame, call, callerMctx, path, PATHK_BACKWARD);
        }

        /**
         * Census: backward pushes that keep more than {@link ContextPolicy#PATHK} links. JVM-wide, like
         * {@link #PATH_TRUNCATED}; an engine prints its delta ({@code RecursiveTracking.deepPushesAtStart}).
         */
        static final AtomicLong BACKWARD_DEEP_PUSHES = new AtomicLong();

        /**
         * A push truncated at the bound {@code k} (production: {@link ContextPolicy#PATHK} or
         * {@link ContextPolicy#PATHK_BACKWARD}; JUnit tests pass other bounds).
         */
        static CallPath push(LocalFlowGraph callerFrame, Object call, Object callerMctx, CallPath path, int k) {
            CallPath raw = new CallPath(callerFrame, call, callerMctx, path);
            int n = 0;
            CallPath p = raw;
            while (p != null) {
                n++;
                p = p.next;
            }
            if (k > PATHK && n > PATHK) {
                BACKWARD_DEEP_PUSHES.incrementAndGet();
            }
            if (n <= k) {
                return raw;
            }
            PATH_TRUNCATED.incrementAndGet();
            // Keep the k most recent links; never drop the call entering the current frame.
            return rebuild(raw, k);
        }

        /** The first {@code keep} links of {@code p} (the most recent ones), as a fresh chain. */
        private static CallPath rebuild(CallPath p, int keep) {
            if (p == null || keep <= 0) {
                return null;
            }
            return new CallPath(p.callerFrame, p.call, p.callerMctx, rebuild(p.next, keep - 1));
        }

        /** Recursion folding: is this link a fold link {@code F(root, rootMctx, owner, next)}? */
        boolean isFold() {
            return call instanceof FoldInfo;
        }

        /** Recursion folding: the fold of a fold link (null for every other link). */
        FoldInfo fold() {
            return call instanceof FoldInfo fi ? fi : null;
        }

        /**
         * Recursion folding: the folding push of call {@code call} in frame {@code f} (path {@code path}, the frame's
         * mctx {@code mctxF}) into the callee frame {@code g}, or null when the push does not fold (the caller then does
         * the plain {@link #push}). Detection is structural on method identity (frames), never on mctx: scan from the
         * head with {@code f} as the virtual link -1; stop at the first link that is not a plain call link (a fold link,
         * a desugared/model/thread-local link, EXHAUSTED, any link with no caller frame). A hit is a plain link whose
         * caller frame is {@code g} (or {@code f == g}), or a barrier fold whose root is {@code g}.
         * <ul>
         * <li>Case A: hit at plain {@code L[i]}, {@code L[i+1]} not a fold: the path becomes the new fold
         * {@code F(g, L[i].callerMctx (mctxF when i = -1), owner, L[i+1]…)}; edges {new, L[0..i]}.</li>
         * <li>Case B: hit at plain {@code L[i]}, {@code L[i+1]} a fold F0 ({@code g} is a member of F0): edges {new,
         * L[0..i]} go into F0's registry; the path becomes {@code L[i+1]} (F0).</li>
         * <li>Case C: the barrier fold {@code L[j]} has root {@code g}: edges {new, L[0..j-1]} into it; the path becomes
         * {@code L[j]}.</li>
         * </ul>
         * The edge targets: {@code new} → {@code g}, {@code L[0]} → {@code f}, {@code L[k]} → {@code L[k-1].callerFrame}.
         * {@link FoldPush#edges()}/{@link FoldPush#targets()} are in registration order {@code L[last] … L[0], new}.
         * A pure function of the path value. {@code owner} is the walking atom's table (the registry owner of a new
         * fold; a merge keeps the existing fold's owner). {@code k} = the path bound (production:
         * {@link ContextPolicy#PATHK}).
         */
        static FoldPush foldPush(LocalFlowGraph f, Object call, Object mctxF, CallPath path, LocalFlowGraph g, Object owner, int k) {
            if (f == null || g == null || call == null) {
                return null;
            }
            java.util.ArrayList<CallPath> links = new java.util.ArrayList<>(k + 1);
            int hit = -2; // -2 = none
            CallPath barrierFold = null;
            if (f == g) {
                hit = -1;
            } else {
                for (CallPath p = path; p != null; p = p.next) {
                    if (p.isFold()) {
                        if (p.fold().root == g) {
                            barrierFold = p; // Case C
                        }
                        break;
                    }
                    if (!isPlainLink(p)) {
                        break; // a barrier
                    }
                    links.add(p);
                    if (p.callerFrame == g) {
                        hit = links.size() - 1;
                        break;
                    }
                }
            }
            if (hit == -2 && barrierFold == null) {
                return null;
            }
            java.util.ArrayList<LocalFlowGraph> targets = new java.util.ArrayList<>(links.size() + 1);
            java.util.ArrayList<FoldEdge> edges = new java.util.ArrayList<>(links.size() + 1);
            targets.add(g);
            edges.add(new FoldEdge(f, call, mctxF));
            int last = barrierFold != null ? links.size() - 1 : hit; // the last removed plain link
            for (int i = 0; i <= last; i++) {
                CallPath l = links.get(i);
                targets.add(i == 0 ? f : links.get(i - 1).callerFrame);
                edges.add(new FoldEdge(l.callerFrame, l.call, l.callerMctx));
            }
            // Registration order = L(last) … L0, new. Registering an edge can deliver it inline to an existing waiter
            // (a shared (owner, root) registry, always so in Case B), which enqueues a position at the edge's caller
            // frame; that frame's own entering edge must already be registered, so the oldest removed link goes first
            // and `new` (whose delivery creates (f, F)) last.
            java.util.Collections.reverse(targets);
            java.util.Collections.reverse(edges);
            if (barrierFold != null) {
                return new FoldPush(barrierFold, barrierFold.fold(), List.copyOf(targets), List.copyOf(edges), 'C');
            }
            CallPath next = hit == -1 ? path : links.get(hit).next;
            if (next != null && next.isFold()) {
                return new FoldPush(next, next.fold(), List.copyOf(targets), List.copyOf(edges), 'B');
            }
            Object rootMctx = hit == -1 ? mctxF : links.get(hit).callerMctx;
            FoldInfo fi = FoldInfo.of(g, rootMctx, owner);
            CallPath raw = new CallPath(null, fi, null, next);
            CallPath folded = raw;
            if (raw.depth() > k) {
                PATH_TRUNCATED.incrementAndGet(); // F counts as one link; truncation below it is the plain counted merge
                folded = rebuild(raw, k);
            }
            return new FoldPush(folded, fi, List.copyOf(targets), List.copyOf(edges), 'A');
        }

        /** A plain forward call link: a caller frame and an LFG call vertex or an IR invoke (the fold scan's non-barrier). */
        static boolean isPlainLink(CallPath p) {
            return p.callerFrame != null && (p.call instanceof LocalFlowGraph.LocalVertex || p.call instanceof jdk.graal.compiler.nodes.Invoke);
        }

        int depth() {
            int d = 0;
            CallPath p = this;
            while (p != null) {
                d++;
                p = p.next;
            }
            return d;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof CallPath other)) {
                return false;
            }
            CallPath a = this;
            CallPath b = other;
            while (a != null && b != null) {
                if (a.callerFrame != b.callerFrame || a.call != b.call || !Objects.equals(a.callerMctx, b.callerMctx)) {
                    return false;
                }
                a = a.next;
                b = b.next;
            }
            return a == null && b == null;
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder("path[");
            CallPath p = this;
            boolean first = true;
            while (p != null) {
                if (!first) {
                    sb.append("; ");
                }
                first = false;
                // Name the call site (caller method @ bci) — dump/diagnostic text only
                if (p.callerFrame != null && p.callerFrame.getMethod() != null) {
                    sb.append(p.callerFrame.getMethod().format("%h.%n")).append('@');
                    if (p.call instanceof LocalFlowGraph.LocalVertex cv) {
                        sb.append(cv.bci);
                    } else if (p.call instanceof jdk.graal.compiler.nodes.Invoke inv) {
                        sb.append(inv.bci());
                    } else {
                        sb.append(p.call);
                    }
                } else {
                    sb.append(p.call);
                }
                p = p.next;
            }
            return sb.append(']').toString();
        }
    }

    // Recursion folding of the forward call path.

    /**
     * The identity of a fold link: {@code root} = the frame recursion re-entered, {@code rootMctx} = the
     * mctx of the root's outer invocation (its exit restores it), {@code owner} = the table of the atom whose walk
     * created the fold (the edge registry's owner). Interned, so the link's identity-based equality and hash hold. A
     * fold link stores it in {@link CallPath#call} with {@code callerFrame == null} and no caller mctx, so a path reader
     * unaware of folds sees a link with no frame and a non-vertex call (fail-safe).
     */
    static final class FoldInfo {
        final LocalFlowGraph root;
        final Object rootMctx;
        final Object owner;

        private FoldInfo(LocalFlowGraph root, Object rootMctx, Object owner) {
            this.root = root;
            this.rootMctx = rootMctx;
            this.owner = owner;
        }

        private record Key(LocalFlowGraph root, Object rootMctx, Object owner) {
        }

        /** Interned in the owner table's {@code foldIntern} (no JVM-static map outliving the analysis run). */
        static FoldInfo of(LocalFlowGraph root, Object rootMctx, Object owner) {
            ContainerTables.Table t = (ContainerTables.Table) Objects.requireNonNull(owner);
            return t.foldIntern.computeIfAbsent(new Key(Objects.requireNonNull(root), rootMctx, owner), k -> new FoldInfo(((Key) k).root, ((Key) k).rootMctx, ((Key) k).owner));
        }

        @Override
        public String toString() {
            String r = root.getMethod() != null ? root.getMethod().format("%h.%n") : String.valueOf(root);
            return "FOLD[" + r + (rootMctx != null ? " " + rootMctx : "") + "]";
        }
    }

    /** One registered crossing of a fold's recursion: a call {@code call} in {@code callerFrame} under {@code callerMctx}. */
    record FoldEdge(LocalFlowGraph callerFrame, Object call, Object callerMctx) {
    }

    /**
     * The result of a folding push: the new {@code path} (a fold link at its top), the fold whose registry receives the
     * edges, and the edges with their target frames ({@code targets.get(i)} is the frame {@code edges.get(i)} calls
     * into). {@code kind} = 'A' (a new fold), 'B' (merged into the fold below the hit), 'C' (the barrier fold's root).
     */
    record FoldPush(CallPath path, FoldInfo fold, List<LocalFlowGraph> targets, List<FoldEdge> edges, char kind) {
    }

    // The default policy: pure context arithmetic. Owner resolution (a BackwardTask on `this`) lives in
    // RecursiveTracking.
    static final class DefaultContextPolicy {

        /**
         * The heap context of an allocation reached under {@code mctx}: {@code k-suffix([elem] ++ ctx-tail)}, with the
         * owner-site element for ctor/instance allocations and the entering call element for static-method allocations.
         * Truncation merges (sound) and is counted.
         */
        static HeapContext contextForAllocation(AnalysisMethod method, MethodContext mctx, Object ownerSite,
                        HeapContext ownerCtx, ContextElement enteringCall, long[] counters) {
            return contextForAllocation(method, mctx, ownerSite, ownerCtx, enteringCall, counters, CTXK);
        }

        /** {@link #contextForAllocation} at the context bound {@code k} (production: {@link ContextPolicy#CTXK}). */
        static HeapContext contextForAllocation(AnalysisMethod method, MethodContext mctx, Object ownerSite,
                        HeapContext ownerCtx, ContextElement enteringCall, long[] counters, int k) {
            List<ContextElement> tail;
            ContextElement elem;
            if (method != null && !method.isStatic() && ownerSite != null) {
                // Owner-context: [ownerSite] ++ ctx(owner).
                elem = ContextElement.ofOwner(ownerSite, siteKey(ownerSite));
                tail = recursionCutTail(elem, ownerCtx != null ? ownerCtx.elements() : List.of(), counters, k);
            } else if (method != null && !method.isStatic()) {
                // An instance frame with no owner site resolves its owner before this call; reaching here anyway
                // gives the merge-safe EMPTY context.
                elem = null;
                tail = List.of();
            } else {
                // Static: [entering call] ++ methodContext(caller) (the static chain).
                elem = enteringCall;
                tail = staticTail(mctx);
            }
            if (elem == null) {
                return truncated(List.of(), true, counters, k);
            }
            ContextElement[] raw = new ContextElement[tail.size() + 1];
            raw[0] = elem;
            for (int i = 0; i < tail.size(); i++) {
                raw[i + 1] = tail.get(i);
            }
            return truncated(List.of(raw), false, counters, k);
        }

        /**
         * Owner-context recursion cut: when the owner-site element {@code elem} already occurs in the owner's context
         * (a recursive same-site owner chain, e.g. jackson {@code UntypedObjectDeserializerNR$Scope}'s
         * {@code new Scope(this, ...)}), the tail is cut just before that repeat: {@code [elem] ++ ctx(owner)[0..j)}.
         * A pure function of (elem, ownerCtx) that bounds the recursive chain's contexts under any schedule; for a
         * fixed owner context it is a prefix of the k-suffix input, i.e. a coarser truncation: a merge, never a
         * refusal. Soundness across the fixpoint (where owner contexts change) rests, as for truncation, on atoms being
         * multi-object abstractions (the union of their minting contexts). A repeat at j >= CTXK - 1 is left to the
         * k-suffix truncation (same result), so {@code ctxRecursionCut} counts only cuts that change the context.
         */
        static List<ContextElement> recursionCutTail(ContextElement elem, List<ContextElement> tail, long[] counters) {
            return recursionCutTail(elem, tail, counters, CTXK);
        }

        /** {@link #recursionCutTail} at the context bound {@code k} (production: {@link ContextPolicy#CTXK}; JUnit: other bounds). */
        static List<ContextElement> recursionCutTail(ContextElement elem, List<ContextElement> tail, long[] counters, int k) {
            int j = tail.indexOf(elem);
            if (j < 0 || j >= k - 1) {
                return tail;
            }
            if (counters != null) {
                counters[CIDX_CTX_RECURSION_CUT]++;
            }
            return tail.subList(0, j);
        }

        /**
         * The static chain: the entering calls of the static callers, then, where the chain reaches an instance caller
         * with a known owner, that owner's site and context (stopping at the first non-static link would merge e.g. the
         * copy arrays grown by different lists). The caller truncates at CTXK.
         */
        private static List<ContextElement> staticTail(MethodContext mctx) {
            java.util.ArrayList<ContextElement> out = new java.util.ArrayList<>(4);
            MethodContext p = mctx;
            while (p != null && p.isStatic()) {
                out.add(p.call);
                p = p.caller;
            }
            if (p != null && p.isOwner()) {
                out.add(ContextElement.ofOwner(p.ownerSite, siteKey(p.ownerSite)));
                out.addAll(p.ownerCtx.elements());
            }
            return out.isEmpty() ? List.of() : List.copyOf(out);
        }

        /** k-suffix truncation (production k = CTXK): a counted merge, never a refusal. */
        private static HeapContext truncated(List<ContextElement> raw, boolean forceEmpty, long[] counters, int k) {
            if (forceEmpty || raw.isEmpty() || k <= 0) {
                return HeapContext.EMPTY;
            }
            if (raw.size() > k && counters != null) {
                counters[CIDX_CTX_TRUNCATED]++;
            }
            // The k-suffix = the k most recent elements = the first k of this newest-first list.
            List<ContextElement> kept = raw.size() <= k ? raw : raw.subList(0, k);
            return intern(kept);
        }

        private static java.util.concurrent.ConcurrentHashMap<List<ContextElement>, HeapContext> INTERN = new java.util.concurrent.ConcurrentHashMap<>();

        private static HeapContext intern(List<ContextElement> elements) {
            if (elements.isEmpty()) {
                return HeapContext.EMPTY;
            }
            List<ContextElement> key = List.copyOf(elements);
            HeapContext fresh = HeapContext.of(key);
            HeapContext interned = INTERN.putIfAbsent(key, fresh);
            return interned != null ? interned : fresh;
        }
    }

    /** A deterministic textual key for an atom site (the owner element's canonical key). */
    static String siteKey(Object site) {
        if (site instanceof LocalFlowGraph.LocalVertex v) {
            Object n = v.irNode;
            String m = v.owner != null && v.owner.getMethod() != null ? TransferFacts.methodFlowKey(v.owner.getMethod()) : "?";
            if (n instanceof jdk.graal.compiler.graph.Node node) {
                return m + "#n" + node.getId();
            }
            return m + "#v" + v.id;
        }
        return String.valueOf(site);
    }

    // Counter sink indices (shared with RecursiveTracking's counters).
    static final int CIDX_CTX_TRUNCATED = 0;
    static final int CIDX_CTX_MERGE_OWNER_UNKNOWN = 1;
    static final int CIDX_CTX_MERGE_STATIC_UNKNOWN = 2;
    static final int CIDX_PATH_TRUNCATED = 3;
    static final int CIDX_PATH_EXHAUSTED_FALLBACK = 4;
    static final int CIDX_CALLER_FAN_FALLBACK = 5;
    static final int CIDX_LENGTH_ZERO_PROOFS = 6;
    static final int CIDX_CTX_RECURSION_CUT = 7;
    static final int CIDX_COUNT = 8;
    static final String[] COUNTER_NAMES = {
                    "ctxTruncated", "ctxMergeOwnerUnknown", "ctxMergeStaticUnknown",
                    "pathTruncated", "pathExhaustedFallback", "callerFanFallback", "lengthZeroProofs",
                    "ctxRecursionCut"
    };
}
