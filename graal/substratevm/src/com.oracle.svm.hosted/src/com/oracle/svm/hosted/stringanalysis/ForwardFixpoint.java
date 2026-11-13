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

import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.LongAdder;
import java.util.function.Consumer;
import java.util.function.Function;

import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.svm.hosted.NativeImageOptions;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;

import com.oracle.svm.hosted.stringanalysis.TransferFacts.IncompleteFact;
import com.oracle.svm.hosted.stringanalysis.TransferFacts.IncompleteReason;
import com.oracle.svm.hosted.stringanalysis.TransferFacts.UsageFact;

/**
 * The Phase-B driver of the string analysis: it indexes the Phase-A local flow graphs (callers by frame, dispatch
 * resolution with its receiver- and arg-position stamp filters), constructs the engine ({@link RecursiveTracking}),
 * seeds one STRING atom per creation site of an activated heuristic ({@link #seedStringAtoms}), drains the engine to
 * quiescence ({@link #solve}) and emits the atoms' facts into the verdict layer ({@link #emit}). Entry point:
 * {@link #runAndEmit}.
 */
final class ForwardFixpoint {

    // ------------------------------------------------------------------
    // Inputs (Phase A products).
    // ------------------------------------------------------------------
    private final StringUtilizationGraph sug;
    private final Map<AnalysisMethod, LocalFlowGraph> localFlows;
    private final Map<AnalysisMethod, Map<Integer, InvokeTypeFlow>> invokes;
    /** The Phase-A walker (decode, universe and type resolution for the bridge); {@code null} in fixtures. */
    private final LfgWalk lfgWalk;
    /** Fixture support: per-invoke resolved targets (tests inject synthetic universes). */
    private final Map<LocalFlowGraph.LocalVertex, List<DispatchResolution.ResolvedTarget>> testTargets;

    // ------------------------------------------------------------------
    // Indices (deterministic: name-sorted methods, per-graph vertex order).
    // ------------------------------------------------------------------
    // The walk-side indices are keyed by the LocalFlowGraph (the vertex owner), not by the AnalysisMethod: identical in
    // production (1:1), and multi-frame test fixtures, whose methods are all the null key, still resolve their frames.
    /** Callee frame -> the call sites resolving into it ((caller, bci)-deduped); the engine's {@code Bridge.callersOf}. */
    private final Map<LocalFlowGraph, List<CallerSite>> callersOf = new HashMap<>();
    private final java.util.concurrent.ConcurrentHashMap<AnalysisMethod, Map<Integer, List<DispatchResolution.ResolvedTarget>>> resolvedCache = new java.util.concurrent.ConcurrentHashMap<>();

    /** One resolved caller reference (package-private: the reverse travel's view re-keys by frame). */
    record CallerSite(AnalysisMethod caller, LocalFlowGraph.LocalVertex call) {
    }

    // ------------------------------------------------------------------
    // The carried type block (local-only form).
    // ------------------------------------------------------------------

    /**
     * A may-type block: a finite set of widened types, or top ({@code null} set). Interned blocks also carry a
     * {@link #members} array (allocation-free iteration for {@link #subsumes}; a cache, never part of the identity:
     * {@link #equals} compares the sets) and a lazily cached {@link #cachedName} (the tie-break of
     * {@link #canonicalBlockOrder}).
     */
    static final class Block {
        static final Block TOP = new Block(null);
        final Set<AnalysisType> types;
        private final int hash;
        private final AnalysisType[] members;
        private volatile String cachedName;

        private Block(Set<AnalysisType> types) {
            this.types = types;
            this.hash = types == null ? 0 : types.hashCode();
            this.members = types == null ? null : types.toArray(new AnalysisType[0]);
        }

        /**
         * Canonical creation: member-capped ({@link #BLOCK_MEMBER_CAP}; wider sets are top, keep-all) and interned by
         * content so {@code equals} hits the identity fast path. An empty input degrades to top: the lattice has no
         * bottom, so an empty query is treated as the unknown population (conservative). Unreachable today: every
         * construction site guarantees a non-empty input.
         */
        static Block of(Set<AnalysisType> types) {
            return of(types, BLOCK_MEMBER_CAP);
        }

        /** {@link #of(Set)} under an explicit member cap (the JUnit seam for a {@code fwd.blockcap} above the default). */
        static Block of(Set<AnalysisType> types, int memberCap) {
            if (types.isEmpty() || types.size() > memberCap) {
                return TOP;
            }
            Block candidate = new Block(new LinkedHashSet<>(types));
            Block interned = internMap.putIfAbsent(candidate, candidate);
            return interned != null ? interned : candidate;
        }

        static final int BLOCK_MEMBER_CAP = Integer.getInteger("svm.stringanalysis.fwd.blockcap", 32);
        private static final java.util.concurrent.ConcurrentHashMap<Block, Block> internMap = new java.util.concurrent.ConcurrentHashMap<>();

        boolean isTop() {
            return types == null;
        }

        boolean subsumes(Block other) {
            if (other == null || other.isTop()) {
                return isTop();
            }
            if (isTop()) {
                return true;
            }
            // Allocation-free contains-all (containsAll would allocate an iterator per check).
            if (types.size() < other.types.size()) {
                return false;
            }
            for (AnalysisType t : other.members) {
                if (!types.contains(t)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof Block other)) {
                return false;
            }
            if (types == null || other.types == null) {
                return types == other.types;
            }
            return hash == other.hash && types.equals(other.types);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            if (types == null) {
                return "TOP";
            }
            // Computed once per interned block (the tie-break calls toString per incomparable pair).
            String name = cachedName;
            if (name == null) {
                List<String> names = new ArrayList<>();
                for (AnalysisType t : members) {
                    names.add(t.toJavaName(true));
                }
                Collections.sort(names);
                name = names.toString();
                cachedName = name;
            }
            return name;
        }
    }

    private final java.util.concurrent.ConcurrentHashMap<AnalysisType, Set<AnalysisType>> widenMemo = new java.util.concurrent.ConcurrentHashMap<>();
    private final java.util.concurrent.ConcurrentHashMap<LocalFlowGraph.LocalVertex, Block> localBlockMemo = new java.util.concurrent.ConcurrentHashMap<>();

    /** Deterministic declared-type widening. */
    private Set<AnalysisType> widenType(AnalysisType declared) {
        Set<AnalysisType> memo = widenMemo.get(declared);
        if (memo != null) {
            return memo;
        }
        Set<AnalysisType> widened = new LinkedHashSet<>(4);
        widened.add(declared);
        try {
            if (declared.hasSubTypes()) {
                for (AnalysisType sub : declared.getAllSubtypes()) {
                    if (sub.isInterface() || !sub.isAnySubtypeInstantiated()) {
                        continue;
                    }
                    widened.add(sub);
                }
            }
        } catch (Throwable t) {
            widenMemo.put(declared, Set.of(declared));
            return Set.of(declared);
        }
        widenMemo.put(declared, widened);
        return widened;
    }

    private static AnalysisType vertexIdentityType(LocalFlowGraph.LocalVertex vertex) {
        if (vertex.declaredType != null) {
            return vertex.declaredType;
        }
        TypeFlow<?> tf = vertex.typeFlow;
        if (tf != null) {
            try {
                return tf.getDeclaredType();
            } catch (Throwable t) {
                return null;
            }
        }
        return null;
    }

    /**
     * The local block of a vertex, without cross-caller chasing (the forward walk is the cross-caller flow): local
     * sources -> own identity widened; passthrough INTERNAL -> its creator's block; other kinds -> declared-type
     * widening; top on any unresolvable corner.
     */
    Block localBlock(AnalysisMethod method, LocalFlowGraph.LocalVertex vertex, Set<Object> stack) {
        Block memo = localBlockMemo.get(vertex);
        if (memo != null) {
            return memo;
        }
        if (!stack.add(vertex)) {
            return Block.TOP;
        }
        Block block = localBlockUncached(method, vertex, stack);
        stack.remove(vertex);
        localBlockMemo.put(vertex, block);
        return block;
    }

    /**
     * A passthrough's block from its creator's block {@code src}: ⊤ stays ⊤; more than 64 members is ⊤ (the in-edge
     * union cap, independent of {@code fwd.blockcap}); otherwise the member-capped copy.
     */
    static Block passthroughBlock(Block src, int memberCap) {
        if (src.isTop()) {
            return Block.TOP;
        }
        if (src.types.size() > 64) {
            return Block.TOP;
        }
        return Block.of(new LinkedHashSet<>(src.types), memberCap);
    }

    private Block localBlockUncached(AnalysisMethod method, LocalFlowGraph.LocalVertex vertex, Set<Object> stack) {
        if (vertex.kind == LocalFlowGraph.VertexKind.INTERNAL &&
                        ("string-constant".equals(vertex.label) || "new-instance".equals(vertex.label) ||
                                        "container-instance".equals(vertex.label) || "new-array".equals(vertex.label) || "invoke-array".equals(vertex.label) ||
                                        "invoke-return".equals(vertex.label))) {
            AnalysisType own = vertexIdentityType(vertex);
            if (own == null) {
                return Block.TOP;
            }
            return Block.of(new LinkedHashSet<>(widenType(own)));
        }
        if (vertex.kind == LocalFlowGraph.VertexKind.INTERNAL) {
            // A passthrough: every vertex has at most one in-edge, from its creator, so the union is the creator's.
            if (vertex.from != null) {
                return passthroughBlock(localBlock(method, vertex.from, stack), Block.BLOCK_MEMBER_CAP);
            }
            AnalysisType own = vertexIdentityType(vertex);
            if (own == null) {
                return Block.TOP;
            }
            return Block.of(new LinkedHashSet<>(widenType(own)));
        }
        if (vertex.kind == LocalFlowGraph.VertexKind.CLASS_CHECK || vertex.kind == LocalFlowGraph.VertexKind.RETURN_EXIT) {
            return Block.TOP;
        }
        AnalysisType own = vertexIdentityType(vertex);
        if (own == null) {
            return Block.TOP;
        }
        return Block.of(new LinkedHashSet<>(widenType(own)));
    }

    // ------------------------------------------------------------------
    // Counters (print-only: the [sug-fwd] line).
    // ------------------------------------------------------------------

    /** Arg-position consult sites whose CHA fan the receiver stamp shrank. */
    final LongAdder argStampSites = new LongAdder();
    /** Total CHA targets dropped by the arg-position receiver-stamp filter. */
    final LongAdder argStampSkips = new LongAdder();
    // Usage mints suppressed because their arm is provably unreachable for the entry's carried block.
    final LongAdder armSkipVacuous = new LongAdder();
    final LongAdder armSkipNever = new LongAdder();

    /** The stringy declaring types: a terminal's declaring type ({@link StringAtoms#isTerminalTarget}). */
    static boolean isStringyDeclaringType(String declaringClassName) {
        return declaringClassName != null && (SugNameTables.STRINGY_ALLOC_TYPES.contains(declaringClassName) ||
                        SugNameTables.STRINGY_REP_TYPES.contains(declaringClassName));
    }

    /** The detached resolved-target usage sites, one per (frame, call bci, target). Never in the SUG vertex list. */
    private final java.util.concurrent.ConcurrentHashMap<List<Object>, SugVertex> targetUsageSites = new java.util.concurrent.ConcurrentHashMap<>();
    /** The id base of the detached target usage sites (an id at or above it is never a SUG vertex of the graph). */
    static final int TARGET_SITE_ID_BASE = 800_000_000;
    private static final java.util.concurrent.atomic.AtomicInteger TARGET_SITE_IDS = new java.util.concurrent.atomic.AtomicInteger(TARGET_SITE_ID_BASE);

    /**
     * The usage site of a resolved-target receiver call: declared by the target's class, named by the target method
     * with its parameter signature (the whitelists' key format), located at the call. Detached from the SUG vertex list
     * (per-vertex consumers such as INLINE_CACHE see only Phase-A sites, so no new profile entry appears); the verdict
     * reads it only through the candidate's usage tags. Its id is outside the graph's range.
     */
    SugVertex targetUsageSite(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, AnalysisMethod target, String targetDecl) {
        List<Object> k = java.util.Arrays.asList(ctx, call.bci, target != null ? target : targetDecl);
        return targetUsageSites.computeIfAbsent(k, kk -> {
            SugVertex v = new SugVertex(TARGET_SITE_IDS.getAndIncrement());
            v.setEnclosingMethod(ctx);
            v.setDeclaringClass(targetDecl);
            v.setMethodName(target != null ? target.getName() : call.label);
            v.setMethodSignature(target != null ? SiteKeys.formatSignature(target) : "");
            String enc = ctx != null ? ctx.getDeclaringClass().toJavaName(true) : null;
            v.setNodeType(StringAnalysisPolicy.isInternalClass(enc) ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL);
            String loc = ctx != null ? SiteKeys.profileKey(ctx, call.bci) : "fixture#m@" + call.bci;
            v.setSourceLocation(loc);
            v.setSourceKey(loc);
            v.setLabel(targetDecl.substring(targetDecl.lastIndexOf('.') + 1) + "." + v.getMethodName() + "(target)");
            return v;
        });
    }

    /** Frame -> owner method (a load vertex's frame method), covering injected fixture frames. */
    private final Map<LocalFlowGraph, AnalysisMethod> frameMethod = new HashMap<>();
    /** The recursive container-tracking engine; constructed at solve(). */
    private RecursiveTracking rtrack;

    ForwardFixpoint(StringUtilizationGraph sug,
                    Map<AnalysisMethod, LocalFlowGraph> localFlows,
                    Map<AnalysisMethod, Map<Integer, InvokeTypeFlow>> invokes,
                    LfgWalk lfgWalk,
                    Map<LocalFlowGraph.LocalVertex, List<DispatchResolution.ResolvedTarget>> testTargets) {
        this.sug = sug;
        this.localFlows = localFlows;
        this.invokes = invokes;
        this.lfgWalk = lfgWalk;
        this.testTargets = testTargets;
    }

    // ------------------------------------------------------------------
    // Indexing.
    // ------------------------------------------------------------------

    private void index() {
        List<Map.Entry<AnalysisMethod, LocalFlowGraph>> sorted = new ArrayList<>(localFlows.entrySet());
        sorted.sort(Comparator.comparing((Map.Entry<AnalysisMethod, LocalFlowGraph> e) -> TransferFacts.methodFlowKey(e.getKey()))
                        .thenComparing(e -> TransferFacts.methodDescriptorKey(e.getKey())));
        // The discovered frames: every walked frame (sorted) plus any resolved-target frame not in the map (fixtures'
        // injected callee graphs; unreachable in production). Owner method = the map key (null for injected frames).
        Map<LocalFlowGraph, AnalysisMethod> ownerOf = new LinkedHashMap<>();
        ArrayDeque<LocalFlowGraph> pending = new ArrayDeque<>();
        for (Map.Entry<AnalysisMethod, LocalFlowGraph> entry : sorted) {
            ownerOf.putIfAbsent(entry.getValue(), entry.getKey());
            pending.add(entry.getValue());
        }
        Set<LocalFlowGraph> indexed = new HashSet<>();
        Set<String> seenCallers = new HashSet<>();
        while (!pending.isEmpty()) {
            LocalFlowGraph lfg = pending.poll();
            if (!indexed.add(lfg)) {
                continue;
            }
            AnalysisMethod method = ownerOf.get(lfg);
            seenCallers.clear();
            for (LocalFlowGraph.LocalVertex call : lfg.getInvokeVertices()) {
                List<DispatchResolution.ResolvedTarget> probeTargets = resolveTargets(method, call);
                for (DispatchResolution.ResolvedTarget target : probeTargets) {
                    AnalysisMethod callee = target.method();
                    // Keyed by the callee frame: the target's own graph (always in production), else the map lookup;
                    // fixture callees index under their injected frame.
                    LocalFlowGraph calleeFrame = target.lfg() != null ? target.lfg() : localFlows.get(callee);
                    if (calleeFrame == null) {
                        continue;
                    }
                    if (!indexed.contains(calleeFrame)) {
                        pending.add(calleeFrame);
                    }
                    String dedup = callee != null
                                    ? callee.format("%H.%n") + callee.getSignature().toMethodDescriptor() + "#" + call.bci
                                    : "<null>#" + call.bci;
                    if (seenCallers.add(dedup)) {
                        callersOf.computeIfAbsent(calleeFrame, k -> new ArrayList<>(2)).add(new CallerSite(method, call));
                    }
                }
            }
        }
        // The frame -> method snapshot for the bridge.
        frameMethod.putAll(ownerOf);
    }

    // ------------------------------------------------------------------
    // Target resolution (fixture-first; production = deterministic CHA + fallbacks).
    // ------------------------------------------------------------------

    private List<DispatchResolution.ResolvedTarget> resolveTargets(AnalysisMethod caller, LocalFlowGraph.LocalVertex call) {
        if (testTargets != null && testTargets.containsKey(call)) {
            List<DispatchResolution.ResolvedTarget> resolved = testTargets.get(call);
            return resolved == null ? List.of() : resolved;
        }
        if (caller == null) {
            return List.of();
        }
        Map<Integer, List<DispatchResolution.ResolvedTarget>> byBci = resolvedCache.computeIfAbsent(caller, k -> new java.util.concurrent.ConcurrentHashMap<>());
        List<DispatchResolution.ResolvedTarget> cached = byBci.get(call.bci);
        if (cached != null) {
            return cached;
        }
        List<DispatchResolution.ResolvedTarget> result = computeTargets(caller, call);
        byBci.put(call.bci, result);
        return result;
    }

    /**
     * The invoke flow of a call vertex, by the one call-site identity rule. An IR invoke left
     * by an inlined scope ({@link StringAnalysisChildInlining#isFromInlinedScope}) is keyed by its root call's bci, which
     * it may share with other invokes: its flow is {@link SugBuilderV2#invokeFlowAt}'s (the key's only flow, and only
     * when its target is the invoke's own), never simply the first flow of the key, which can belong to another invoke
     * (a special invoke of another target would bind a virtual callee to its declared method, a foreign receiver type
     * would give a wrong cone). No flow means: the cone of the callee's declaring class (the widest sound cone), no
     * invokespecial shortcut and no arg-position stamp cap. Every other vertex is looked up by its bci.
     */
    static <F> F callFlowAt(Map<Integer, F> byBci, Set<Integer> ambiguous, LocalFlowGraph.LocalVertex call, Function<F, ?> targetOf) {
        if (byBci == null) {
            return null;
        }
        if (call.irNode instanceof Invoke inv && StringAnalysisChildInlining.isFromInlinedScope(inv)) {
            return SugBuilderV2.invokeFlowAt(byBci, ambiguous, inv, targetOf);
        }
        return byBci.get(call.bci);
    }

    private InvokeTypeFlow callFlowOf(AnalysisMethod caller, LocalFlowGraph.LocalVertex call) {
        Map<Integer, InvokeTypeFlow> byBci = caller != null ? invokes.get(caller) : null;
        Set<Integer> ambiguous = caller != null && lfgWalk != null && lfgWalk.builder() != null ? lfgWalk.builder().methodBciInvokeAmbiguous.get(caller) : null;
        return callFlowAt(byBci, ambiguous, call, InvokeTypeFlow::getTargetMethod);
    }

    private List<DispatchResolution.ResolvedTarget> computeTargets(AnalysisMethod caller, LocalFlowGraph.LocalVertex call) {
        AnalysisMethod calleeMethod = call.calleeMethod;
        InvokeTypeFlow invoke = callFlowOf(caller, call);
        List<AnalysisMethod> cha = DispatchResolution.computeDeterministicChaTargets(calleeMethod, invoke);
        Collection<AnalysisMethod> targetMethods;
        if (cha.isEmpty()) {
            Set<AnalysisMethod> impls = null;
            try {
                impls = calleeMethod != null ? calleeMethod.collectMethodImplementations(false) : null;
            } catch (Throwable t) {
                impls = null;
            }
            if (impls == null || impls.isEmpty()) {
                return List.of();
            }
            targetMethods = impls;
        } else {
            targetMethods = cha;
        }
        // No fan cap here: filter before cap. The carried block's receiver-position filter (handleInvokeRecord) runs
        // first; the cap trips only on the surviving residue.
        List<DispatchResolution.ResolvedTarget> targets = new ArrayList<>(targetMethods.size());
        for (AnalysisMethod m : sortMethods(targetMethods)) {
            LocalFlowGraph lfg = localFlows.get(m);
            String declaring = m.getDeclaringClass() != null ? m.getDeclaringClass().toJavaName(true) : "";
            targets.add(new DispatchResolution.ResolvedTarget(m, lfg, null, m.isStatic(), declaring));
        }
        return targets;
    }

    private static List<AnalysisMethod> sortMethods(Collection<AnalysisMethod> methods) {
        List<AnalysisMethod> sorted = new ArrayList<>(methods);
        sorted.sort(Comparator.comparing((AnalysisMethod m) -> m.format("%H.%n"))
                        .thenComparing(m -> m.getSignature().toMethodDescriptor()));
        return sorted;
    }

    /**
     * The analysis thread count ({@code -J-Dsvm.stringanalysis.fwd.threads=N}). Default: the build's worker count,
     * {@link NativeImageOptions#getActualNumberOfThreads()} (the forked child receives the parent's settings). N&gt;1
     * drains container rounds in parallel ({@code fwd.rtrack.parcontainer}); results are schedule-independent. Read in
     * {@link #solve()}, because the hosted option exists only inside an image build.
     */
    private static int configuredThreads() {
        Integer explicit = Integer.getInteger("svm.stringanalysis.fwd.threads");
        return explicit != null ? explicit : NativeImageOptions.getActualNumberOfThreads();
    }

    private int fwdThreads;

    // ------------------------------------------------------------------
    // The one fixpoint.
    // ------------------------------------------------------------------

    void solve() {
        long t0 = System.nanoTime();
        // Coarse phase timers (always on).
        long p5IndexNs;
        long p5SeedNs;
        long p5DrainNs;
        long p5AuditNs;
        long p5Span = System.nanoTime();
        index();
        ContainerAtoms.setDriver(Thread.currentThread()); // the tripwire's driver fast path
        this.rtrack = new RecursiveTracking(new RTrackBridge(),
                        lfgWalk != null ? lfgWalk.builder().argStampResolution : null);
        rtrack.strackSites(new StrackSites()); // the string rows' usage-site adapter
        p5IndexNs = System.nanoTime() - p5Span;
        fwdThreads = configuredThreads();
        boolean parallelMode = fwdThreads > 1;
        if (parallelMode) {
            parT0 = t0;
            parStart();
            // The container queue drains in parallel rounds on the same executor (fwd.rtrack.parcontainer).
            rtrack.useParallel(parPool, parThreads);
        }
        p5Span = System.nanoTime();
        seedStringAtoms(); // one STRING atom per creation site of an activated heuristic
        seedAccumulatorAtoms(activatedHeuristics()); // the accumulator heuristic's pass-1 seeds
        p5SeedNs = System.nanoTime() - p5Span;
        // Watchdog: if a single evaluation runs long, dump the engine stack to stderr once per minute.
        Thread watch = new Thread(() -> {
            long last = System.nanoTime();
            while (true) {
                try {
                    Thread.sleep(1000);
                } catch (InterruptedException e) {
                    return;
                }
                if (System.nanoTime() - last > 60_000_000_000L) {
                    last = System.nanoTime();
                    for (Map.Entry<Thread, StackTraceElement[]> e : Thread.getAllStackTraces().entrySet()) {
                        boolean inEngine = false;
                        for (StackTraceElement f : e.getValue()) {
                            if (f.getClassName().endsWith("ForwardFixpoint")) {
                                inEngine = true;
                                break;
                            }
                        }
                        if (!inEngine) {
                            continue;
                        }
                        StringBuilder sb = new StringBuilder("[sug-fwd-watch] thread=" + e.getKey().getName() + ":");
                        for (int i = 0; i < Math.min(14, e.getValue().length); i++) {
                            sb.append("\n[sug-fwd-watch]     at ").append(e.getValue()[i]);
                        }
                        System.err.println(sb);
                    }
                }
            }
        }, "sug-fwd-watchdog");
        watch.setDaemon(true);
        watch.start();
        p5Span = System.nanoTime();
        // The container queue is the only work queue (every string is a STRING atom of the container engine).
        // Quiescence = the container queue empty; the owner decisions of the round are taken only there
        // (roundBoundary; true = they minted something, another round). Two forms: the parallel and the serial loop.
        drainSettled(parallelMode);
        if (accPass2(parallelMode)) {
            drainSettled(parallelMode); // the accumulator heuristic's pass 2 (the extraction atoms) on the same engine state
            accRecheckReceivers(); // the receiver verdicts re-taken on the final facts
        }
        p5DrainNs = System.nanoTime() - p5Span;
        String guardWarning = rtrack.guardHeadroomWarning(); // print-only
        if (guardWarning != null) {
            System.err.println(guardWarning);
        }
        // EVALUATION_GUARD: a global refusal (strackAggregates: every string atom takes it), never a silent cut. The
        // "audit" span stays in the timer line (always 0).
        p5AuditNs = 0L;
        System.err.println("[sug-fwd-time] index=" + (p5IndexNs / 1_000_000) + "ms seed=" + (p5SeedNs / 1_000_000) +
                        "ms drain=" + (p5DrainNs / 1_000_000) + "ms audit=" + (p5AuditNs / 1_000_000) +
                        "ms (sum " + ((p5IndexNs + p5SeedNs + p5DrainNs + p5AuditNs) / 1_000_000) + "ms)");
        // The lock-discipline tripwire (ContainerAtoms.lockOrderSummary): a thread holds at most one Table/Sink monitor;
        // a nonzero violation count means a cross-monitor nesting, i.e. a constructible deadlock.
        System.err.println("[sug-fwd-phase] drainMs=" + (p5DrainNs / 1_000_000) +
                        " containerMs=" + (rtrack.drainNs / 1_000_000) + " containerDrains=" + rtrack.drainCalls +
                        " boundaryMs=" + (rtrack.boundaryNs / 1_000_000) + " boundaries=" + rtrack.boundaryCalls +
                        " boundaryReadMs=" + (rtrack.boundaryReadNs / 1_000_000) + " boundaryResolutions=" + rtrack.boundaryResolutions);
        System.err.println(ContainerAtoms.lockOrderSummary());
        // The census line (always printed; counters only).
        rtrack.objectReturn.objretRerunCheck(); // objret=1 and a tripped guard only
        rtrack.printStrackSeeds(); // the per-seed lines, before the census line
        System.err.println(rtrack.census());
        parShutdown();
        System.out.println("[sug-fwd] argStampSites=" + argStampSites.sum() +
                        ", argStampSkips=" + argStampSkips.sum() +
                        ", armSkipVacuous=" + armSkipVacuous.sum() +
                        ", armSkipNever=" + armSkipNever.sum() +
                        ", lfgSuccFail=" + LocalFlowGraph.SUCC_READ_FAILURES.sum() +
                        ", ms=" + ((System.nanoTime() - t0) / 1_000_000));
        // Stop the diagnostic watchdog (a daemon, but it would keep polling).
        watch.interrupt();
    }

    private AnalysisField rtrackResolveField(ResolvedJavaField rjf) {
        if (rjf instanceof AnalysisField af) {
            return af;
        }
        if (lfgWalk != null) {
            return lfgWalk.resolveAnalysisField(rjf);
        }
        return null;
    }

    /** The builder's decode is single-threaded code; parallel container rounds decode under this lock. */
    private final Object rtrackDecodeLock = new Object();

    /** The bridge from the engine to this fixpoint's owned pieces. */
    private final class RTrackBridge implements RecursiveTracking.Bridge {

        /**
         * The engine's dispatch resolution: the same computation and stamp filters as
         * {@link ForwardFixpoint#resolveCrossing}, but uncached (those caches are keyed by (caller, bci) and must not be
         * read or poisoned by the engine's call descriptors). The caller memoizes per descriptor.
         */
        @Override
        public List<DispatchResolution.ResolvedTarget> resolveCrossing(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call,
                        boolean receiverPosition, Block siteBlock) {
            if (ctx == null || call.calleeMethod == null) {
                return List.of();
            }
            List<DispatchResolution.ResolvedTarget> targets = computeTargets(ctx, call);
            if (targets.size() <= 1) {
                return targets;
            }
            if (receiverPosition && siteBlock != null && !siteBlock.isTop()) {
                List<DispatchResolution.ResolvedTarget> filtered = new ArrayList<>(targets.size());
                for (DispatchResolution.ResolvedTarget target : targets) {
                    AnalysisType declaring = target.method() != null ? target.method().getDeclaringClass() : null;
                    if (declaring == null || blockIntersects(siteBlock, declaring)) {
                        filtered.add(target);
                    }
                }
                targets = filtered;
            }
            if (!receiverPosition) {
                targets = filterTargetsByArgStamp(ctx, call, targets);
            }
            return targets;
        }

        @Override
        public List<DispatchResolution.ResolvedTarget> committedFan(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call) {
            return ctx == null || call.calleeMethod == null ? List.of() : resolveTargets(ctx, call); // the index's memo
        }

        @Override
        public AnalysisMethod methodOf(LocalFlowGraph frame) {
            return frameMethod.get(frame);
        }

        @Override
        public List<CallerSite> callersOf(LocalFlowGraph frame) {
            return callersOf.get(frame);
        }

        @Override
        public boolean isWorldTop(LocalFlowGraph frame) {
            // A world-top entry: a native entry point or a root method (main has no analysed caller).
            AnalysisMethod m = frameMethod.get(frame);
            try {
                return m != null && (m.isNativeEntryPoint() || m.isDirectRootMethod());
            } catch (Throwable t) {
                return false;
            }
        }

        @Override
        public StructuredGraph decodeIrGraph(AnalysisMethod method) {
            // The builder's decode is single-threaded code: parallel container rounds decode under one lock.
            synchronized (rtrackDecodeLock) {
                return lfgWalk != null ? lfgWalk.builder().decodeIrGraph(method) : null;
            }
        }

        @Override
        public AnalysisField resolveField(ResolvedJavaField field) {
            return rtrackResolveField(field);
        }

        @Override
        public AnalysisMethod resolveMethod(ResolvedJavaMethod method) {
            if (method instanceof AnalysisMethod am) {
                return am;
            }
            try {
                return lfgWalk != null ? lfgWalk.builder().bb.getUniverse().getMethod(method) : null;
            } catch (Throwable t) {
                return null;
            }
        }

        @Override
        public Block siteBlockOf(LocalFlowGraph frame, LocalFlowGraph.LocalVertex site) {
            return ForwardFixpoint.this.siteBlockOf(frame, site);
        }

        /** The caller's points-to invoke flows, by method (lazily, once per method; the final flow graph). */
        private final Map<AnalysisMethod, List<InvokeTypeFlow>> pointsToInvokes = new java.util.concurrent.ConcurrentHashMap<>();

        /** The unique points-to invoke flow of one LFG call (null after telling {@code why}). */
        private InvokeTypeFlow matchedInvokeFlow(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, java.util.function.Consumer<String> why) {
            AnalysisMethod callee = call.calleeMethod;
            if (ctx == null || callee == null || lfgWalk == null || lfgWalk.builder() == null || lfgWalk.builder().bb == null) {
                why.accept("noCtx");
                return null;
            }
            if (callee.isStatic() || callee.canBeStaticallyBound()) {
                why.accept("direct");
                return null;
            }
            List<InvokeTypeFlow> all = pointsToInvokes.computeIfAbsent(ctx, m -> {
                if (m instanceof com.oracle.graal.pointsto.meta.PointsToAnalysisMethod ptm && ptm.getTypeFlow() != null && ptm.getTypeFlow().flowsGraphCreated()) {
                    return new ArrayList<>(ptm.getTypeFlow().getInvokes());
                }
                return List.of();
            });
            // the unique invoke flow of this call: same method, same source bci, same declared target
            return uniqueInvokeFlow(all, f -> f.getSource() instanceof BytecodePosition pos ? pos : null, InvokeTypeFlow::getTargetMethod,
                            invokeOwnMethod(call.irNode, ctx), call.bci, callee, why);
        }

        @Override
        public java.util.Collection<AnalysisMethod> pointsToCallees(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call) {
            InvokeTypeFlow match = matchedInvokeFlow(ctx, call, r -> {
            });
            return match == null ? null : match.getOriginalCallees(); // the self-check's oracle
        }

        @Override
        public List<AnalysisType> pointsToReceiverTypes(AnalysisMethod ctx, LocalFlowGraph.LocalVertex call, java.util.function.Consumer<String> why) {
            InvokeTypeFlow match = matchedInvokeFlow(ctx, call, why);
            if (match == null) {
                return null;
            }
            if (!(match instanceof com.oracle.graal.pointsto.flow.AbstractVirtualInvokeTypeFlow) || match.isSaturated()) {
                why.accept(match.isSaturated() ? "invokeSaturated" : "notVirtual");
                return null;
            }
            TypeFlow<?> recv = match.getReceiver();
            if (recv == null || !recv.isFlowEnabled() || recv.isSaturated() || recv.isAllInstantiated()) {
                why.accept(recv == null ? "noReceiver" : !recv.isFlowEnabled() ? "receiverDisabled" : recv.isSaturated() ? "receiverSaturated" : "receiverAllInstantiated");
                return null;
            }
            com.oracle.graal.pointsto.typestate.TypeState state = recv.getState();
            if (state == null || state.typesCount() == 0) {
                why.accept("emptyState");
                return null;
            }
            List<AnalysisType> types = new ArrayList<>(state.typesCount());
            for (AnalysisType r : state.types(lfgWalk.builder().bb)) {
                types.add(r);
            }
            return types;
        }

        @Override
        public Block widenedBlockOf(AnalysisType exactType) {
            // The declared-type widening of a birth type (pure in the type: widenType's own memo)
            return exactType == null ? null : Block.of(new LinkedHashSet<>(widenType(exactType)));
        }

        @Override
        public LocalFlowGraph frameOf(AnalysisMethod method) {
            return localFlows.get(method);
        }

        @Override
        public long frameCount() {
            return localFlows.size();
        }

        @Override
        public Map<AnalysisType, Set<com.oracle.graal.pointsto.heap.ImageHeapConstant>> heapObjects() {
            try {
                Object scanner = lfgWalk != null ? lfgWalk.builder().bb.getUniverse().getHeapScanner() : null;
                if (scanner instanceof com.oracle.svm.hosted.heap.SVMImageHeapScanner svm && svm.getImageHeap() != null) {
                    return svm.getImageHeap().getReachableObjects();
                }
            } catch (Throwable t) {
                // unavailable: the caller refuses by name (CONSTANT_HOLDERS_UNINDEXED)
            }
            return null;
        }

        @Override
        public boolean classInitSimulated(AnalysisType type) {
            try {
                return com.oracle.svm.hosted.classinitialization.SimulateClassInitializerSupport.singleton().isClassInitializerSimulated(type);
            } catch (Throwable t) {
                return false; // unavailable: treated as run-time init (the unseen-writer check then applies)
            }
        }

        @Override
        public jdk.vm.ci.meta.JavaConstant simulatedStaticValue(AnalysisField f) {
            try {
                return com.oracle.svm.hosted.classinitialization.SimulateClassInitializerSupport.singleton().getSimulatedFieldValue(f);
            } catch (Throwable t) {
                return null;
            }
        }

        @Override
        public Iterable<AnalysisMethod> universeMethods() {
            List<AnalysisMethod> out = new ArrayList<>();
            try {
                if (lfgWalk != null) {
                    for (AnalysisMethod m : lfgWalk.builder().bb.getUniverse().getMethods()) {
                        out.add(m);
                    }
                }
            } catch (Throwable t) {
                // unavailable: the index stays LFG-only for these (counted as problems by the caller)
            }
            return out;
        }

        @Override
        public List<Object[]> invokeSites(AnalysisMethod m) {
            // The identity-tracking premise: the analysis's own invokes of m (unavailable throws: the premise fails closed)
            if (lfgWalk == null) {
                throw new IllegalStateException("invokeSites: no analysis");
            }
            if (!(m instanceof com.oracle.graal.pointsto.meta.PointsToAnalysisMethod ptm) || ptm.getTypeFlow() == null || !ptm.getTypeFlow().flowsGraphCreated()) {
                return null;
            }
            List<Object[]> out = new ArrayList<>();
            for (InvokeTypeFlow f : ptm.getTypeFlow().getInvokes()) {
                BytecodePosition pos = f.getSource() instanceof BytecodePosition bp ? bp : null;
                java.util.Collection<AnalysisMethod> callees; // the points-to callees (null = unavailable)
                try {
                    callees = f.getAllCallees();
                } catch (Throwable t) {
                    callees = null;
                }
                out.add(new Object[]{f.getTargetMethod(), pos != null ? pos.getMethod() : null, pos != null ? pos.getBCI() : -1, callees});
            }
            return out;
        }

        @Override
        public AnalysisType classConstantType(jdk.vm.ci.meta.JavaConstant c) {
            // The type a Class/hub constant stands for (AnalysisConstantReflectionProvider.asJavaType: no side effect).
            // Null only for "not a Class constant"; an unavailable lookup throws (the callers fail closed).
            if (lfgWalk == null) {
                throw new IllegalStateException("classConstantType: no analysis");
            }
            jdk.vm.ci.meta.ResolvedJavaType t = lfgWalk.builder().bb.getConstantReflectionProvider().asJavaType(c);
            return t instanceof AnalysisType at ? at : null;
        }

        @Override
        public AnalysisType optionalAnalysisType(jdk.vm.ci.meta.ResolvedJavaType t) {
            // null only for "not in the universe"; an unavailable lookup throws (the callers fail closed)
            if (lfgWalk == null) {
                throw new IllegalStateException("optionalAnalysisType: no analysis");
            }
            return lfgWalk.builder().bb.getUniverse().optionalLookup(t);
        }

        @Override
        public AnalysisType lookupJavaType(Class<?> c) {
            try {
                return lfgWalk != null ? lfgWalk.builder().bb.getMetaAccess().lookupJavaType(c) : null;
            } catch (Throwable t) {
                return null; // unavailable: the thread-local rules refuse by name
            }
        }

        @Override
        public AnalysisMethod resolveMethodSubstituted(ResolvedJavaMethod method) {
            // The universe's own key (substitutions applied, as universe.lookup), no creation
            if (method instanceof AnalysisMethod am) {
                return am;
            }
            try {
                com.oracle.graal.pointsto.meta.AnalysisUniverse u = lfgWalk != null ? lfgWalk.builder().bb.getUniverse() : null;
                if (u == null) {
                    return null;
                }
                AnalysisMethod m = u.getMethod(u.getSubstitutions().lookup(method));
                return m != null ? m : u.getMethod(method);
            } catch (Throwable t) {
                return null;
            }
        }

        @Override
        public List<AnalysisMethod> foreignCallTargets() {
            // Every registered foreign call's target (a superset of the analysed graphs' uses)
            try {
                var fc = lfgWalk.builder().bb.getProviders(com.oracle.svm.common.meta.MultiMethod.ORIGINAL_METHOD).getForeignCalls();
                List<AnalysisMethod> out = new ArrayList<>();
                for (var linkage : ((com.oracle.svm.core.graal.meta.SubstrateForeignCallsProvider) fc).getForeignCalls().values()) {
                    ResolvedJavaMethod lm = linkage.getMethod();
                    AnalysisMethod am = lm != null ? resolveMethodSubstituted(lm) : null;
                    if (am != null) {
                        out.add(am);
                    }
                }
                return out;
            } catch (Throwable t) {
                return null;
            }
        }

        @Override
        public Set<AnalysisType> argStampOfUnregistered(jdk.graal.compiler.nodes.Invoke inv) {
            ArgStampResolution asr = lfgWalk != null ? lfgWalk.builder().argStampResolution : null;
            return asr != null ? asr.stampOfUnregisteredInvoke(inv) : null;
        }

        @Override
        public Iterable<AnalysisField> universeFields() {
            List<AnalysisField> out = new ArrayList<>();
            if (lfgWalk != null) {
                for (AnalysisField f : lfgWalk.builder().bb.getUniverse().getFields()) {
                    out.add(f);
                }
            }
            return out; // a failure propagates: the caller counts it (the refusal direction)
        }

        @Override
        public Iterable<AnalysisField> staticFields() {
            List<AnalysisField> out = new ArrayList<>();
            try {
                if (lfgWalk != null) {
                    for (AnalysisField f : lfgWalk.builder().bb.getUniverse().getFields()) {
                        if (f.isStatic() && f.getJavaKind() == jdk.vm.ci.meta.JavaKind.Object) {
                            out.add(f);
                        }
                    }
                }
            } catch (Throwable t) {
                return null;
            }
            return out;
        }
    }

    // ------------------------------------------------------------------
    // Dispatch narrowing (read by DispatchResolution and RecursiveTracking) and the arg-stamp filter.
    // ------------------------------------------------------------------

    /**
     * The drop proof (exact dispatch): a receiver-position call whose carried block is not top, and every
     * block type t dispatches M to another method ({@code t.resolveConcreteMethod(M, t) != M}; a type whose
     * resolution is unknown keeps M). {@code blockTypes == null} = TOP. Package-private for the fixture pin.
     */
    static boolean overrideDropProven(boolean asReceiver, Collection<? extends jdk.vm.ci.meta.ResolvedJavaType> blockTypes,
                    jdk.vm.ci.meta.ResolvedJavaMethod dropped) {
        if (!asReceiver || blockTypes == null || blockTypes.isEmpty() || dropped == null) {
            return false;
        }
        for (jdk.vm.ci.meta.ResolvedJavaType t : blockTypes) {
            jdk.vm.ci.meta.ResolvedJavaMethod r;
            try {
                r = t.resolveConcreteMethod(dropped, t);
            } catch (Throwable e) {
                return false;
            }
            if (r == null || r.equals(dropped)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The arg-position receiver-stamp consult: narrow an arg-position invoke's CHA fan to the targets the dispatch
     * receiver's provable may-stamp can dispatch to.
     * <p>
     * {@code call.argStamp} ({@code ArgStampResolution}) is a set of cone roots R (runtime receiver type in the
     * instantiated subtypes of R), derived from the IR (allocation evidence, Pi-stamp narrowing, the field-writer union
     * with the unsafe/reflection gate): a sound may-set, or {@code null} (top: full fan). Every root is first capped by
     * the invoke's declared receiver cone (a root wider than the declared cone contributes the declared root; a
     * disjoint root is a provably dead pair and dropped), so the fan can only shrink. The fan is then the per-root
     * deterministic CHA. Guard rails, all conservative: no stamp, an empty effective root set, an empty or
     * non-shrinking recomputation, a fallback-search fan or any throwable keeps the full fan. Precision only: it never
     * mints incompleteness and only drops provably unreachable consult edges.
     * <p>
     * Soundness: a receiver outside the stamp's roots would mean the stamp was not a sound may-set, which the
     * ArgStampResolution contract excludes. The declared-cone cap is an independent second guard: every runtime
     * receiver satisfies the declared cone by type safety, so the kept targets are exactly those reachable from
     * declared-cone ∩ stamp-cone and only an unsound stamp could miss a target.
     */
    private List<DispatchResolution.ResolvedTarget> filterTargetsByArgStamp(AnalysisMethod ctx,
                    LocalFlowGraph.LocalVertex call, List<DispatchResolution.ResolvedTarget> targets) {
        Set<AnalysisType> stamp = call.argStamp;
        if (stamp == null || stamp.isEmpty() || targets.size() <= 1) {
            return targets;
        }
        try {
            AnalysisMethod callee = call.calleeMethod;
            if (callee == null || callee.isStatic() || callee.canBeStaticallyBound()) {
                return targets;
            }
            // The declared receiver cone, resolved exactly as computeTargets does (the call-site identity rule).
            InvokeTypeFlow invoke = callFlowOf(ctx, call);
            if (invoke == null) {
                return targets; // no invoke flow metadata — no declared cone to cap by
            }
            AnalysisType declared = invoke.getReceiverType();
            if (declared == null) {
                return targets;
            }
            // Only fans from the deterministic CHA path (an empty CHA means the implementation-search fallback).
            if (DispatchResolution.computeDeterministicChaTargets(callee, invoke).isEmpty()) {
                return targets;
            }
            // Cap every stamp root by the declared cone (the pair rule).
            Set<AnalysisType> effective = new LinkedHashSet<>(stamp.size());
            for (AnalysisType root : stamp) {
                if (root == null) {
                    continue;
                }
                if (declared.equals(root) || declared.isAssignableFrom(root)) {
                    effective.add(root); // root ⊆ declared — usable narrowing
                } else if (root.isAssignableFrom(declared)) {
                    effective.add(declared); // declared ⊆ root — no gain, keep the floor
                }
                // disjoint → provably dead pair — contributes nothing
            }
            if (effective.isEmpty()) {
                return targets;
            }
            Set<AnalysisMethod> merged = new LinkedHashSet<>(targets.size());
            for (AnalysisType root : effective) {
                merged.addAll(DispatchResolution.computeDeterministicChaTargets(callee, root));
                // An abstract root's own resolution is never a runtime target
                // by itself (the same rule as the CHA root's, DispatchResolution.rootContributesOwnResolution).
                if (!root.isInterface() && root.isAnySubtypeInstantiated() && DispatchResolution.rootContributesOwnResolution(root)) {
                    // The class root's own override resolution, added explicitly so that a leaf class root (no
                    // instantiated subtypes) never resolves to nothing. Sound: it is the dispatch target of every
                    // root-cone receiver that does not override it, and always a member of the original fan.
                    AnalysisMethod own = root.resolveConcreteMethod(callee);
                    if (own != null && !Modifier.isAbstract(own.getModifiers())) {
                        merged.add(own);
                    }
                }
            }
            if (merged.isEmpty() || merged.size() >= targets.size()) {
                return targets; // strict-shrink-only: no movement, no reordering churn
            }
            argStampSites.increment();
            argStampSkips.add(targets.size() - merged.size());
            List<DispatchResolution.ResolvedTarget> narrowed = new ArrayList<>(merged.size());
            for (AnalysisMethod m : sortMethods(merged)) {
                LocalFlowGraph lfg = localFlows.get(m);
                String declaring = m.getDeclaringClass() != null ? m.getDeclaringClass().toJavaName(true) : "";
                narrowed.add(new DispatchResolution.ResolvedTarget(m, lfg, null, m.isStatic(), declaring));
            }
            return narrowed;
        } catch (Throwable tv) {
            return targets; // precision-only: never throw, never mint
        }
    }

    /**
     * The block ∧ declared-type intersection, for the walk's cast guard (a provably out-of-cone cast is CCE-identical
     * for every value of the cone, so its continuation is dropped).
     */
    boolean blockIntersects(Block block, AnalysisType declaring) {
        if (block == null || declaring == null || block.isTop()) {
            return true; // unprovable ⇒ intersecting (the sound-push direction)
        }
        for (AnalysisType type : block.types) {
            if (declaring.equals(type) || declaring.isAssignableFrom(type) || type.isAssignableFrom(declaring)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The unique points-to invoke flow of one IR call, or null after telling {@code why}. A
     * flow matches when its source position has the call's method, its bci and its declared target. The method is the
     * IR invoke's own method ({@link #invokeOwnMethod}; null for an inlined-before-analysis invoke, which points-to
     * records at its outermost caller's position, so it never matches, nor does a same-bci flow of another method).
     * Any doubt keeps the committed fan: no match ({@code noInvokeFlow}), a (bci, target) match only in another method
     * ({@code invokeFlowMethodMismatch}), or several matches ({@code ambiguousInvokeFlow}). Pure; pinned by
     * {@code ReceiverDispatchTest}.
     */
    static <F> F uniqueInvokeFlow(List<F> flows, Function<F, ? extends BytecodePosition> source, Function<F, ? extends ResolvedJavaMethod> target, ResolvedJavaMethod method,
                    int bci, ResolvedJavaMethod callee, Consumer<String> why) {
        F match = null;
        int matches = 0;
        int otherMethod = 0;
        for (F f : flows) {
            BytecodePosition pos = source.apply(f);
            if (pos == null || pos.getBCI() != bci || !callee.equals(target.apply(f))) {
                continue;
            }
            if (method == null || !method.equals(pos.getMethod())) {
                otherMethod++;
                continue;
            }
            match = f;
            matches++;
        }
        if (matches != 1) {
            why.accept(matches > 1 ? "ambiguousInvokeFlow" : otherMethod > 0 ? "invokeFlowMethodMismatch" : "noInvokeFlow");
            return null;
        }
        return match;
    }

    /**
     * The method an IR invoke's own bytecode belongs to (from its source position, else its frame state): normally
     * {@code ctx}; null for an inlined-before-analysis invoke, whose points-to flow sits at the outermost caller's bci.
     * {@code ctx} for a non-invoke node or without either.
     */
    static ResolvedJavaMethod invokeOwnMethod(Object irNode, ResolvedJavaMethod ctx) {
        if (irNode instanceof Invoke inv) {
            NodeSourcePosition nsp = inv.asNode().getNodeSourcePosition();
            if (nsp != null) {
                return nsp.getCaller() == null ? nsp.getMethod() : null;
            }
            FrameState fs = inv.stateAfter() != null ? inv.stateAfter() : inv.stateDuring();
            if (fs != null && fs.getMethod() != null) {
                return fs.outerFrameState() == null ? fs.getMethod() : null;
            }
        }
        return ctx;
    }

    // ------------------------------------------------------------------
    // Value-relative arm feasibility: usages in arms provably unreachable with the traced value's type are not usages
    // of this value. Their mints are skipped, and the walk's continuation through a dead arm's PiNode stops too
    // (RecursiveTracking.piArmDead). Everything else (other uses, stores, loads, invoke consults, result channels) is
    // still explored. The proof is per carried block, never per method; a pure function of (guard kind, tested type,
    // carried block, closed-world types).
    // ------------------------------------------------------------------

    /**
     * The guard-kind feasibility table for one usage anchor: whether a usage in an arm is provably unreachable for a
     * value carrying {@code block}, given the anchor's vacuous guards (non-exact {@code instanceof T} whose dead arm
     * hosts every anchor) and never guards (any guard, exact included, whose covered arm hosts every anchor). Returns
     * 1 (dead: every block member is {@code T}-assignable for a vacuous guard, the test always succeeds), 2 (dead: no
     * member is {@code T}-assignable for a never guard, the test always fails) or 0 (keep). A top or null block and
     * missing lists prove nothing. Two-sided because finite blocks are widened ({@code widenType}: declared type +
     * every instantiated subtype), so every member decides the guard as the table says; an exact test is never in the
     * vacuous list (an assignable member can still fail it). In the analysis child a STRING block's widened cone is
     * {String}: no rep is instantiated there ({@code RepTypeChecks.recordChildRepTypes}). A String that becomes a rep in
     * the parent still decides every child-IR guard as String does, because (i) the reps add no supertype beyond
     * String's ({@code class X extends String}, no {@code implements}), and (ii) no rep-typed test exists in the
     * child's IR (no rep type is reachable there, and the rep plugins register only outside the fork). Read by
     * {@code StrackSites.armDead}; pinned by {@code ArmFeasibilityTest}.
     */
    static int armDeadDirection(List<LocalFlowGraph.TypeGuard> vacuous, List<LocalFlowGraph.TypeGuard> never, Block block) {
        if (block == null || block.isTop()) {
            return 0;
        }
        if (vacuous != null) {
            for (LocalFlowGraph.TypeGuard guard : vacuous) {
                if (guard.targetType != null && allMembersAssignable(block, guard.targetType)) {
                    return 1;
                }
            }
        }
        if (never != null) {
            for (LocalFlowGraph.TypeGuard guard : never) {
                if (guard.targetType != null && noMemberAssignable(block, guard.targetType)) {
                    return 2;
                }
            }
        }
        return 0;
    }

    /**
     * The feasibility table for one (frame, anchor, observed value, block): the value's type guards (after Pi/proxy
     * skipping: the same value), their vacuous/never lists for the anchor ({@code LfgWalk.guardListsFor}, memoised per
     * (frame, anchor, value)), then {@link #armDeadDirection}. Shared by {@code StrackSites.armDead} and
     * {@code RecursiveTracking.piArmDead}.
     */
    @SuppressWarnings("unchecked")
    static int armFeasibility(LocalFlowGraph frame, jdk.graal.compiler.graph.Node anchor, jdk.graal.compiler.nodes.ValueNode observed, Block block,
                    Map<List<Object>, List<LocalFlowGraph.TypeGuard>[]> memo) {
        if (frame == null || anchor == null || observed == null || block == null || block.isTop() || !(frame.irGraph instanceof StructuredGraph ir) || ir.start() == null) {
            return 0;
        }
        jdk.graal.compiler.nodes.ValueNode obs = observed;
        while (true) {
            if (obs instanceof jdk.graal.compiler.nodes.PiNode pi) {
                obs = pi.getOriginalNode();
            } else if (obs instanceof jdk.graal.compiler.nodes.spi.ValueProxy proxy) {
                obs = proxy.getOriginalNode();
            } else {
                break;
            }
        }
        List<LocalFlowGraph.TypeGuard> guards = frame.guardsForValue(obs);
        if (guards.isEmpty()) {
            return 0;
        }
        List<LocalFlowGraph.TypeGuard>[] lists = memo.computeIfAbsent(List.of(frame, anchor, obs), k -> {
            List<LocalFlowGraph.TypeGuard> vac = new ArrayList<>(2);
            List<LocalFlowGraph.TypeGuard> nev = new ArrayList<>(2);
            LfgWalk.guardListsFor(ir.start(), LocalFlowGraph.fixedAnchorsOfRoot(anchor), guards, vac, nev);
            return new List[]{vac, nev};
        });
        return armDeadDirection(lists[0], lists[1], block);
    }

    /** Every block member is {@code T}-assignable (the always-succeeds side). */
    private static boolean allMembersAssignable(Block block, AnalysisType target) {
        for (AnalysisType type : block.types) {
            if (!target.isAssignableFrom(type)) {
                return false;
            }
        }
        return true;
    }

    /** No block member is {@code T}-assignable (the always-fails side). */
    private static boolean noMemberAssignable(Block block, AnalysisType target) {
        for (AnalysisType type : block.types) {
            if (target.isAssignableFrom(type)) {
                return false;
            }
        }
        return true;
    }

    // ------------------------------------------------------------------
    // The executor (threads>1): runs the container engine's parallel rounds only.
    // ------------------------------------------------------------------

    private java.util.concurrent.ExecutorService parPool;
    private int parThreads;
    private long parT0;

    /** The round executor's worker stack reservation (bytes; virtual, committed only as used). */
    private static final long WORKER_STACK = Long.getLong("svm.stringanalysis.fwd.workerstack", 512L << 20);

    private void parStart() {
        parThreads = Math.max(1, fwdThreads);
        if (parThreads > 1) {
            final java.util.concurrent.atomic.AtomicInteger workerSeq = new java.util.concurrent.atomic.AtomicInteger();
            parPool = java.util.concurrent.Executors.newFixedThreadPool(parThreads - 1, r -> {
                // MonThread holds the tripwire's per-thread state; workers run deep delivery cascades inline, hence
                // a generous reserved stack.
                Thread t = new ContainerAtoms.MonThread(r, "sug-fwd-worker-" + workerSeq.getAndIncrement(), WORKER_STACK);
                t.setDaemon(true);
                return t;
            });
        }
    }

    private void parShutdown() {
        if (parPool != null) {
            parPool.shutdownNow();
            parPool = null;
        }
        // Only when the executor was started.
        if (parThreads > 0) {
            System.err.println("[sug-fwd-par] threads=" + parThreads + " ms=" + ((System.nanoTime() - parT0) / 1_000_000));
        }
    }

    // ------------------------------------------------------------------
    // Emission.
    // ------------------------------------------------------------------

    /** The canonical budget-refusal token (the REJECT line reports the refusal, not its schedule-dependent names). */
    static final String D2_ALL_TOKEN = "RTRACK-REFUSED";

    // ------------------------------------------------------------------
    // The string atoms' seeds, their usage-site adapter, and the emit adapter (see StringAtoms).
    // ------------------------------------------------------------------
    /** The activated heuristics (the option filter, {@code StringAnalysisFeature}); all three when unavailable. */
    private static java.util.Set<String> activatedHeuristics() {
        java.util.Set<String> on = new java.util.LinkedHashSet<>(List.of("SV", "LC", "SB"));
        try {
            if (com.oracle.svm.core.SubstrateOptions.StringAnalysisStringViewOnly.getValue()) {
                on.retainAll(List.of("SV"));
            } else if (com.oracle.svm.core.SubstrateOptions.StringAnalysisLazyConcatOnly.getValue()) {
                on.retainAll(List.of("LC"));
            }
            if (com.oracle.svm.core.SubstrateOptions.StringAnalysisSingleByteOnly.getValue()) {
                on.retainAll(List.of("SB")); // the profile keeps SINGLE_BYTE only: that is the one applied heuristic
            }
        } catch (Throwable t) {
            // outside an image build (fixtures): every heuristic
        }
        return on;
    }

    /** The seed kind of an element-source call (ElementSources). */
    static final String ELEM_KIND = "ELEM";

    /** The seed's bci: its invoke flow's position, else the {@code …@bci} of its source location; -1 = unknown. */
    private static int seedBci(SugVertex v) {
        if (v.getSourceFlow() instanceof InvokeTypeFlow inv && inv.getSource() instanceof jdk.vm.ci.code.BytecodePosition pos) {
            return pos.getBCI();
        }
        String loc = v.getSourceLocation();
        int at = loc != null ? loc.lastIndexOf('@') : -1;
        if (at >= 0) {
            try {
                return Integer.parseInt(loc.substring(at + 1));
            } catch (NumberFormatException e) {
                return -1;
            }
        }
        return -1;
    }

    /**
     * One STRING atom per user-code creation site of an activated heuristic: String View (substring / subSequence; an
     * element-source call as an ELEM seed), Lazy Concat (every user-code makeConcat-family concat, a superset of the
     * parent's rewrite set; a join source call), Single Byte (length-1 substring, {@code valueOf(char)}; a
     * length-1 literal). Accumulator seeds come from {@link #seedAccumulatorAtoms}. The walk
     * starts at the creation invoke(s) in the site's frame.
     */
    private void seedStringAtoms() {
        java.util.Set<String> on = activatedHeuristics();
        Map<SugVertex, String> kinds = new LinkedHashMap<>();
        for (SugVertex v : sug.getVertices()) {
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            StringBuilder k = new StringBuilder();
            boolean substringLike = v.getNodeType() == SugNodeType.STRING_METHOD_CALL &&
                            ("substring".equals(v.getMethodName()) || "subSequence".equals(v.getMethodName()));
            if (on.contains("SV") && substringLike) {
                k.append("SV");
            }
            // A join source call (LazyConcatMint's source table) is a lazy-concat seed like a concat
            if (on.contains("LC") && (v.getNodeType() == SugNodeType.CONCAT_EXPRESSION || LazyConcatMint.isJoinSource(v))) {
                k.append(k.length() > 0 ? "+" : "").append("LC");
            }
            if (on.contains("SB") && isSbCreationSeed(v)) {
                k.append(k.length() > 0 ? "+" : "").append("SB");
            }
            // An element-source call is an ELEM seed: its atom is the element of the fresh stream/array the call returns
            // (RecursiveTracking.mintElementString)
            if (on.contains("SV") && k.length() == 0 && ElementSources.isSource(v)) {
                k.append(ELEM_KIND);
                sug.elemSources().add(v);
            }
            if (on.contains("SB") && StringAtoms.isSeedableLiteral(v)) {
                k.append(k.length() > 0 ? "+" : "").append("SB"); // an SB literal seed
            }
            if (k.length() > 0) {
                kinds.put(v, k.toString());
            }
        }
        List<Map.Entry<SugVertex, String>> sorted = new ArrayList<>(kinds.entrySet());
        sorted.sort(Comparator.comparing((Map.Entry<SugVertex, String> e) -> String.valueOf(e.getKey().getSourceLocation())).thenComparingInt(e -> e.getKey().getId()));
        int unwalkable = 0;
        for (Map.Entry<SugVertex, String> e : sorted) {
            SugVertex v = e.getKey();
            AnalysisMethod m = v.getEnclosingMethod();
            LocalFlowGraph frame = m != null ? localFlows.get(m) : null;
            StructuredGraph g = frame != null ? rtrack.graphOf(frame) : null;
            int bci = seedBci(v);
            List<jdk.graal.compiler.nodes.ValueNode> births = new ArrayList<>(1);
            if (g != null && bci >= 0 && v.getNodeType() == SugNodeType.STRING_LITERAL) {
                // The literal's birth is its ConstantNode; a method's ldcs of one text share that node
                for (jdk.graal.compiler.graph.Node n : g.getNodes()) {
                    if (n instanceof jdk.graal.compiler.nodes.ConstantNode cn && cn.getNodeSourcePosition() != null && cn.getNodeSourcePosition().getBCI() == bci &&
                                    v.getLiteralText().equals(literalText(cn))) {
                        births.add(cn);
                    }
                }
            } else if (g != null && bci >= 0) {
                String want = v.getNodeType() == SugNodeType.CONCAT_EXPRESSION ? ("concat".equals(v.getMethodName()) ? "concat" : null) : v.getMethodName();
                // An inlined-scope invoke is a birth only if the call-site identity rule gives it a flow
                Map<Integer, InvokeTypeFlow> seedByBci = m != null ? invokes.get(m) : null;
                Set<Integer> seedAmbiguous = m != null && lfgWalk != null && lfgWalk.builder() != null ? lfgWalk.builder().methodBciInvokeAmbiguous.get(m) : null;
                for (jdk.graal.compiler.graph.Node n : g.getNodes()) {
                    if (n instanceof jdk.graal.compiler.nodes.Invoke inv && StringAnalysisChildInlining.pointsToBci(inv) == bci && n instanceof jdk.graal.compiler.nodes.ValueNode vn &&
                                    inv.callTarget() != null && inv.callTarget().targetMethod() != null &&
                                    (want == null || want.equals(inv.callTarget().targetMethod().getName())) &&
                                    (!StringAnalysisChildInlining.isFromInlinedScope(inv) ||
                                                    SugBuilderV2.invokeFlowAt(seedByBci, seedAmbiguous, inv, InvokeTypeFlow::getTargetMethod) != null)) {
                        births.add(vn);
                    }
                }
            }
            ContainerTables.RTrackRefusal why = births.isEmpty() ? ContainerTables.RTrackRefusal.MISSING_IR : null;
            if (why != null) {
                unwalkable++;
            }
            StringAtoms.StringSeed seed = new StringAtoms.StringSeed(v, e.getValue(), frame, births, why);
            if (ELEM_KIND.equals(e.getValue())) {
                rtrack.mintElementString(seed, ElementSources.kindOf(v.getDeclaringClass(), v.getMethodName(), v.getMethodSignature()));
            } else {
                rtrack.mintString(seed);
            }
            System.out.println("[sug-strack-seed] " + e.getValue() + " " + v.getSourceLocation() + " births=" + births.size() + (why != null ? " unwalkable=" + why : ""));
        }
        System.out.println("[sug-strack-seeds] activated=" + on + " seeds=" + sorted.size() + " unwalkable=" + unwalkable);
    }

    /**
     * Drain to quiescence, then apply the holder-end rule ({@link HolderEndRule#holderEndRule}); a rule
     * refusal may fire waiters (e.g. a closed-field fallback), so drain again until the rule refuses nothing new (each
     * round refuses at least one more atom: terminates).
     */
    private void drainSettled(boolean parallelMode) {
        drainToQuiescence(parallelMode);
        while (rtrack.holderEnd.holderEndRule()) {
            drainToQuiescence(parallelMode);
        }
    }

    /** The drain loop: the parallel rounds or the serial loop, to quiescence. */
    private void drainToQuiescence(boolean parallelMode) {
        if (parallelMode) {
            rtrack.drain();
            while (rtrack.roundBoundary()) {
                rtrack.drain();
            }
        } else {
            do {
                rtrack.drain();
            } while (rtrack.hasWork() || rtrack.roundBoundary());
        }
    }

    // ------------------------------------------------------------------
    // The accumulator heuristic's two passes.
    // ------------------------------------------------------------------
    /** The pass-1 seeds (ACC), in seed order. */
    private final List<StringAtoms.StringSeed> accSeeds = new ArrayList<>();
    /** The seeded pass-2 sites (with their sinks) and the pass-1 birth map, kept for the final re-check. */
    private final List<AccSite> accSeededSites = new ArrayList<>();
    private Map<jdk.graal.compiler.graph.Node, SugVertex> accAdmittedBirths = Map.of();
    private Set<jdk.graal.compiler.graph.Node> accAllBirths = Set.of();

    /**
     * Pass 1's seeds: one STRING atom of kind "ACC" per user-code builder allocation (a NEW_ACCUMULATOR vertex), born
     * at the allocation node, with the builder class as its block (so the receiver filter keeps the builder's own
     * methods). Activated with String View; in LC-only mode only the StringJoiner accumulators are seeded (their
     * extraction is a LAZY_CONCAT INTERLEAVED).
     */
    private void seedAccumulatorAtoms(java.util.Set<String> on) {
        // LC-only seeds the StringJoiner accumulators alone (their extraction's rep is a lazy-concat rep)
        boolean lcOnlyJoiner = on.contains("LC") && !on.contains("SV");
        if (!on.contains("SV") && !lcOnlyJoiner) {
            return;
        }
        // A joiner extraction's rep is minted only in ALL and LC-only mode (AccumulatorHeuristic.joinerAllowed)
        boolean joinerSeeds = on.containsAll(List.of("SV", "LC", "SB")) || lcOnlyJoiner;
        List<SugVertex> cands = new ArrayList<>();
        for (SugVertex v : sug.getVertices()) {
            if (v.getNodeType() != SugNodeType.NEW_ACCUMULATOR || v.getJavaType() == null) {
                continue;
            }
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc) || !StringAtoms.ACC_SEED_TYPES.contains(v.getJavaType().toJavaName(true))) {
                continue;
            }
            boolean joiner = AccumulatorWhitelist.JOINER.equals(v.getJavaType().toJavaName(true));
            if ((!joinerSeeds && joiner) || (lcOnlyJoiner && !joiner)) {
                continue;
            }
            cands.add(v);
        }
        cands.sort(Comparator.comparing((SugVertex v) -> String.valueOf(v.getSourceLocation())).thenComparingInt(SugVertex::getId));
        int unwalkable = 0;
        for (SugVertex v : cands) {
            AnalysisMethod m = v.getEnclosingMethod();
            LocalFlowGraph frame = m != null ? localFlows.get(m) : null;
            StructuredGraph g = frame != null ? rtrack.graphOf(frame) : null;
            int bci = seedBci(v);
            String tn = v.getJavaType().toJavaName(true);
            List<jdk.graal.compiler.nodes.ValueNode> births = new ArrayList<>(1);
            if (g != null && bci >= 0) {
                for (jdk.graal.compiler.graph.Node n : g.getNodes()) {
                    jdk.vm.ci.meta.ResolvedJavaType it = StringAtoms.allocatedType(n);
                    jdk.graal.compiler.graph.NodeSourcePosition ap = it != null ? StringAtoms.allocationPosition(n) : null;
                    if (it != null && ap != null && ap.getBCI() == bci && tn.equals(it.toJavaName(true))) {
                        births.add((jdk.graal.compiler.nodes.ValueNode) n);
                    }
                }
            }
            ContainerTables.RTrackRefusal why = births.isEmpty() ? ContainerTables.RTrackRefusal.MISSING_IR : null;
            if (why != null) {
                unwalkable++;
            }
            Block block = Block.of(new LinkedHashSet<>(widenType(v.getJavaType())));
            StringAtoms.StringSeed seed = new StringAtoms.StringSeed(v, "ACC", frame, births, why, block);
            accSeeds.add(seed);
            rtrack.mintString(seed);
            System.out.println("[sug-strack-seed] ACC " + v.getSourceLocation() + " births=" + births.size() + (why != null ? " unwalkable=" + why : ""));
        }
        System.out.println("[sug-acc-seeds] seeds=" + cands.size() + " unwalkable=" + unwalkable);
    }

    /**
     * Pass 1's decision and pass 2's seeds (after the first quiescence). An accumulator passes pass 1 iff its atom has
     * no refusal and every usage is GROWING or READ ({@link AccumulatorWhitelist#accumulatorUsageRow}; the heuristic
     * re-derives the same verdict from the emitted facts). Its user-code {@code toString()} extraction sites are seeded
     * as kind "ACCX" iff the extraction's receiver provably comes only from pass-1 accumulators' allocations. The
     * receiver proof: a backward receiver resolution with the engine's sink
     * ({@link RecursiveTracking#attachOperandSink}, root task {@link RecursiveTracking#backward}) at every candidate site,
     * drained to quiescence before the verdict (the within-method proof {@link #localBuilderOrigins} is computed and
     * printed, {@code [sug-acc-recv]}, but is not a proof); the site qualifies iff the sink has no refusal and every
     * atom it holds is born at a pass-1 accumulator's allocation node (mapped by birth node, not by atom key). Returns
     * true when a seed was minted.
     */
    private boolean accPass2(boolean parallelMode) {
        if (accSeeds.isEmpty()) {
            return false;
        }
        Map<jdk.graal.compiler.graph.Node, SugVertex> admittedBirths = new HashMap<>();
        Set<jdk.graal.compiler.graph.Node> allBirths = new HashSet<>();
        Map<SugVertex, Set<SugVertex>> extractionOwners = new LinkedHashMap<>();
        int pass1 = 0;
        for (StringAtoms.StringSeed seed : accSeeds) {
            allBirths.addAll(seed.births);
            RecursiveTracking.RAtom a = rtrack.stringAtoms.get(seed);
            if (a == null || seed.unwalkable != null || !a.table.refusalsSnapshot().isEmpty() || rtrack.guardTripped()) {
                continue;
            }
            boolean ok = true;
            List<SugVertex> ext = new ArrayList<>();
            for (UsageFact f : a.strUsages) {
                SugVertex site = f.usageSite();
                AccumulatorWhitelist.AccRow row = site == null ? AccumulatorWhitelist.AccRow.REJECT
                                : AccumulatorWhitelist.accumulatorUsageRow(AccumulatorWhitelist.classifyingOwner(site.getDeclaringClass(), f.dispatchOwner()), site.getMethodName(), f.role());
                if (row == AccumulatorWhitelist.AccRow.REJECT) {
                    ok = false;
                    break;
                }
                String enc = StringAnalysisPolicy.enclosingClassName(site);
                if (row == AccumulatorWhitelist.AccRow.GROWING && site.getNodeType() == SugNodeType.STRING_METHOD_CALL && enc != null &&
                                StringAnalysisPolicy.isUserCodeClass(enc) && site.getId() < TARGET_SITE_ID_BASE &&
                                AccumulatorWhitelist.isSeedableExtraction(AccumulatorWhitelist.classifyingOwner(site.getDeclaringClass(), f.dispatchOwner()), site.getMethodName(),
                                                site.getMethodSignature())) {
                    ext.add(site);
                }
            }
            if (!ok) {
                continue;
            }
            pass1++;
            for (jdk.graal.compiler.nodes.ValueNode b : seed.births) {
                admittedBirths.put(b, seed.vertex);
            }
            for (SugVertex e : ext) {
                extractionOwners.computeIfAbsent(e, k -> new LinkedHashSet<>()).add(seed.vertex);
            }
        }
        List<SugVertex> sites = new ArrayList<>(extractionOwners.keySet());
        sites.sort(Comparator.comparing((SugVertex v) -> String.valueOf(v.getSourceLocation())).thenComparingInt(SugVertex::getId));
        // First, per site, the IR invokes and the within-method verdict (printed only); a backward receiver sink is
        // attached at every site.
        List<AccSite> cases = new ArrayList<>(sites.size());
        int sinks = 0;
        for (SugVertex e : sites) {
            AccSite c = new AccSite(e);
            cases.add(c);
            AnalysisMethod m = e.getEnclosingMethod();
            c.frame = m != null ? localFlows.get(m) : null;
            StructuredGraph g = c.frame != null ? rtrack.graphOf(c.frame) : null;
            int bci = seedBci(e);
            if (g != null && bci >= 0) {
                for (jdk.graal.compiler.graph.Node n : g.getNodes()) {
                    if (n instanceof jdk.graal.compiler.nodes.Invoke inv && StringAnalysisChildInlining.pointsToBci(inv) == bci && n instanceof jdk.graal.compiler.nodes.ValueNode vn &&
                                    !StringAnalysisChildInlining.isFromInlinedScope(inv) && inv.callTarget() != null && inv.callTarget().targetMethod() != null &&
                                    "toString".equals(inv.callTarget().targetMethod().getName()) && !inv.callTarget().arguments().isEmpty()) {
                        c.births.add(vn);
                        c.receivers.add(inv.callTarget().arguments().get(0));
                    }
                }
            }
            if (c.births.isEmpty()) {
                continue;
            }
            // the within-method verdict: every receiver's local origins are pass-1 births
            String localWhy = null;
            for (jdk.graal.compiler.nodes.ValueNode r : c.receivers) {
                Set<jdk.graal.compiler.graph.Node> origins = new LinkedHashSet<>();
                if (!localBuilderOrigins(r, origins, new HashSet<>())) {
                    localWhy = "receiver not local (a parameter, a load or another origin)";
                    break;
                }
                for (jdk.graal.compiler.graph.Node o : origins) {
                    if (admittedBirths.get(o) == null) {
                        localWhy = localWhy != null ? localWhy : "receiver from an allocation that is not a pass-1 accumulator";
                    }
                }
            }
            c.localWhy = localWhy;
            for (jdk.graal.compiler.nodes.ValueNode r : c.receivers) {
                List<ClosedFieldEscape.FieldStoreSite> stores = fieldHeldStores(e, r);
                if (stores != null) {
                    // The receiver is this.f of a store-closed field: its values are exactly the stored values
                    // (or null), each resolved backward in its own frame; the holder is not resolved
                    c.fieldHeld = true;
                    for (ClosedFieldEscape.FieldStoreSite st : stores) {
                        if (st.value() == null) {
                            c.sinks.add(null); // an unresolvable stored value: UNRESOLVED_VALUE (recvSinks)
                            continue;
                        }
                        LocalFlowGraph sf = st.frame();
                        jdk.graal.compiler.nodes.ValueNode sv = st.value();
                        c.sinks.add(rtrack.attachOperandSink("accrecv", sf, sv, sk -> rtrack.backward(sf, sv, ContextPolicy.MethodContext.UNKNOWN, null, sk),
                                        ContextPolicy.MethodContext.UNKNOWN, null, List.of("accrecv", sv), x -> {
                                        }, x -> {
                                        }, null, c.idDep));
                        sinks++;
                    }
                    continue;
                }
                LocalFlowGraph fr = c.frame;
                c.sinks.add(rtrack.attachOperandSink("accrecv", fr, r, sk -> rtrack.backward(fr, r, ContextPolicy.MethodContext.UNKNOWN, null, sk),
                                ContextPolicy.MethodContext.UNKNOWN, null, List.of("accrecv", r), x -> {
                                }, x -> {
                                }, null, c.idDep)); // ID-DEP reaches the extraction candidate (emit)
                sinks++;
            }
        }
        long recvNs = 0L;
        int atomsBefore = rtrack.atoms.size();
        Set<RecursiveTracking.RAtomKey> keysBefore = sinks > 0 ? new HashSet<>(rtrack.atoms.keySet()) : Set.of();
        if (sinks > 0) {
            long t = System.nanoTime();
            drainToQuiescence(parallelMode); // the receiver sinks resolve (and the container atoms they mint walk)
            recvNs = System.nanoTime() - t;
        }
        int atomsAfter = rtrack.atoms.size();
        long newAtomSteps = 0L;
        int newRefused = 0;
        if (sinks > 0) {
            for (Map.Entry<RecursiveTracking.RAtomKey, RecursiveTracking.RAtom> en : rtrack.atoms.entrySet()) {
                if (!keysBefore.contains(en.getKey())) {
                    newAtomSteps += en.getValue().steps.get();
                    newRefused += en.getValue().table.refusalsSnapshot().isEmpty() ? 0 : 1;
                }
            }
        }
        // Then the verdicts. A site qualifies iff the backward resolution completed with no refusal and every atom it
        // found is born at a pass-1 accumulator's allocation.
        int seeded = 0;
        int byBwd = 0;
        for (AccSite c : cases) {
            SugVertex e = c.site;
            String why;
            Set<SugVertex> owners = new LinkedHashSet<>();
            if (c.births.isEmpty()) {
                why = "no IR invoke at the site";
            } else {
                RecvVerdict<SugVertex> bv = receiverVerdict(recvSinks(c, allBirths), admittedBirths, rtrack.guardTripped());
                c.bwd = bv;
                String bwdWhy = bv.why();
                Set<SugVertex> bwdOwners = bv.owners();
                int bwdAtoms = bv.atoms();
                boolean bwdOk = bwdWhy == null;
                System.out.println("[sug-acc-recv] " + e.getSourceLocation() + " local=" + (c.localWhy == null ? "OK" : "NO") + " bwd=" +
                                (c.sinks.isEmpty() ? "-" : bwdOk ? "OK atoms=" + bwdAtoms : "NO (" + bwdWhy + ")") + (c.fieldHeld ? " field-held" : ""));
                if (bwdOk) {
                    byBwd++;
                    why = null;
                    owners.addAll(bwdOwners);
                } else {
                    why = c.sinks.isEmpty() ? c.localWhy : bwdWhy;
                }
            }
            if (why != null) {
                sug.accExtractionUnseeded().put(e, why);
                System.out.println("[sug-acc-extraction] UNSEEDED " + e.getSourceLocation() + " : " + why);
                continue;
            }
            sug.accExtractionReceivers().put(e, owners);
            accSeededSites.add(c);
            StringAtoms.StringSeed seed = new StringAtoms.StringSeed(e, "ACCX", c.frame, c.births, null);
            rtrack.mintString(seed);
            seeded++;
            System.out.println("[sug-strack-seed] ACCX " + e.getSourceLocation() + " births=" + c.births.size() + " owners=" + owners.size());
        }
        accAdmittedBirths = admittedBirths;
        accAllBirths = allBirths;
        System.out.println("[sug-acc-pass] accumulators=" + accSeeds.size() + " pass1=" + pass1 + " extractions=" + sites.size() + " seeded=" + seeded);
        System.out.println("[sug-acc-recv-cost] mode=2 sinks=" + sinks + " drainMs=" + (recvNs / 1_000_000) + " atoms=" + atomsBefore + "->" + atomsAfter +
                        " newAtomSteps=" + newAtomSteps + " newAtomsRefused=" + newRefused +
                        " qualified(local-only/bwd-only/both)=0/" + byBwd + "/0");
        return seeded > 0;
    }

    /** Per field, its store sites or (a String) why it is not store-closed; one census line per field. */
    private final Map<com.oracle.graal.pointsto.meta.AnalysisField, Object> fieldRecvSeen = new HashMap<>();

    /**
     * The store sites that replace receiver {@code r} of extraction {@code e} (field-held receivers), else null
     * (not a field load, or the field is not store-closed: the holder walk).
     *
     * <p>Field-held receivers: a pass-2 receiver that is a load {@code h.f} of a
     * reference instance field whose stores are closed ({@link ClosedFieldEscape#fieldStoreSites}: no
     * Unsafe/VarHandle/updater/reflective/MethodHandle/serialization/JNI channel, no substitution, no offset taken, no
     * unframed {@code putfield} of its name:type, no holder instance in the image heap, a closed-world build) is
     * resolved as the union of the values of every IR store to {@code f} (each by a backward sink in its own frame)
     * instead of resolving the holder: a read of {@code f} yields null or a value some store wrote. Same verdict
     * ({@link #receiverVerdict}), re-taken after the final drain. Other fields take the holder walk.
     */
    @SuppressWarnings("unchecked")
    private List<ClosedFieldEscape.FieldStoreSite> fieldHeldStores(SugVertex e, jdk.graal.compiler.nodes.ValueNode r) {
        jdk.graal.compiler.nodes.java.LoadFieldNode lfn = fieldLoadOf(r);
        if (lfn == null) {
            return null;
        }
        com.oracle.graal.pointsto.meta.AnalysisField f = rtrack.bridge.resolveField(lfn.field());
        if (f == null) {
            return null;
        }
        Object st = rtrack.closedField.fieldStoreSites(f);
        if (fieldRecvSeen.put(f, st) == null) {
            System.out.println("[sug-acc-fieldrecv] " + e.getSourceLocation() + " field=" + f.format("%H.%n") + " " +
                            (st instanceof List<?> l ? "closed stores=" + l.size() : "open " + st));
        }
        return st instanceof List<?> l ? (List<ClosedFieldEscape.FieldStoreSite>) l : null;
    }

    /** Pure: the reference instance-field load {@code r} is (through null-check pis and non-phi proxies), else null. */
    static jdk.graal.compiler.nodes.java.LoadFieldNode fieldLoadOf(jdk.graal.compiler.nodes.ValueNode r) {
        jdk.graal.compiler.nodes.ValueNode v = r;
        for (int i = 0; i < 16 && v != null; i++) {
            if (v instanceof jdk.graal.compiler.nodes.java.LoadFieldNode lfn) {
                return !lfn.field().isStatic() && lfn.field().getJavaKind() == jdk.vm.ci.meta.JavaKind.Object ? lfn : null;
            }
            if (v instanceof jdk.graal.compiler.nodes.PiNode pi) {
                v = pi.object();
            } else if (v instanceof jdk.graal.compiler.nodes.spi.ValueProxy vp && !(v instanceof jdk.graal.compiler.nodes.PhiNode)) {
                v = vp.getOriginalNode();
            } else {
                return null;
            }
        }
        return null;
    }

    /** One pass-2 candidate site (its invokes, receivers, the within-method verdict, the receiver sinks). */
    private static final class AccSite {
        final SugVertex site;
        LocalFlowGraph frame;
        final List<jdk.graal.compiler.nodes.ValueNode> births = new ArrayList<>(1);
        final List<jdk.graal.compiler.nodes.ValueNode> receivers = new ArrayList<>(1);
        String localWhy;
        final List<ContainerTables.Sink> sinks = new ArrayList<>(1);
        /** The backward verdict taken at the receiver quiescence. */
        RecvVerdict<SugVertex> bwd;
        /** A receiver was resolved as a field-held receiver (its stores' values). */
        boolean fieldHeld;
        /** Set when a receiver sink is ID-DEP (its resolution read an object-return rule delivery). */
        final ContainerTables.DepFlag idDep = new ContainerTables.DepFlag();

        AccSite(SugVertex site) {
            this.site = site;
        }
    }

    /**
     * The receiver verdicts re-taken after the final drain (the ACCX seeds' drain runs further round boundaries). A
     * site whose backward verdict changed is withdrawn from {@code accExtractionReceivers} (the heuristic has not run
     * yet) and reported unseeded.
     */
    private void accRecheckReceivers() {
        int withdrawn = 0;
        for (AccSite c : accSeededSites) {
            if (c.bwd == null || c.sinks.isEmpty()) {
                continue;
            }
            RecvVerdict<SugVertex> now = receiverVerdict(recvSinks(c, accAllBirths), accAdmittedBirths, rtrack.guardTripped());
            if (now.equals(c.bwd)) {
                continue;
            }
            withdrawn++;
            String why = "receiver verdict changed after the final drain: " + (now.why() != null ? now.why() : "owners " + now.owners().size() + " (were " + c.bwd.owners().size() + ")");
            sug.accExtractionReceivers().remove(c.site);
            sug.accExtractionUnseeded().put(c.site, why);
            System.out.println("[sug-acc-extraction] WITHDRAWN " + c.site.getSourceLocation() + " : " + why);
        }
        System.out.println("[sug-acc-recheck] seeded=" + accSeededSites.size() + " withdrawn=" + withdrawn);
    }

    /** One atom of a receiver sink as the verdict reads it: its birth (null = none) and a stable name. */
    record RecvAtom(Object birth, String stableKey) {
    }

    /** One receiver sink as the verdict reads it ({@code refusals == null}: no sink could be attached). */
    record RecvSink(List<ContainerTables.RTrackRefusal> refusals, List<RecvAtom> atoms) {
    }

    /** The backward receiver verdict: {@code why == null} = the site qualifies, with these owners. */
    record RecvVerdict<O>(String why, Set<O> owners, int atoms) {
    }

    /**
     * Pure; pinned by {@code AccumulatorRulesTest}: the backward receiver verdict over a site's receiver sinks. In order:
     * no sink -> "not run"; any refusal (a sink that could not be attached counts as UNRESOLVED_VALUE) -> REJECT naming
     * the sorted distinct refusals; the global guard tripped -> REJECT; an atom without a birth (an image-heap
     * constant, the current thread) or whose birth is not a pass-1 accumulator's -> REJECT naming the least such atom
     * by its stable key (independent of drain order and identity hashes). Else the site qualifies with the owners its
     * atoms map to (an empty owner set is left to the heuristic, which rejects it).
     */
    static <O> RecvVerdict<O> receiverVerdict(List<RecvSink> sinks, Map<?, O> admittedBirths, boolean guardTripped) {
        if (sinks.isEmpty()) {
            return new RecvVerdict<>("not run", Set.of(), 0);
        }
        java.util.TreeSet<String> refusals = new java.util.TreeSet<>();
        java.util.TreeSet<String> foreign = new java.util.TreeSet<>();
        Set<O> owners = new LinkedHashSet<>();
        int atoms = 0;
        for (RecvSink sk : sinks) {
            if (sk.refusals() == null) {
                refusals.add(String.valueOf(ContainerTables.RTrackRefusal.UNRESOLVED_VALUE));
                continue;
            }
            if (!sk.refusals().isEmpty()) {
                for (ContainerTables.RTrackRefusal r : sk.refusals()) {
                    refusals.add(String.valueOf(r));
                }
                continue;
            }
            for (RecvAtom a : sk.atoms()) {
                atoms++;
                O owner = a.birth() != null ? admittedBirths.get(a.birth()) : null;
                if (owner == null) {
                    foreign.add(a.stableKey());
                } else {
                    owners.add(owner);
                }
            }
        }
        String why;
        if (!refusals.isEmpty()) {
            why = "backward receiver refused " + refusals;
        } else if (guardTripped) {
            why = "backward receiver: EVALUATION_GUARD";
        } else if (!foreign.isEmpty()) {
            why = "backward receiver reaches an object that is not a pass-1 accumulator (" + foreign.first() + (foreign.size() > 1 ? ", +" + (foreign.size() - 1) + " more" : "") + ")";
        } else {
            why = null;
        }
        return new RecvVerdict<>(why, why == null ? owners : Set.of(), atoms);
    }

    /** The verdict's view of a site's sinks (snapshots; each atom with its birth and stable key). */
    private List<RecvSink> recvSinks(AccSite c, Set<jdk.graal.compiler.graph.Node> allAccBirths) {
        List<RecvSink> out = new ArrayList<>(c.sinks.size());
        for (ContainerTables.Sink sk : c.sinks) {
            if (sk == null) {
                out.add(new RecvSink(null, List.of()));
                continue;
            }
            List<RecvAtom> atoms = new ArrayList<>();
            for (Object k : sk.atomsSnapshot()) {
                RecursiveTracking.RAtom xa = k instanceof RecursiveTracking.RAtomKey rk ? rtrack.atoms.get(rk) : null;
                atoms.add(new RecvAtom(xa != null ? xa.birthNode : null, stableAtomKey(xa, allAccBirths)));
            }
            out.add(new RecvSink(sk.refusalsSnapshot(), atoms));
        }
        return out;
    }

    /**
     * A deterministic name of a receiver atom for the REJECT text (never an identity hash or node id):
     * {@code constant <type>}, {@code failed-seed <method>@<bci>} (an ACC seed that did not pass pass 1), or
     * {@code birth <method>@<bci> <type>}.
     */
    static String stableAtomKey(RecursiveTracking.RAtom xa, Set<jdk.graal.compiler.graph.Node> allAccBirths) {
        if (xa == null) {
            return "unknown-atom";
        }
        if (xa.birthNode == null) {
            String type = xa.constant != null && xa.constant.getType() != null ? xa.constant.getType().toJavaName(true) : String.valueOf(xa.kind);
            return "constant " + type;
        }
        jdk.graal.compiler.graph.NodeSourcePosition p = StringAtoms.allocationPosition(xa.birthNode);
        String where;
        if (p != null && p.getMethod() != null) {
            where = p.getMethod().format("%H.%n(%p)") + "@" + p.getBCI();
        } else {
            where = (xa.birthFrame != null && xa.birthFrame.getMethod() != null ? xa.birthFrame.getMethod().format("%H.%n(%p)") : "?") + "@?";
        }
        if (allAccBirths.contains(xa.birthNode)) {
            return "failed-seed " + where;
        }
        jdk.vm.ci.meta.ResolvedJavaType t = StringAtoms.allocatedType(xa.birthNode);
        return "birth " + where + (t != null ? " " + t.toJavaName(true) : "");
    }

    /**
     * The intra-procedural origins of a builder value, through Pi/proxy/Phi and the result of a builder
     * {@code append}/{@code appendCodePoint}/{@code repeat} (which return {@code this}), to its
     * {@code NewInstanceNode}s. False when any origin is something else (a parameter, a load, another invoke, a
     * constant).
     */
    static boolean localBuilderOrigins(jdk.graal.compiler.nodes.ValueNode v, Set<jdk.graal.compiler.graph.Node> out, Set<jdk.graal.compiler.graph.Node> seen) {
        if (v == null) {
            return false;
        }
        if (!seen.add(v)) {
            return true;
        }
        if (StringAtoms.allocatedType(v) != null) {
            out.add(v);
            return true;
        }
        if (v instanceof jdk.graal.compiler.nodes.PiNode pi) {
            return localBuilderOrigins(pi.object(), out, seen);
        }
        if (v instanceof jdk.graal.compiler.nodes.spi.ValueProxy vp && !(v instanceof jdk.graal.compiler.nodes.PhiNode)) {
            return localBuilderOrigins(vp.getOriginalNode(), out, seen);
        }
        if (v instanceof jdk.graal.compiler.nodes.ValuePhiNode phi) {
            for (jdk.graal.compiler.nodes.ValueNode in : phi.values()) {
                if (!localBuilderOrigins(in, out, seen)) {
                    return false;
                }
            }
            return true;
        }
        if (v instanceof jdk.graal.compiler.nodes.Invoke inv && inv.callTarget() != null && inv.callTarget().targetMethod() != null &&
                        !inv.callTarget().arguments().isEmpty()) {
            jdk.vm.ci.meta.ResolvedJavaMethod t = inv.callTarget().targetMethod();
            String decl = t.getDeclaringClass().toJavaName(true);
            if (!t.isStatic() && AccumulatorWhitelist.returnsThis(decl, t.getName())) {
                return localBuilderOrigins(inv.callTarget().arguments().get(0), out, seen);
            }
        }
        return false;
    }

    /**
     * The Single Byte creation-site seed rule: a {@code substring} or {@code valueOf(char)} STRING_METHOD_CALL whose
     * length is 1 or not yet known. Seeding runs before {@code LengthPropagator}, so these vertices are still
     * {@code UNKNOWN_LENGTH} and a {@code getLength() == 1} gate would be dead; {@code SingleByteHeuristic.isCandidate}'s
     * post-propagator check stays the length filter. User-code filtering is the caller's.
     */
    static boolean isSbCreationSeed(SugVertex v) {
        if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL) {
            return false;
        }
        boolean valueOfChar = "valueOf".equals(v.getMethodName()) && ("char".equals(v.getMethodSignature()) || "C".equals(v.getMethodSignature()));
        if (!"substring".equals(v.getMethodName()) && !valueOfChar) {
            return false;
        }
        return v.getLength() == 1 || v.getLength() == SugVertex.UNKNOWN_LENGTH;
    }

    /** The text of a String {@code ConstantNode} (the reading LfgWalk's scan uses), else null. */
    private String literalText(jdk.graal.compiler.nodes.ConstantNode cn) {
        jdk.vm.ci.meta.JavaConstant jc = cn.asJavaConstant();
        if (jc == null || jc.getJavaKind() != jdk.vm.ci.meta.JavaKind.Object || lfgWalk == null || lfgWalk.builder() == null) {
            return null;
        }
        try {
            return lfgWalk.builder().bb.getSnippetReflectionProvider().asObject(String.class, jc);
        } catch (Throwable t) {
            return null;
        }
    }

    /** The usage-site adapter of the string rows (the verdict interface). */
    private final class StrackSites implements StringAtoms.Sites {
        private final Block stringBlock;
        private final AnalysisMethod objectToString;
        private final java.util.concurrent.ConcurrentHashMap<List<Object>, SugVertex> detached = new java.util.concurrent.ConcurrentHashMap<>();
        private final java.util.concurrent.ConcurrentHashMap<jdk.graal.compiler.graph.Node, StringAtoms.Concat> concatMemo = new java.util.concurrent.ConcurrentHashMap<>();
        private final LongAdder concatReadFailures = new LongAdder();
        private final LongAdder concatUnreadableRefused = new LongAdder();
        /** Print-only: invokes whose bci holds a readable non-INVOKEDYNAMIC opcode, and of those the refused. */
        private final LongAdder concatNonIndyOpcode = new LongAdder();
        private final LongAdder concatNonIndyRefused = new LongAdder();
        private final java.util.concurrent.ConcurrentHashMap<List<Object>, List<LocalFlowGraph.TypeGuard>[]> armMemo = new java.util.concurrent.ConcurrentHashMap<>();

        StrackSites() {
            AnalysisType stringType = lfgWalk != null ? lfgWalk.builder().resolveAnalysisTypeByName("java.lang.String") : null;
            this.stringBlock = stringType != null ? Block.of(new LinkedHashSet<>(widenType(stringType))) : Block.TOP;
            AnalysisType objectType = lfgWalk != null ? lfgWalk.builder().resolveAnalysisTypeByName("java.lang.Object") : null;
            AnalysisMethod ts = null;
            if (objectType != null) {
                try {
                    for (AnalysisMethod dm : objectType.getDeclaredMethods(false)) {
                        if ("toString".equals(dm.getName()) && "()Ljava/lang/String;".equals(dm.getSignature().toMethodDescriptor())) {
                            ts = dm;
                        }
                    }
                } catch (Throwable t) {
                    ts = null;
                }
            }
            this.objectToString = ts;
        }

        @Override
        public Block stringBlock() {
            return stringBlock;
        }

        @Override
        public AnalysisMethod objectToString() {
            return objectToString;
        }

        private SugVertex phaseAVertexAt(LocalFlowGraph frame, jdk.graal.compiler.nodes.Invoke inv) {
            AnalysisMethod m = frameMethod.get(frame);
            Map<Integer, InvokeTypeFlow> byBci = m != null ? invokes.get(m) : null;
            Set<Integer> ambiguous = m != null && lfgWalk != null && lfgWalk.builder() != null ? lfgWalk.builder().methodBciInvokeAmbiguous.get(m) : null;
            InvokeTypeFlow f = SugBuilderV2.invokeFlowAt(byBci, ambiguous, inv, InvokeTypeFlow::getTargetMethod);
            return f != null ? sug.getVertex(f) : null;
        }

        @Override
        public SugVertex phaseACallSite(LocalFlowGraph frame, jdk.graal.compiler.nodes.Invoke inv) {
            SugVertex v = phaseAVertexAt(frame, inv);
            return v != null && (v.getNodeType() == SugNodeType.STRING_METHOD_CALL || v.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) ? v : null;
        }

        private SugVertex detachedSite(List<Object> key, AnalysisMethod ctx, int bci, String decl, String name, String sig, SugNodeType type, String label) {
            return detached.computeIfAbsent(key, k -> {
                SugVertex v = new SugVertex(TARGET_SITE_IDS.getAndIncrement());
                v.setEnclosingMethod(ctx);
                v.setDeclaringClass(decl);
                v.setMethodName(name);
                v.setMethodSignature(sig);
                v.setNodeType(type);
                String loc = ctx != null ? SiteKeys.profileKey(ctx, bci) : "fixture#m@" + bci;
                v.setSourceLocation(loc);
                v.setSourceKey(loc);
                v.setLabel(label);
                return v;
            });
        }

        private SugNodeType callSiteType(AnalysisMethod ctx) {
            String enc = ctx != null ? ctx.getDeclaringClass().toJavaName(true) : null;
            return StringAnalysisPolicy.isInternalClass(enc) ? SugNodeType.JDK_LIBRARY_CALL : SugNodeType.STRING_METHOD_CALL;
        }

        @Override
        public SugVertex concatSite(LocalFlowGraph frame, jdk.graal.compiler.nodes.Invoke inv) {
            SugVertex v = phaseAVertexAt(frame, inv);
            if (v == null || v.getNodeType() != SugNodeType.CONCAT_EXPRESSION) {
                AnalysisMethod ctx = frameMethod.get(frame);
                // the detached CONCAT_EXPRESSION site of a concat without a Phase-A vertex, keyed by (frame, bci)
                int bci = StringAnalysisChildInlining.pointsToBci(inv);
                v = detachedSite(java.util.Arrays.asList("concat", ctx, bci), ctx, bci, null, "makeConcatWithConstants", "",
                                SugNodeType.CONCAT_EXPRESSION, "concat(detached)");
            }
            // The site's strategy never copies an operand (indy F1 only); a pure function of the site, so idempotent.
            StringAtoms.Concat c = concatAt(frame, inv);
            if (c.kind() == StringAtoms.ConcatKind.F1 && !c.copiesOperand()) {
                v.markScfNoCopy();
            }
            // A copying site's shape (UNARY/BINARY; lowered with RepConcat). Not from a parse-time-inlined scope: such an
            // invoke is keyed on the root, which the parent's lowering (keyed on the inlinee) would never match
            if (c.kind() == StringAtoms.ConcatKind.F1 && (c.copyShape() == StringAtoms.CopyShape.UNARY || c.copyShape() == StringAtoms.CopyShape.BINARY) &&
                            !StringAnalysisChildInlining.isFromInlinedScope(inv)) {
                v.markScfCopyShape(c.copyShape());
            }
            return v;
        }

        @Override
        public SugVertex targetSite(LocalFlowGraph frame, LocalFlowGraph.LocalVertex call, AnalysisMethod target) {
            String decl = target.getDeclaringClass() != null ? target.getDeclaringClass().toJavaName(true) : "";
            return targetUsageSite(frameMethod.get(frame), call, target, decl);
        }

        private int bciOf(jdk.graal.compiler.graph.Node n) {
            jdk.graal.compiler.graph.NodeSourcePosition pos = n.getNodeSourcePosition();
            return pos != null ? pos.getBCI() : -1;
        }

        @Override
        public SugVertex fieldSite(LocalFlowGraph frame, jdk.graal.compiler.nodes.java.LoadFieldNode lfn) {
            AnalysisMethod ctx = frameMethod.get(frame);
            String decl = lfn.field().getDeclaringClass() != null ? lfn.field().getDeclaringClass().toJavaName(true) : "?";
            String fname = lfn.field().getName();
            int bci = bciOf(lfn);
            if ("java.lang.String".equals(decl)) {
                if ("hash".equals(fname) || "hashIsZero".equals(fname)) {
                    return null; // the String hash-cache protocol: not a usage (SugNameTables.rawStringFieldUsageName)
                }
                String usage = SugNameTables.rawStringFieldUsageName(fname);
                if (usage != null) {
                    // the Phase-A raw-read site's shape (SugBuilderV2.getOrCreateRawStringFieldReadSite), detached
                    return detachedSite(java.util.Arrays.asList("raw", ctx, bci, usage), ctx, bci, "java.lang.String", usage, "", SugNodeType.JDK_LIBRARY_CALL,
                                    "String." + usage);
                }
            }
            // a strict field usage (class, field): a name no whitelist admits
            String usage = StringAtoms.strictFieldUsageName(fname);
            return detachedSite(java.util.Arrays.asList("field", ctx, bci, decl, fname), ctx, bci, decl, usage, "", SugNodeType.JDK_LIBRARY_CALL,
                            decl.substring(decl.lastIndexOf('.') + 1) + "." + usage);
        }

        @Override
        public SugVertex classCheckSite(LocalFlowGraph frame, jdk.graal.compiler.nodes.ValueNode node, String label) {
            AnalysisMethod ctx = frameMethod.get(frame);
            int bci = bciOf(node);
            // the Phase-A class-check site's shape (SugBuilderV2.getOrCreateClassCheckSite: Object.getClass), detached
            return detachedSite(java.util.Arrays.asList("classcheck", ctx, bci), ctx, bci, "java.lang.Object", "getClass", "", SugNodeType.JDK_LIBRARY_CALL,
                            label != null ? label : "Object.getClass");
        }

        @Override
        public SugVertex classCheckSiteAt(AnalysisMethod ctx, int bci, String label) {
            // A JDK model's class check at an internal site (method, bci): the classCheckSite shape, keyed alike
            return detachedSite(java.util.Arrays.asList("classcheck", ctx, bci), ctx, bci, "java.lang.Object", "getClass", "", SugNodeType.JDK_LIBRARY_CALL,
                            label != null ? label : "Object.getClass");
        }

        @Override
        public boolean armDead(LocalFlowGraph frame, jdk.graal.compiler.graph.Node anchor, jdk.graal.compiler.nodes.ValueNode observed, Block block) {
            int dead = armFeasibility(frame, anchor, observed, block);
            if (dead == 1) {
                armSkipVacuous.increment();
            } else if (dead == 2) {
                armSkipNever.increment();
            }
            return dead != 0;
        }

        @Override
        public int armFeasibility(LocalFlowGraph frame, jdk.graal.compiler.graph.Node anchor, jdk.graal.compiler.nodes.ValueNode observed, Block block) {
            return ForwardFixpoint.armFeasibility(frame, anchor, observed, block, armMemo);
        }

        @Override
        public boolean strictExactInstanceOf(LocalFlowGraph frame, jdk.graal.compiler.nodes.java.InstanceOfNode ion) {
            AnalysisMethod m = frameMethod.get(frame);
            if (lfgWalk == null) {
                return true;
            }
            return !LfgWalk.instanceofSourceFoldAllowed(ion, m, lfgWalk.builder()::resolveAnalysisType);
        }

        @Override
        public StringAtoms.Concat concatAt(LocalFlowGraph frame, jdk.graal.compiler.nodes.Invoke inv) {
            return concatMemo.computeIfAbsent(inv.asNode(), k -> recogniseConcat(frame, inv));
        }

        /** The SCF indy test on the bytecode (the capture plugin's test), then the F1 shape. */
        private StringAtoms.Concat recogniseConcat(LocalFlowGraph frame, jdk.graal.compiler.nodes.Invoke inv) {
            AnalysisMethod m = frameMethod.get(frame);
            jdk.graal.compiler.nodes.CallTargetNode ct0 = inv.callTarget();
            String irTarget = ct0 != null && ct0.targetMethod() != null ? ct0.targetMethod().getName() : null;
            int bci = StringAnalysisChildInlining.pointsToBci(inv); // the frame's own bytecode index of the call
            if (m == null || bci < 0) {
                return unreadableConcat(irTarget, false);
            }
            jdk.vm.ci.meta.ConstantPool.BootstrapMethodInvocation bmi;
            boolean indy = false;
            try {
                jdk.vm.ci.meta.ResolvedJavaMethod raw = m.getWrapped();
                byte[] code = raw.getCode();
                if (code == null || bci >= code.length) {
                    return unreadableConcat(irTarget, false);
                }
                jdk.graal.compiler.bytecode.BytecodeStream s = new jdk.graal.compiler.bytecode.BytecodeStream(code);
                s.setBCI(bci);
                if (s.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.INVOKEDYNAMIC) {
                    // linkToTargetMethod at a non-indy opcode: the bci does not index this frame's bytecode (e.g. a
                    // substitution); it may be an unseen SCF concat -> the named refusal.
                    concatNonIndyOpcode.increment();
                    if (StringAtoms.nonIndyOpcodeSite(irTarget) == StringAtoms.ConcatKind.UNRECOGNISED) {
                        concatNonIndyRefused.increment();
                        return StringAtoms.Concat.UNRECOGNISED;
                    }
                    return StringAtoms.Concat.NONE;
                }
                indy = true;
                bmi = raw.getConstantPool().lookupBootstrapMethodInvocation(s.readCPI4(), jdk.graal.compiler.bytecode.Bytecodes.INVOKEDYNAMIC);
            } catch (Throwable t) {
                // an indy (or linkToTargetMethod) site we cannot read is refused by name, never the ordinary crossing
                return unreadableConcat(irTarget, indy);
            }
            jdk.vm.ci.meta.ResolvedJavaMethod boot = bmi != null ? bmi.getMethod() : null;
            if (boot == null) {
                return unreadableConcat(irTarget, true); // an indy whose bootstrap cannot be read
            }
            if (StringAtoms.isTypeSwitchBootstrap(boot.getDeclaringClass().toJavaName(true), boot.getName(), boot.getSignature().toMethodDescriptor())) {
                return recogniseTypeSwitch(bmi, inv, irTarget);
            }
            if (!"java.lang.invoke.StringConcatFactory".equals(boot.getDeclaringClass().toJavaName(true)) ||
                            !(boot.getName().equals("makeConcat") || boot.getName().equals("makeConcatWithConstants"))) {
                return StringAtoms.Concat.NONE;
            }
            // an SCF site: F1, or a named refusal
            java.lang.invoke.MethodType mt;
            try {
                mt = com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(java.lang.invoke.MethodType.class, bmi.getType());
            } catch (Throwable t) {
                mt = null;
            }
            jdk.graal.compiler.nodes.CallTargetNode ct = inv.callTarget();
            if (mt == null || ct == null || ct.targetMethod() == null) {
                return StringAtoms.Concat.UNRECOGNISED;
            }
            var args = ct.arguments();
            int nargs = args.size();
            boolean lastConst = nargs > 0 && args.get(nargs - 1) != null && args.get(nargs - 1).isConstant();
            if (StringAtoms.f1Shape(ct.targetMethod().getName(), nargs, lastConst, mt.parameterCount()) != StringAtoms.ConcatKind.F1) {
                return StringAtoms.Concat.UNRECOGNISED;
            }
            int dyn = mt.parameterCount();
            boolean[] str = new boolean[dyn];
            boolean[] prim = new boolean[dyn];
            AnalysisType[] types = new AnalysisType[dyn];
            for (int i = 0; i < dyn; i++) {
                Class<?> pt = mt.parameterType(i);
                str[i] = pt == String.class;
                prim[i] = pt.isPrimitive();
                jdk.graal.compiler.nodes.ValueNode a = args.get(i);
                if (!pt.isPrimitive() && a != null) {
                    // the CHA root of the desugared toString(): the operand's own stamp type (sound: the runtime value is in it)
                    jdk.vm.ci.meta.ResolvedJavaType st = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(a.stamp(jdk.graal.compiler.nodes.NodeView.DEFAULT));
                    types[i] = st instanceof AnalysisType at ? at : null;
                }
            }
            // The JDK strategy's copy test (StringAtoms.scfCopiesOperand); an unreadable recipe copies
            String recipe = null;
            if ("makeConcatWithConstants".equals(boot.getName())) {
                try {
                    java.util.List<jdk.vm.ci.meta.JavaConstant> sa = bmi.getStaticArguments();
                    recipe = sa != null && !sa.isEmpty() ? com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection().asObject(String.class, sa.get(0)) : null;
                } catch (Throwable t) {
                    recipe = null;
                }
            }
            return new StringAtoms.Concat(StringAtoms.ConcatKind.F1, str, types, StringAtoms.scfCopyShape(boot.getName(), recipe, prim));
        }

        /**
         * A {@code SwitchBootstraps.typeSwitch} site: {@link StringAtoms.Concat#TYPESWITCH} when
         * {@link StringAtoms#typeSwitchRefusal} finds nothing to refuse, else {@link StringAtoms.Concat#NONE}.
         */
        private StringAtoms.Concat recogniseTypeSwitch(jdk.vm.ci.meta.ConstantPool.BootstrapMethodInvocation bmi, jdk.graal.compiler.nodes.Invoke inv, String irTarget) {
            Class<?>[] params = null;
            Class<?> ret = null;
            List<Object> labels = null;
            try {
                var snippets = com.oracle.graal.pointsto.util.GraalAccess.getOriginalSnippetReflection();
                java.lang.invoke.MethodType mt = snippets.asObject(java.lang.invoke.MethodType.class, bmi.getType());
                if (mt != null) {
                    params = mt.parameterArray();
                    ret = mt.returnType();
                }
                labels = StringAtoms.typeSwitchLabels(bmi.getStaticArguments(), c -> snippets.asObject(Object.class, c));
            } catch (Throwable t) {
                labels = null;
            }
            jdk.graal.compiler.nodes.CallTargetNode ct = inv.callTarget();
            var args = ct != null ? ct.arguments() : null;
            int nargs = args != null ? args.size() : -1;
            boolean lastConst = nargs > 0 && args.get(nargs - 1) != null && args.get(nargs - 1).isConstant();
            String refusal = StringAtoms.typeSwitchRefusal(params, ret, irTarget, nargs, lastConst, labels, StringAtoms.TYPESWITCH_REPS);
            StringAtoms.countTypeSwitchSite(refusal == null ? "modelled" : refusal);
            return refusal == null ? StringAtoms.Concat.TYPESWITCH : StringAtoms.Concat.NONE;
        }

        /** A site whose bytecode or bootstrap cannot be read ({@link StringAtoms#unreadableSite}), counted. */
        private StringAtoms.Concat unreadableConcat(String irTarget, boolean knownIndy) {
            concatReadFailures.increment();
            if (StringAtoms.unreadableSite(irTarget, knownIndy) == StringAtoms.ConcatKind.UNRECOGNISED) {
                concatUnreadableRefused.increment();
                return StringAtoms.Concat.UNRECOGNISED;
            }
            return StringAtoms.Concat.NONE;
        }

        @Override
        public long[] concatUnreadable() {
            return new long[]{concatReadFailures.sum(), concatUnreadableRefused.sum(), concatNonIndyOpcode.sum(), concatNonIndyRefused.sum()};
        }
    }

    void emit() {
        Map<UsageFact, Integer> usageIndex = new LinkedHashMap<>();
        List<UsageTag> usageTags = new ArrayList<>();
        Map<SourceTag, Integer> sourceIndex = new LinkedHashMap<>();
        List<SourceTag> sourceTags = new ArrayList<>();
        Map<SugVertex, EmissionAggregate> aggregates = new LinkedHashMap<>();

        for (SugVertex vertex : sug.getVertices()) {
            vertex.setUsageTags(new BitSet());
            vertex.getSourceTags().clear();
            vertex.clearResourceLimitedTrace();
            vertex.clearWiredAnyLoad();
            vertex.clearIdDep();
            vertex.clearEmittedAtom();
        }
        strackAggregates(aggregates); // the string atoms' facts, in the emit form
        sug.setTypeCheckObservations(typeCheckObservations()); // type-check inline cache: observations only (no tag, no verdict)
        for (Map.Entry<SugVertex, EmissionAggregate> entry : aggregates.entrySet()) {
            SugVertex source = entry.getKey();
            EmissionAggregate aggregate = entry.getValue();
            source.markEmittedAtom(); // read by AccumulatorHeuristic
            BitSet bits = source.getUsageTags();
            String d2Names = aggregate.d2Token();
            source.setBudgetRefusal(d2Names);
            List<UsageFact> orderedFacts = new ArrayList<>(aggregate.usages);
            if (d2Names != null) {
                orderedFacts.clear(); // any refusal: the emitted usage list is suppressed
            }
            orderedFacts.sort(USAGE_FACT_ORDER);
            for (UsageFact fact : orderedFacts) {
                int usageTag = usageIndex.computeIfAbsent(fact, k -> {
                    usageTags.add(new UsageTag(k.usageSite(), k.role(), k.argumentIndex(), k.dispatchOwner()));
                    return usageTags.size() - 1;
                });
                bits.set(usageTag);
                SourceTag sourceTag = new SourceTag(source, fact.role(), fact.argumentIndex());
                int sourceTagId = sourceIndex.computeIfAbsent(sourceTag, k -> {
                    sourceTags.add(k);
                    return sourceTags.size() - 1;
                });
                fact.usageSite().getSourceTags().set(sourceTagId);
            }
            if (d2Names != null) {
                source.markIncompleteTrace(); // d2all: never masked
            } else if (aggregate.incomplete) {
                // No safe-sink mask: an incomplete candidate is marked.
                source.markIncompleteTrace();
            } else {
                source.clearIncompleteTrace();
            }
            if (aggregate.resourceLimited) {
                source.markResourceLimitedTrace();
            }
            if (aggregate.wiredAnyLoad) {
                source.markWiredAnyLoad();
            }
            if (aggregate.idDep) {
                source.markIdDep(); // read only by the cross-candidate precedence
            }
            if (aggregate.stored) {
                source.markStored(); // read only by the accumulator view's variant (AccumulatorHeuristic.accVariant)
            }
        }
        // An accumulator extraction whose receiver sinks read an object-return rule delivery is ID-DEP
        for (AccSite c : accSeededSites) {
            if (c.idDep.idDep()) {
                c.site.markIdDep();
            }
        }
        for (SugVertex vertex : sug.getVertices()) {
            if (TransferFacts.isPotentialOrigin(vertex) && !aggregates.containsKey(vertex)) {
                vertex.markIncompleteTrace();
            }
        }
        sug.setUsageTags(usageTags);
        sug.setSourceTags(sourceTags);
        sug.setUsageSourceBuilt();
    }

    /**
     * The candidate line's usage list in a canonical order: {@code summary.usages} is insertion-ordered, so parallel
     * and serial runs could print it differently. The sort key is the rendered element itself, a total order in which
     * equal keys are identical strings, so the output is byte-comparable across runs.
     */
    private static String usageSites(Set<UsageFact> usages) {
        List<String> rendered = new ArrayList<>(usages.size());
        for (UsageFact fact : usages) {
            SugVertex site = fact.usageSite();
            rendered.add((site != null && site.getSourceLocation() != null ? site.getSourceLocation() : "null") +
                            ":" + fact.role() + ":" + fact.argumentIndex());
        }
        java.util.Collections.sort(rendered);
        StringBuilder sb = new StringBuilder("[");
        for (String r : rendered) {
            if (sb.length() > 1) {
                sb.append(", ");
            }
            sb.append(r);
        }
        return sb.append("]").toString();
    }

    /**
     * Some usage site is keyed in a hidden class other than the concat machinery ({@link SiteKeys#isHidden}): such an
     * atom takes the {@code HIDDEN_SINK} refusal.
     */
    static boolean hasHiddenSink(java.util.Collection<UsageFact> usages) {
        for (UsageFact u : usages) {
            if (u.usageSite() != null && isHiddenSinkKey(u.usageSite().getSourceLocation())) {
                return true;
            }
        }
        return false;
    }

    static boolean isHiddenSinkKey(String key) {
        if (key == null) {
            return false;
        }
        String cls = SiteKeys.classOf(key);
        return SiteKeys.isHidden(cls) && !StringAnalysisPolicy.isConcatMachineryClass(cls);
    }

    /**
     * Type-check inline cache: site key -> the seed vertices of the STRING atoms that observed it. Every atom counts,
     * refused or not (a superset: an extra creation site can only add reps to a site's list).
     */
    private Map<String, Set<SugVertex>> typeCheckObservations() {
        if (TypeCheckSites.MODE == 0) {
            return java.util.Collections.emptyMap();
        }
        List<RecursiveTracking.RAtom> sa;
        synchronized (rtrack.stringAtoms) {
            sa = new ArrayList<>(rtrack.stringAtoms.values());
        }
        Map<String, Set<SugVertex>> out = new java.util.TreeMap<>();
        for (RecursiveTracking.RAtom a : sa) {
            if (a.strTypeChecks == null || a.seed == null) {
                continue;
            }
            for (String k : a.strTypeChecks) {
                out.computeIfAbsent(k, x -> new LinkedHashSet<>()).add(a.seed.vertex);
            }
        }
        return out;
    }

    /**
     * The emit adapter: per seed, the STRING atom's usages, its refusal names (every string-walk incompleteness is a
     * named refusal, under the every-refusal-is-named rule {@code d2all}), the budget-class RESOURCE_LIMIT mark and
     * {@code wiredAnyLoad}. EVALUATION_GUARD refuses every atom (a global refusal).
     */
    private void strackAggregates(Map<SugVertex, EmissionAggregate> aggregates) {
        List<RecursiveTracking.RAtom> sa;
        synchronized (rtrack.stringAtoms) {
            sa = new ArrayList<>(rtrack.stringAtoms.values());
        }
        for (RecursiveTracking.RAtom a : sa) {
            SugVertex source = a.seed.vertex;
            EmissionAggregate aggregate = aggregates.computeIfAbsent(source, k -> new EmissionAggregate());
            aggregate.usages.addAll(a.strUsages);
            EnumSet<ContainerTables.RTrackRefusal> names = EnumSet.noneOf(ContainerTables.RTrackRefusal.class);
            names.addAll(a.table.refusalsSnapshot());
            if (hasHiddenSink(a.strUsages)) {
                names.add(ContainerTables.RTrackRefusal.HIDDEN_SINK);
            }
            if (rtrack.guardTripped()) {
                names.add(ContainerTables.RTrackRefusal.EVALUATION_GUARD);
            }
            aggregate.rtrackNames.addAll(names);
            List<IncompleteReason> reasons = new ArrayList<>();
            for (ContainerTables.RTrackRefusal r : names) {
                if (!reasons.contains(r.verdictReason())) {
                    reasons.add(r.verdictReason());
                }
                aggregate.resourceLimited |= r.budgetClass;
            }
            reasons.sort(Comparator.comparingInt(Enum::ordinal));
            aggregate.incomplete |= !names.isEmpty();
            aggregate.incompleteReasons.addAll(reasons);
            aggregate.wiredAnyLoad |= a.wiredAnyLoad;
            aggregate.idDep |= a.table.idDep(); // objret=1 only; false at objret=0
            aggregate.stored |= a.strStored || rtrack.elementContainerStored(a); // the confinement flag, from the same final facts as the usages (+ an element-source array's own heap escape)
            if (source.getNodeType() == SugNodeType.STRING_METHOD_CALL && ("substring".equals(source.getMethodName()) || "subSequence".equals(source.getMethodName()))) {
                boolean d2 = !names.isEmpty();
                Set<UsageFact> us = new LinkedHashSet<>(a.strUsages);
                if (d2) {
                    System.out.println("[sug-fwd-candidate] " + source.getSourceLocation() + " rtrackRefused (reasons/usages/stores suppressed)");
                    System.out.println("[sug-fwd-candidate-facts] " + source.getSourceLocation() + " downstreamFacts=[suppressed] rtrackRefusals=[refused]");
                }
                System.out.println((d2 ? "[sug-fwd-candidate-raw] " : "[sug-fwd-candidate] ") + source.getSourceLocation() +
                                " downstreamUsages=" + (d2 ? "suppressed" : String.valueOf(us.size())) +
                                ", reasons=" + reasons +
                                ", returns=false" +
                                ", stores=" + (d2 ? "suppressed" : String.valueOf(a.strEscapes.get())) +
                                ", wiredAnyLoad=" + a.wiredAnyLoad +
                                ", resourceLimited=" + names.stream().anyMatch(r -> r.budgetClass) +
                                ", safeSinkMasked=[]" +
                                ", usages=" + (d2 ? "[suppressed]" : usageSites(us)));
                List<IncompleteFact> facts = new ArrayList<>();
                for (IncompleteReason r : reasons) {
                    facts.add(new IncompleteFact(r, source.getEnclosingMethod(), seedBci(source)));
                }
                System.out.println((d2 ? "[sug-fwd-candidate-facts-raw] " : "[sug-fwd-candidate-facts] ") + source.getSourceLocation() +
                                " downstreamFacts=" + facts + " rtrackRefusals=" + names);
            }
        }
    }

    private static final java.util.Comparator<UsageFact> USAGE_FACT_ORDER = (a, b) -> {
        String ka = a.usageSite() != null && a.usageSite().getSourceLocation() != null
                        ? a.usageSite().getSourceLocation()
                        : "null";
        String kb = b.usageSite() != null && b.usageSite().getSourceLocation() != null
                        ? b.usageSite().getSourceLocation()
                        : "null";
        int c = ka.compareTo(kb);
        if (c != 0) {
            return c;
        }
        String ma = a.usageSite() != null && a.usageSite().getMethodName() != null
                        ? a.usageSite().getMethodName()
                        : "null";
        String mb = b.usageSite() != null && b.usageSite().getMethodName() != null
                        ? b.usageSite().getMethodName()
                        : "null";
        c = ma.compareTo(mb);
        if (c != 0) {
            return c;
        }
        c = a.role().toString().compareTo(b.role().toString());
        if (c != 0) {
            return c;
        }
        c = Integer.compare(a.argumentIndex(), b.argumentIndex());
        if (c != 0) {
            return c;
        }
        return String.valueOf(a.dispatchOwner()).compareTo(String.valueOf(b.dispatchOwner()));
    };

    private static final class EmissionAggregate {
        final Set<UsageFact> usages = new HashSet<>();
        boolean incomplete;
        boolean resourceLimited;
        final Set<IncompleteReason> incompleteReasons = new LinkedHashSet<>();
        boolean wiredAnyLoad;
        /** Some atom of the vertex reads an object-return rule delivery (ID-DEP). */
        boolean idDep;
        /** Some string atom of the vertex had a heap-escape event ({@code RAtom.strStored}). */
        boolean stored;
        /** The refusal names of the roots (empty with the flag off). */
        final EnumSet<ContainerTables.RTrackRefusal> rtrackNames = EnumSet.noneOf(ContainerTables.RTrackRefusal.class);

        /**
         * The every-refusal-is-named rule's trigger: any refusal, the schedule-independent predicate (an object is refused
         * in one schedule iff in every schedule). The refusal name set of a refused candidate is schedule-dependent, so
         * "any budget-class name" cannot canonicalise. Returns {@link #D2_ALL_TOKEN}, or null when there is no refusal.
         */
        String d2Token() {
            return rtrackNames.isEmpty() ? null : D2_ALL_TOKEN;
        }
    }

    // ------------------------------------------------------------------
    // Production entry (called from SugBuilderV2.phaseBDownstreamSearch).
    // ------------------------------------------------------------------

    static void runAndEmit(StringUtilizationGraph sug,
                    Map<AnalysisMethod, LocalFlowGraph> localFlows,
                    Map<AnalysisMethod, Map<Integer, InvokeTypeFlow>> invokes,
                    LfgWalk lfgWalk) {
        ForwardFixpoint engine = new ForwardFixpoint(sug, localFlows, invokes, lfgWalk, null);
        engine.solve();
        engine.emit();
    }

    // ------------------------------------------------------------------
    // The pieces RTrackBridge delegates to.
    // ------------------------------------------------------------------

    Block siteBlockOf(LocalFlowGraph frame, LocalFlowGraph.LocalVertex site) {
        // Fast path: the memo check without recursion-guard allocation (the walk's hottest bridge call).
        Block memo = localBlockMemo.get(site);
        if (memo != null) {
            return memo;
        }
        return localBlock(frameMethod.get(frame), site, new HashSet<>());
    }

}
