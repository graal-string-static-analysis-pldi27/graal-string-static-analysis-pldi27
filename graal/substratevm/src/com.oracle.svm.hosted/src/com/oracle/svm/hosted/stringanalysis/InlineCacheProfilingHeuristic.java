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
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class InlineCacheProfilingHeuristic {

    /* The method set is StringIcMethods (descriptor-exact). */
    private static final java.util.concurrent.atomic.AtomicInteger UNKNOWN_DESCRIPTOR_SITES = new java.util.concurrent.atomic.AtomicInteger();
    private static final java.util.concurrent.atomic.AtomicInteger NOT_MEMBER_SITES = new java.util.concurrent.atomic.AtomicInteger();
    private static final Map<String, Integer> DECLINED_SHAPES = new java.util.TreeMap<>();

    private int inlineCacheCount;

    /** The one pairing computation; the dump writes its pairs (null when the concat group is off). */
    private LazyOperandPairing.Result lazyOperandPairing;

    private static final int TRANSITIVE_DEPTH_LIMIT = 6;

    /**
     * A receiver whose upstream walk was cut at {@link #TRANSITIVE_DEPTH_LIMIT} is not proven: its rep set may be
     * incomplete (a cut path, or a vertex first reached beyond the limit and skipped as visited on a shorter path). Such
     * an entry gets the variant {@link #UNPROVEN}. The parent reads it as no proof: an unknown rep name on the String path
     * (decline, stock virtual dispatch) and not rep-free for csfinal.
     */
    static final String UNPROVEN = "UNPROVEN";
    private static final java.util.concurrent.atomic.AtomicInteger UNPROVEN_ENTRIES = new java.util.concurrent.atomic.AtomicInteger();
    private static final java.util.concurrent.atomic.AtomicInteger UNPROVEN_WOULD_BE_REPFREE = new java.util.concurrent.atomic.AtomicInteger();

    /** The variant of a receiver: UNKNOWN, EXACT_STRING, a rep list, or UNPROVEN for a truncated walk (pure; JUnit-pinned). */
    static String receiverVariant(boolean anyReceiverRecord, boolean truncated, Set<String> exactReps, Set<String> customReps) {
        if (truncated) {
            return UNPROVEN;
        }
        if (!anyReceiverRecord) {
            return "UNKNOWN";
        }
        if (customReps.isEmpty()) {
            return "EXACT_STRING";
        }
        return (exactReps.isEmpty() ? "" : "EXACT,") + String.join(",", customReps);
    }

    private static final class RepResult {
        final Set<String> exact;
        final Set<String> custom;
        boolean truncated;

        RepResult(Set<String> exact, Set<String> custom) {
            this.exact = exact.isEmpty() ? Collections.emptySet() : Collections.unmodifiableSet(new LinkedHashSet<>(exact));
            this.custom = custom.isEmpty() ? Collections.emptySet() : Collections.unmodifiableSet(new LinkedHashSet<>(custom));
        }
    }

    /* Type-check IC: this run's IC receiver inputs (rep rule, root cache, KT kind facts), kept for TypeCheckSites. */
    private Map<SugVertex, InstrumentationDecision> tcDecisionByCandidate = Map.of();
    private Map<SugVertex, RepResult> tcRootCache = new HashMap<>();
    private Set<String> tcAdmittedKinds = Set.of();
    private Set<String> tcConcatOperandKinds = Set.of();

    /** Type-check IC: the IC receiver facts of a set of creation sites (any = non-empty; the rep names; a depth cut). */
    record RepFacts(boolean any, boolean truncated, Set<String> exact, Set<String> custom) {
    }

    /** Type-check IC: {@link #collectRepFromCreationSite} over {@code creationSites}, root-cached as in {@link #apply}. */
    RepFacts repFactsOf(StringUtilizationGraph sug, java.util.Collection<SugVertex> creationSites) {
        Set<String> exact = new LinkedHashSet<>();
        Set<String> custom = new LinkedHashSet<>();
        boolean truncated = false;
        for (SugVertex cs : creationSites) {
            RepResult rr = tcRootCache.get(cs);
            if (rr == null) {
                Set<String> e = new LinkedHashSet<>();
                Set<String> c = new LinkedHashSet<>();
                boolean[] cut = new boolean[1];
                collectRepFromCreationSite(sug, cs, tcDecisionByCandidate, e, c, new HashSet<>(), 0, cut);
                rr = new RepResult(e, c);
                rr.truncated = cut[0];
                tcRootCache.put(cs, rr);
            }
            exact.addAll(rr.exact);
            custom.addAll(rr.custom);
            truncated |= rr.truncated;
        }
        return new RepFacts(!creationSites.isEmpty(), truncated, exact, custom);
    }

    /** Type-check IC: the KT kind set of a terminal-body key (null: not a terminal body). */
    Set<String> ktKindSet(String key) {
        return TerminalBodyKinds.kindSet(key, tcAdmittedKinds, tcConcatOperandKinds);
    }

    /** The listing and pairs this run's concat group was built from (null: kind-terminal off, no concat group). */
    LazyOperandPairing.Result getLazyOperandPairing() {
        return lazyOperandPairing;
    }

    List<InstrumentationDecision> apply(StringUtilizationGraph sug, List<InstrumentationDecision> validated) {
        long start = System.nanoTime();
        inlineCacheCount = 0;
        lazyOperandPairing = null;
        UNKNOWN_DESCRIPTOR_SITES.set(0);
        UNPROVEN_ENTRIES.set(0);
        UNPROVEN_WOULD_BE_REPFREE.set(0);
        NOT_MEMBER_SITES.set(0);
        DECLINED_SHAPES.clear();
        Map<SugVertex, InstrumentationDecision> decisionByCandidate = new HashMap<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.EQUALS_MATRIX || d.getType() == OptimizationType.INLINE_CACHE) {
                continue;
            }
            decisionByCandidate.put(d.getCandidate(), d);
        }
        Map<SugVertex, RepResult> rootCache = new HashMap<>();
        this.tcDecisionByCandidate = decisionByCandidate;
        this.tcRootCache = rootCache;
        List<InstrumentationDecision> decisions = new ArrayList<>();
        /*
         * Kind-level terminal-body entries (TerminalBodyKinds): the admitted rep kinds and whether an admitted SV is a
         * non-copying concat operand, as the orchestrator's nested-concat pass reads them.
         */
        Set<String> admittedKinds = new java.util.TreeSet<>();
        boolean svConcatOperand = false;
        Set<String> concatOperandKinds = new java.util.TreeSet<>();
        /*
         * The kinds come from every typed decision, not from decisionByCandidate (a second typed decision of one
         * candidate would drop a kind); "one typed decision per candidate" is counted below (multi=0 expected).
         */
        Map<SugVertex, Integer> typedPerCandidate = new HashMap<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.EQUALS_MATRIX || d.getType() == OptimizationType.INLINE_CACHE) {
                continue;
            }
            typedPerCandidate.merge(d.getCandidate(), 1, Integer::sum);
            String rep = HeuristicOrchestrator.repTypeOf(d);
            if (rep != null) {
                admittedKinds.add(rep);
            }
        }
        long multi = typedPerCandidate.values().stream().filter(n -> n > 1).count();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.STRING_VIEW && !svConcatOperand &&
                            !StringViewHeuristic.concatOperandSites(sug, d.getCandidate()).isEmpty()) {
                svConcatOperand = true;
            }
        }
        if (svConcatOperand) {
            concatOperandKinds.add("SV");
        }
        // Nested concat: a lazy rep admitted as a non-copying concat operand reaches the concat group;
        // KT precision: only through an outer that stays stock (LazyOperandPairing: the rule, the pairs, the revert)
        LazyOperandPairing.Result pairing = LazyOperandPairing.compute(validated);
        lazyOperandPairing = pairing;
        concatOperandKinds.addAll(pairing.listedKinds());
        System.out.println("[string-analysis] kind-terminal: lazy-operand pairing " + pairing.mode() + " listed " + pairing.listedKinds() +
                        " paired-only " + pairing.pairedOnlyKinds() + " paired inners " + pairing.pairs().size() + " pair lines " +
                        LazyOperandPairing.profileLines(pairing).size());
        if (!concatOperandKinds.equals(svConcatOperand ? Set.of("SV") : Set.of())) {
            System.out.println("[string-analysis] kind-terminal: concat-operand kinds " + concatOperandKinds);
        }
        System.out.println("[string-analysis] kind-terminal: admitted kinds " + admittedKinds + " svConcatOperand=" + svConcatOperand +
                        (multi == 0 ? "" : " WARNING multi-decision candidates=" + multi));
        this.tcAdmittedKinds = admittedKinds;
        this.tcConcatOperandKinds = concatOperandKinds;
        int ktEntries = 0;
        int ktWithReps = 0;
        for (SugVertex c : sug.getVertices()) {
            if (!isTrivialMethodCallSite(c)) {
                continue;
            }
            Set<String> exactReps = new LinkedHashSet<>();
            Set<String> customReps = new LinkedHashSet<>();
            boolean anyReceiverRecord = false;
            boolean truncated = false;
            BitSet recvTags = c.getSourceTags();
            for (int i = recvTags.nextSetBit(0); i >= 0; i = recvTags.nextSetBit(i + 1)) {
                SourceTag tag = sug.getSourceTag(i);
                if (tag.role() != UsageRole.RECEIVER) {
                    continue;
                }
                anyReceiverRecord = true;
                SugVertex creationSite = tag.creationSite();
                RepResult cached = rootCache.get(creationSite);
                if (cached != null) {
                    exactReps.addAll(cached.exact);
                    customReps.addAll(cached.custom);
                    truncated |= cached.truncated;
                    continue;
                }
                Set<String> rootExact = new LinkedHashSet<>();
                Set<String> rootCustom = new LinkedHashSet<>();
                boolean[] cut = new boolean[1];
                collectRepFromCreationSite(sug, creationSite, decisionByCandidate, rootExact, rootCustom, new HashSet<>(), 0, cut);
                RepResult rr = new RepResult(rootExact, rootCustom);
                rr.truncated = cut[0];
                truncated |= cut[0];
                rootCache.put(creationSite, rr);
                exactReps.addAll(rootExact);
                customReps.addAll(rootCustom);
            }
            String variant = receiverVariant(anyReceiverRecord, truncated, exactReps, customReps);
            if (UNPROVEN.equals(variant)) {
                UNPROVEN_ENTRIES.incrementAndGet();
                if (customReps.isEmpty()) {
                    UNPROVEN_WOULD_BE_REPFREE.incrementAndGet();
                }
            }
            if (c.getSourceLocation() != null) {
                Set<String> kinds = TerminalBodyKinds.kindSet(c.getSourceLocation(), admittedKinds, concatOperandKinds);
                if (kinds != null) {
                    variant = TerminalBodyKinds.markedVariant(variant, customReps, kinds);
                    ktEntries++;
                    if (!kinds.isEmpty() || !customReps.isEmpty()) {
                        ktWithReps++;
                    }
                }
            }
            decisions.add(new InstrumentationDecision(c, OptimizationType.INLINE_CACHE, variant));
            inlineCacheCount++;
        }
        System.out.println("[string-analysis] kind-terminal: marked entries " + ktEntries + " (with reps " + ktWithReps + ")");
        System.out.println("[string-analysis] ic-widen: members=" + StringIcMethods.descriptors().size() +
                        " entries=" + inlineCacheCount + " String-decl call vertices declined: unknown-descriptor=" + UNKNOWN_DESCRIPTOR_SITES.get() +
                        " not-member=" + NOT_MEMBER_SITES.get() + " unproven(depth-cut)=" + UNPROVEN_ENTRIES.get() + " (would-be rep-free " + UNPROVEN_WOULD_BE_REPFREE.get() + ")");
        DECLINED_SHAPES.forEach((k, n) -> System.out.println("[ic-widen-child] " + k + " x" + n));
        System.out.println("[string-analysis-timing] InlineCacheProfilingHeuristic.apply done: " + ((System.nanoTime() - start) / 1_000_000) + "ms (vertices=" + sug.getVertices().size() +
                        ", entries=" + inlineCacheCount + ", cachedRoots=" + rootCache.size() + ")");
        return decisions;
    }

    int getInlineCacheCount() {
        return inlineCacheCount;
    }

    private static boolean isTrivialMethodCallSite(SugVertex v) {
        SugNodeType t = v.getNodeType();
        if (t != SugNodeType.STRING_METHOD_CALL && t != SugNodeType.JDK_LIBRARY_CALL) {
            return false;
        }
        String name = v.getMethodName();
        if (name == null) {
            return false;
        }
        /*
         * A String-declared call vertex whose (name, parameter signature) is in the shared set, descriptor-exact. The
         * vertex's declaring class is the resolved target's (vertices the builder labels String keep their entries: the
         * parent fires only at String-declared invokes).
         */
        if (!InlineCacheTrivialMethodNodePlugin.STRING_CLASS.equals(v.getDeclaringClass())) {
            return false;
        }
        if (StringIcMethods.isMemberSite(name, v.getMethodSignature())) {
            return true;
        }
        if (StringIcMethods.isMemberName(name)) {
            UNKNOWN_DESCRIPTOR_SITES.incrementAndGet();
            DECLINED_SHAPES.merge("unknown-descriptor " + name + "|" + v.getMethodSignature() + " " + v.getLabel(), 1, Integer::sum);
        } else {
            NOT_MEMBER_SITES.incrementAndGet();
            DECLINED_SHAPES.merge("not-member " + name + "|" + v.getMethodSignature() + " " + v.getLabel(), 1, Integer::sum);
        }
        return false;
    }

    private static void collectRepFromCreationSite(StringUtilizationGraph graph, SugVertex creationSite,
                    Map<SugVertex, InstrumentationDecision> decisionByCandidate,
                    Set<String> exactReps, Set<String> customReps, Set<SugVertex> visited, int depth, boolean[] truncated) {
        if (creationSite == null || !visited.add(creationSite)) {
            return;
        }
        if (depth > TRANSITIVE_DEPTH_LIMIT) {
            truncated[0] = true;
            return;
        }
        InstrumentationDecision d = decisionByCandidate.get(creationSite);
        if (d != null) {
            String rep = HeuristicOrchestrator.repTypeOf(d);
            if (rep == null) {
                exactReps.add("EXACT");
            } else {
                customReps.add(rep);
            }
            return;
        }
        SugNodeType t = creationSite.getNodeType();
        boolean isIntermediate = t == SugNodeType.STRING_METHOD_CALL || t == SugNodeType.JDK_LIBRARY_CALL;
        if (!isIntermediate) {
            exactReps.add("EXACT");
            return;
        }
        boolean hasUpstreamReceiver = false;
        BitSet upstreamTags = creationSite.getSourceTags();
        for (int i = upstreamTags.nextSetBit(0); i >= 0; i = upstreamTags.nextSetBit(i + 1)) {
            SourceTag tag = graph.getSourceTag(i);
            if (tag.role() != UsageRole.RECEIVER) {
                continue;
            }
            hasUpstreamReceiver = true;
            collectRepFromCreationSite(graph, tag.creationSite(), decisionByCandidate, exactReps, customReps, visited, depth + 1, truncated);
        }
        if (!hasUpstreamReceiver) {
            exactReps.add("EXACT");
        }
    }
}