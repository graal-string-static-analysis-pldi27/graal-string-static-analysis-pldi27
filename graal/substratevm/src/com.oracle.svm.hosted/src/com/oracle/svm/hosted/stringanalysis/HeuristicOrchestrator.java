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
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class HeuristicOrchestrator {

    private final StringUtilizationGraph graph;
    private final List<InstrumentationDecision> validated = new ArrayList<>();
    private final List<String> conflicts = new ArrayList<>();
    private final List<InstrumentationDecision> precedenceSuppressed = new ArrayList<>();
    private final List<InstrumentationDecision> conflictSuppressed = new ArrayList<>();
    /** The decisions the cross-rep equals conflict pass reverted (each has its REJECT line). */
    private final Set<InstrumentationDecision> crossRepEqualsReverted = new LinkedHashSet<>();

    private int rawCount;
    /** Census: ID-DEP decisions dropped by the ID-DEP precedence (a conflict with a non-ID-DEP one). */
    private int idDepDropped;
    /** The {@code lc.lazyoperand} mode {@link #run} applies (default 2); mutable only so a JUnit test can pin another. */
    int lazyOperandMode = LazyConcatHeuristic.LAZY_OPERAND_MODE;

    public HeuristicOrchestrator(StringUtilizationGraph graph) {
        this.graph = graph;
    }

    public void run(List<InstrumentationDecision> singleByte,
                    List<InstrumentationDecision> stringView,
                    List<InstrumentationDecision> lazyConcat,
                    List<InstrumentationDecision> accumulator,
                    List<InstrumentationDecision> equalsMatrix) {
        long runStart = System.nanoTime();
        List<InstrumentationDecision> all = new ArrayList<>();
        all.addAll(singleByte);
        all.addAll(stringView);
        all.addAll(lazyConcat);
        all.addAll(accumulator);
        rawCount = all.size() + equalsMatrix.size();

        long t0 = System.nanoTime();
        List<InstrumentationDecision> afterPrecedence = applyPrecedence(all);
        System.out.println("[string-analysis-timing]   orchestrator applyPrecedence done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (in=" + all.size() + ", out=" + afterPrecedence.size() +
                        ")");

        t0 = System.nanoTime();
        List<InstrumentationDecision> afterNestedConcat = applyNestedLsRule(runNestedConcatConflictPass(afterPrecedence), lazyOperandMode);
        System.out.println("[string-analysis-timing]   orchestrator runNestedConcatConflictPass done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (in=" + afterPrecedence.size() + ", out=" +
                        afterNestedConcat.size() + ")");

        t0 = System.nanoTime();
        runValidationPass(afterNestedConcat);
        System.out.println("[string-analysis-timing]   orchestrator runValidationPass done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (in=" + afterNestedConcat.size() + ", validated=" +
                        validated.size() + ")");
        validated.addAll(equalsMatrix);

        t0 = System.nanoTime();
        runCrossRepConflictPass();
        System.out.println("[string-analysis-timing]   orchestrator runCrossRepConflictPass done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (validated=" + validated.size() + ")");
        validated.sort(Comparator.comparingInt(d -> d.getCandidate().getId()));
        System.out.println("[string-analysis-timing]   orchestrator run total: " + ((System.nanoTime() - runStart) / 1_000_000) + "ms");
    }

    public void runSecondPhase(List<InstrumentationDecision> equalsMatrix) {
        long runStart = System.nanoTime();
        rawCount += equalsMatrix.size();
        validated.addAll(equalsMatrix);

        long t0 = System.nanoTime();
        runCrossRepConflictPass();
        System.out.println("[string-analysis-timing]   orchestrator runCrossRepConflictPass done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (validated=" + validated.size() + ")");
        validated.sort(Comparator.comparingInt(d -> d.getCandidate().getId()));
        if (RecursiveTracking.OBJRET_DELIVER) {
            // ID-DEP precedence census (objret=1 only: the objret=0 output is unchanged)
            long admits = validated.stream().filter(d -> d.getCandidate().isIdDep()).count();
            System.out.println("[objret-iddep] idDep{tables=" + ContainerTables.ID_DEP_TABLES.sum() + " sinks=" + ContainerTables.ID_DEP_SINKS.sum() + " untargeted=" +
                            ContainerTables.ID_DEP_UNTARGETED.sum() + new java.util.TreeMap<>(ContainerTables.ID_DEP_UNTARGETED_BY) + " admitsWithIdDep=" + admits + " dropped=" + idDepDropped + "}");
        }
        System.out.println("[string-analysis-timing]   orchestrator runSecondPhase total: " + ((System.nanoTime() - runStart) / 1_000_000) + "ms");
    }

    public List<InstrumentationDecision> getValidatedDecisions() {
        return Collections.unmodifiableList(validated);
    }

    public List<String> getConflicts() {
        return Collections.unmodifiableList(conflicts);
    }

    public List<InstrumentationDecision> getPrecedenceSuppressed() {
        return Collections.unmodifiableList(precedenceSuppressed);
    }

    /** The reverted decisions; the accepted counters, REJECT lines and profile all exclude them (they agree). */
    public Set<InstrumentationDecision> getCrossRepEqualsReverted() {
        return Collections.unmodifiableSet(crossRepEqualsReverted);
    }

    public List<InstrumentationDecision> getConflictSuppressed() {
        return Collections.unmodifiableList(conflictSuppressed);
    }

    public int getRawCount() {
        return rawCount;
    }

    public Map<OptimizationType, Long> validatedCountsByType() {
        Map<OptimizationType, Long> counts = new HashMap<>();
        for (InstrumentationDecision d : validated) {
            counts.merge(d.getType(), 1L, Long::sum);
        }
        return counts;
    }

    private List<InstrumentationDecision> applyPrecedence(List<InstrumentationDecision> all) {
        Map<SugVertex, InstrumentationDecision> best = new HashMap<>();
        for (InstrumentationDecision d : all) {
            SugVertex v = d.getCandidate();
            InstrumentationDecision existing = best.get(v);
            if (existing == null || priority(d.getType()) < priority(existing.getType())) {
                if (existing != null) {
                    precedenceSuppressed.add(existing);
                }
                best.put(v, d);
            } else {
                precedenceSuppressed.add(d);
            }
        }
        return new ArrayList<>(best.values());
    }

    private static int priority(OptimizationType t) {
        return switch (t) {
            case SINGLE_BYTE -> 1;
            case STRING_VIEW -> 2;
            case LAZY_CONCAT -> 3;
            case EQUALS_MATRIX -> Integer.MAX_VALUE - 1;
            case INLINE_CACHE -> Integer.MAX_VALUE - 2;
            case NONE -> Integer.MAX_VALUE;
        };
    }

    private List<InstrumentationDecision> runNestedConcatConflictPass(List<InstrumentationDecision> candidates) {
        Map<String, InstrumentationDecision> decisionBySourceLocation = new LinkedHashMap<>();
        for (InstrumentationDecision d : candidates) {
            String loc = d.getCandidate().getSourceLocation();
            if (loc != null) {
                decisionBySourceLocation.putIfAbsent(loc, d);
            }
        }
        // The concat sites a String View decision is an admitted (non-copying) operand of, through any flow, with the
        // reaching String View decisions per site (for the ID-DEP precedence)
        Map<String, List<InstrumentationDecision>> svOperandSites = new LinkedHashMap<>();
        for (InstrumentationDecision d : candidates) {
            if (d.getType() == OptimizationType.STRING_VIEW) {
                for (String site : StringViewHeuristic.concatOperandSites(graph, d.getCandidate())) {
                    svOperandSites.computeIfAbsent(site, k -> new ArrayList<>()).add(d);
                }
                // The copying sites too (the parent lowers them with RepConcat; an LC lowering there would
                // hold the view as a rope child): the same DROP_SITE / ID-DEP precedence
                for (String site : StringViewHeuristic.copyingConcatSites(graph, d.getCandidate()).keySet()) {
                    svOperandSites.computeIfAbsent(site, k -> new ArrayList<>()).add(d);
                }
            }
        }
        Set<InstrumentationDecision> disabled = new LinkedHashSet<>();
        for (InstrumentationDecision d : candidates) {
            if (d.getType() != OptimizationType.LAZY_CONCAT) {
                continue;
            }
            List<InstrumentationDecision> svReach = svOperandSites.getOrDefault(d.getCandidate().getSourceLocation(), List.of()).stream().filter(x -> !disabled.contains(x)).toList();
            SvReachOutcome svo = svReachOutcome(d.getCandidate().isIdDep(), disabled.contains(d), svReach.stream().map(x -> x.getCandidate().isIdDep()).toList());
            if (svo == SvReachOutcome.DROP_ID_DEP_SVS) {
                // ID-DEP precedence: only ID-DEP String View admits reach this non-ID-DEP LS site: they are dropped,
                // the site stays
                for (InstrumentationDecision x : svReach) {
                    disabled.add(x);
                    idDepDropped++;
                    conflicts.add("NESTED-CONCAT-CONFLICT: disabled SV V" + x.getCandidate().getId() + " @ " + x.getCandidate().getSourceLocation() + " (ID-DEP, reaches the non-ID-DEP LS site V" +
                                    d.getCandidate().getId() + ")");
                }
            } else if (svo == SvReachOutcome.DROP_SITE) {
                disabled.add(d);
                conflicts.add("NESTED-CONCAT-CONFLICT: disabled LS site V" + d.getCandidate().getId() + " @ " + d.getCandidate().getSourceLocation() +
                                " (a String View operand reaches it)");
                continue;
            }
            if (disabled.contains(d)) {
                continue;
            }
            SugVertex v = d.getCandidate();
            List<String> opLocs = v.getOperandSourceLocations();
            if (opLocs == null || opLocs.isEmpty()) {
                continue;
            }
            boolean hasNonLSCustomRep = false;
            List<InstrumentationDecision> customOps = new ArrayList<>();
            Set<InstrumentationDecision> innerLS = new LinkedHashSet<>();
            for (String opLoc : opLocs) {
                if (opLoc == null) {
                    continue;
                }
                InstrumentationDecision opDec = decisionBySourceLocation.get(opLoc);
                if (opDec == null || opDec == d) {
                    continue;
                }
                OptimizationType opType = opDec.getType();
                if ((opType == OptimizationType.SINGLE_BYTE || opType == OptimizationType.STRING_VIEW) && !disabled.contains(opDec)) {
                    hasNonLSCustomRep = true;
                    customOps.add(opDec);
                } else if (opType == OptimizationType.SINGLE_BYTE || opType == OptimizationType.STRING_VIEW) {
                    // An operand dropped by the ID-DEP precedence no longer counts (never at objret=0: only LS decisions
                    // are disabled before this point there)
                    continue;
                } else if (opType == OptimizationType.LAZY_CONCAT && !disabled.contains(opDec)) {
                    if (opDec.getCandidate().getLazyOperandSites().contains(v.getSourceLocation())) {
                        // Nested concat: the inner rep was admitted as an operand of this site
                        // (LazyConcatHeuristic.isLazyOperandOk): sound under the outer's lazy and stock lowerings
                        continue;
                    }
                    innerLS.add(opDec);
                }
            }
            OperandOutcome oo = operandOutcome(v.isIdDep(), customOps.stream().map(x -> x.getCandidate().isIdDep()).toList(), innerLS.stream().map(x -> x.getCandidate().isIdDep()).toList());
            if (oo == OperandOutcome.DROP_ID_DEP_OPERANDS || oo == OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER) {
                // ID-DEP precedence: only ID-DEP SB/SV operands disable this non-ID-DEP LS site: they are dropped
                // instead (and with DROP_ID_DEP_OPERANDS_AND_INNER the inner rule below then applies too)
                for (InstrumentationDecision x : customOps) {
                    disabled.add(x);
                    idDepDropped++;
                    conflicts.add("NESTED-CONCAT-CONFLICT: disabled operand V" + x.getCandidate().getId() + " @ " + x.getCandidate().getSourceLocation() +
                                    " (ID-DEP, operand of the non-ID-DEP LS site V" +
                                    v.getId() + ")");
                }
            }
            if (oo == OperandOutcome.DROP_ID_DEP_OUTER) {
                // ID-DEP precedence: this ID-DEP outer LS site would disable a non-ID-DEP inner one: the outer is
                // dropped instead
                disabled.add(d);
                idDepDropped++;
                conflicts.add("NESTED-CONCAT-CONFLICT: disabled LS site V" + v.getId() + " @ " + v.getSourceLocation() + " (ID-DEP, would disable a non-ID-DEP inner LS)");
            } else if (oo == OperandOutcome.DROP_OUTER) {
                disabled.add(d);
                conflicts.add("NESTED-CONCAT-CONFLICT: disabled LS site V" + v.getId() + " @ " + v.getSourceLocation() +
                                " (operand has higher-priority custom rep SBS/SV)");
            } else if (oo == OperandOutcome.DROP_INNER || oo == OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER) {
                disabled.addAll(innerLS);
                for (InstrumentationDecision inner : innerLS) {
                    conflicts.add("NESTED-CONCAT-CONFLICT: disabled LS arg V" + inner.getCandidate().getId() + " @ " +
                                    inner.getCandidate().getSourceLocation() + " (nested inside LS site V" + v.getId() + " @ " + v.getSourceLocation() + ")");
                }
            }
        }
        if (disabled.isEmpty()) {
            return candidates;
        }
        List<InstrumentationDecision> kept = new ArrayList<>();
        for (InstrumentationDecision d : candidates) {
            if (disabled.contains(d)) {
                conflictSuppressed.add(d);
            } else {
                kept.add(d);
            }
        }
        return kept;
    }

    /**
     * Under {@code lc.lazyoperand} 2 or 3 no LS value may be an operand of another LS site. Runs on the decisions the
     * nested-concat pass kept; each refusal is a NESTED-CONCAT-CONFLICT line naming {@link LazyConcatHeuristic#LS_NESTED_INNER}
     * / {@link LazyConcatHeuristic#LS_NESTED_OUTER} and goes to {@link #getConflictSuppressed}. Modes 0 and 1: identity.
     * <p>
     * The rule runs before the receiver cap and the cross-rep pass, so a decision may be refused because of a partner a
     * later pass drops. That is sound (later passes only remove decisions, so they never bring back an LS-in-LS edge) but
     * loses that LS.
     */
    List<InstrumentationDecision> applyNestedLsRule(List<InstrumentationDecision> kept, int mode) {
        Map<InstrumentationDecision, String> refused = nestedLsRefusals(kept, mode);
        if (mode == 2 || mode == 3) {
            System.out.println("[string-analysis] nested-ls: lazyoperand=" + mode + " refused " + refused.size() + " (" + (mode == 2 ? LazyConcatHeuristic.LS_NESTED_INNER
                            : LazyConcatHeuristic.LS_NESTED_OUTER) + ")");
        }
        if (refused.isEmpty()) {
            return kept;
        }
        List<InstrumentationDecision> out = new ArrayList<>();
        for (InstrumentationDecision d : kept) {
            String why = refused.get(d);
            if (why == null) {
                out.add(d);
            } else {
                conflictSuppressed.add(d);
                conflicts.add("NESTED-CONCAT-CONFLICT: disabled LS " + (mode == 2 ? "arg" : "site") + " V" + d.getCandidate().getId() + " @ " + d.getCandidate().getSourceLocation() + ": " + why);
            }
        }
        return out;
    }

    /**
     * Pure (JUnit): the LS decisions {@code lc.lazyoperand} {@code mode} refuses among {@code kept}, with their reason. The
     * graph is over site keys ({@code class#method@bci}; the parent lowers per key, and two SUG vertices may share a key):
     * an edge inner -> outer exists when any LAZY_CONCAT decision with a rep ({@link #repTypeOf}) at the inner key recorded
     * the outer key as a lazy-operand site and any LAZY_CONCAT decision at the outer key is lowered lazily
     * ({@link LazyOperandPairing#isKeptLazyOuter}); an edge to a stock outer is no nesting. A refused key refuses every
     * LAZY_CONCAT decision at it (so no sibling keeps the key lazy in the profile).
     * <ul>
     * <li>A key on a cycle (e.g. {@code s = s + "," + x}) is always refused: it is its own (transitive) operand.</li>
     * <li>mode 2 (INNER), outermost first: an inner key is refused when one of its outer keys is kept.</li>
     * <li>mode 3 (OUTER), innermost first: an outer key is refused when one of its inner keys is kept.</li>
     * </ul>
     * So the kept set has no LS-in-LS edge (in a chain A in B in C both modes refuse only B). Deterministic: the result
     * depends only on the key graph; the reason names the smallest kept partner key. Modes 0 and 1: empty.
     */
    static Map<InstrumentationDecision, String> nestedLsRefusals(List<InstrumentationDecision> kept, int mode) {
        Map<InstrumentationDecision, String> refused = new LinkedHashMap<>();
        if (mode != 2 && mode != 3) {
            return refused;
        }
        String name = mode == 2 ? LazyConcatHeuristic.LS_NESTED_INNER : LazyConcatHeuristic.LS_NESTED_OUTER;
        Map<String, List<InstrumentationDecision>> lcByKey = new java.util.TreeMap<>();
        for (InstrumentationDecision d : kept) {
            if (d.getType() == OptimizationType.LAZY_CONCAT && d.getSourceLocation() != null) {
                lcByKey.computeIfAbsent(d.getSourceLocation(), k -> new ArrayList<>()).add(d);
            }
        }
        Set<String> lazyOuterKeys = new HashSet<>();
        for (Map.Entry<String, List<InstrumentationDecision>> e : lcByKey.entrySet()) {
            if (e.getValue().stream().anyMatch(LazyOperandPairing::isKeptLazyOuter)) {
                lazyOuterKeys.add(e.getKey());
            }
        }
        Map<String, java.util.TreeSet<String>> outersOf = new java.util.TreeMap<>();
        Map<String, java.util.TreeSet<String>> innersOf = new java.util.TreeMap<>();
        for (Map.Entry<String, List<InstrumentationDecision>> e : lcByKey.entrySet()) {
            for (InstrumentationDecision d : e.getValue()) {
                if (d.getCandidate().getLazyOperandSites().isEmpty() || repTypeOf(d) == null) {
                    continue;
                }
                for (String site : d.getCandidate().getLazyOperandSites()) {
                    if (lazyOuterKeys.contains(site)) {
                        outersOf.computeIfAbsent(e.getKey(), k -> new java.util.TreeSet<>()).add(site);
                        innersOf.computeIfAbsent(site, k -> new java.util.TreeSet<>()).add(e.getKey());
                    }
                }
            }
        }
        if (outersOf.isEmpty()) {
            return refused;
        }
        Set<String> cyclic = cyclicKeys(outersOf);
        Map<String, String> why = new java.util.TreeMap<>();
        for (String k : cyclic) {
            why.put(k, name + " (on a lazy-operand cycle" + (outersOf.get(k).contains(k) ? ": self-loop" : "") + ")");
        }
        // the rest is a DAG: a key is refused iff some non-cyclic dependency (outers for INNER, inners for OUTER) is
        // kept; evaluated dependencies first with an explicit stack
        Map<String, java.util.TreeSet<String>> deps = mode == 2 ? outersOf : innersOf;
        Map<String, String> keptDep = new HashMap<>(); // decided key -> its smallest kept dependency ("" = none: kept)
        Set<String> all = new java.util.TreeSet<>(outersOf.keySet());
        all.addAll(innersOf.keySet());
        for (String root : all) {
            if (cyclic.contains(root) || keptDep.containsKey(root)) {
                continue;
            }
            java.util.ArrayDeque<String> stack = new java.util.ArrayDeque<>();
            stack.push(root);
            while (!stack.isEmpty()) {
                String x = stack.peek();
                if (keptDep.containsKey(x)) {
                    stack.pop();
                    continue;
                }
                boolean ready = true;
                for (String y : deps.getOrDefault(x, new java.util.TreeSet<>())) {
                    if (!cyclic.contains(y) && !keptDep.containsKey(y)) {
                        stack.push(y);
                        ready = false;
                    }
                }
                if (ready) {
                    String by = "";
                    for (String y : deps.getOrDefault(x, new java.util.TreeSet<>())) {
                        if (!cyclic.contains(y) && keptDep.get(y).isEmpty()) {
                            by = y;
                            break;
                        }
                    }
                    keptDep.put(x, by);
                    stack.pop();
                }
            }
        }
        for (String k : all) {
            String by = keptDep.get(k);
            if (by != null && !by.isEmpty()) {
                long id = lcByKey.get(by).stream().mapToLong(d -> d.getCandidate().getId()).min().getAsLong();
                why.put(k, name + (mode == 2 ? " (lazy operand of the LS site V" : " (has the LS operand V") + id + " @ " + by + ")");
            }
        }
        for (Map.Entry<String, String> e : why.entrySet()) {
            for (InstrumentationDecision d : lcByKey.get(e.getKey())) {
                refused.put(d, e.getValue());
            }
        }
        return refused;
    }

    /** The keys on a cycle of {@code succ} (a self-loop or an SCC of size > 1); iterative Tarjan, linear. */
    static Set<String> cyclicKeys(Map<String, java.util.TreeSet<String>> succ) {
        Set<String> cyclic = new HashSet<>();
        Map<String, Integer> index = new HashMap<>();
        Map<String, Integer> low = new HashMap<>();
        Set<String> onStack = new HashSet<>();
        java.util.ArrayDeque<String> sccStack = new java.util.ArrayDeque<>();
        java.util.ArrayDeque<String> callNode = new java.util.ArrayDeque<>();
        java.util.ArrayDeque<java.util.Iterator<String>> callIter = new java.util.ArrayDeque<>();
        int next = 0;
        for (String root : succ.keySet()) {
            if (index.containsKey(root)) {
                continue;
            }
            index.put(root, next);
            low.put(root, next++);
            sccStack.push(root);
            onStack.add(root);
            callNode.push(root);
            callIter.push(succ.get(root).iterator());
            while (!callNode.isEmpty()) {
                String v = callNode.peek();
                java.util.Iterator<String> it = callIter.peek();
                if (it.hasNext()) {
                    String w = it.next();
                    if (!index.containsKey(w)) {
                        index.put(w, next);
                        low.put(w, next++);
                        sccStack.push(w);
                        onStack.add(w);
                        callNode.push(w);
                        callIter.push(succ.getOrDefault(w, new java.util.TreeSet<>()).iterator());
                    } else if (onStack.contains(w)) {
                        low.put(v, Math.min(low.get(v), index.get(w)));
                    }
                    continue;
                }
                callNode.pop();
                callIter.pop();
                if (low.get(v).equals(index.get(v))) {
                    List<String> scc = new ArrayList<>();
                    String w;
                    do {
                        w = sccStack.pop();
                        onStack.remove(w);
                        scc.add(w);
                    } while (!w.equals(v));
                    if (scc.size() > 1 || succ.getOrDefault(v, new java.util.TreeSet<>()).contains(v)) {
                        cyclic.addAll(scc);
                    }
                }
                if (!callNode.isEmpty()) {
                    String u = callNode.peek();
                    low.put(u, Math.min(low.get(u), low.get(v)));
                }
            }
        }
        return cyclic;
    }

    /** The outcome of the String-View-reaches-an-LS-site rule of the nested-concat pass. */
    enum SvReachOutcome {
        /** No String View reaches the site (or the site is already disabled): nothing. */
        NONE,
        /** ID-DEP precedence: only ID-DEP String Views reach a non-ID-DEP LS site: the Views are dropped, the site stays. */
        DROP_ID_DEP_SVS,
        /** The base rule: the LS site is disabled. */
        DROP_SITE
    }

    /**
     * Pure (JUnit truth table): the nested-concat pass's decision at one LS site reached by the (still enabled) String
     * View decisions with ID-DEP flags {@code svIdDep}. Without any ID-DEP flag (always at objret=0) this is the base
     * rule: any reaching View disables the site.
     */
    static SvReachOutcome svReachOutcome(boolean siteIdDep, boolean siteDisabled, List<Boolean> svIdDep) {
        if (svIdDep.isEmpty()) {
            return SvReachOutcome.NONE;
        }
        if (!siteIdDep && !siteDisabled && svIdDep.stream().allMatch(b -> b)) {
            return SvReachOutcome.DROP_ID_DEP_SVS;
        }
        return SvReachOutcome.DROP_SITE;
    }

    /** The outcome of the operand rule of the nested-concat pass at one (still enabled) LS site. */
    enum OperandOutcome {
        /** No SB/SV operand and no conflicting inner LS: nothing. */
        NONE,
        /** ID-DEP precedence: only ID-DEP SB/SV operands would disable a non-ID-DEP outer: the operands are dropped. */
        DROP_ID_DEP_OPERANDS,
        /**
         * As {@link #DROP_ID_DEP_OPERANDS}, and the outer still conflicts with inner LS operands, which are disabled too
         * (the base inner rule), so the pass result stays conflict-free.
         */
        DROP_ID_DEP_OPERANDS_AND_INNER,
        /** ID-DEP precedence: an ID-DEP outer would disable a non-ID-DEP inner LS: the outer is dropped, the inners stay. */
        DROP_ID_DEP_OUTER,
        /** The base rule: an SB/SV operand disables the outer LS site. */
        DROP_OUTER,
        /** The base rule: the inner LS operands are disabled. */
        DROP_INNER
    }

    /**
     * Pure (JUnit truth table): the nested-concat pass's operand decision at one enabled LS site, given the ID-DEP flags
     * of its enabled SB/SV operand decisions and of the conflicting inner LS decisions. Without any ID-DEP flag (always at
     * objret=0) this is the base rule: an SB/SV operand disables the outer, else the inner LS operands are disabled.
     */
    static OperandOutcome operandOutcome(boolean outerIdDep, List<Boolean> customOpIdDep, List<Boolean> innerLsIdDep) {
        boolean custom = !customOpIdDep.isEmpty();
        if (custom && !outerIdDep && customOpIdDep.stream().allMatch(b -> b)) {
            return innerLsIdDep.isEmpty() ? OperandOutcome.DROP_ID_DEP_OPERANDS : OperandOutcome.DROP_ID_DEP_OPERANDS_AND_INNER;
        }
        if (!custom && !innerLsIdDep.isEmpty() && outerIdDep && innerLsIdDep.stream().anyMatch(b -> !b)) {
            return OperandOutcome.DROP_ID_DEP_OUTER;
        }
        if (custom) {
            return OperandOutcome.DROP_OUTER;
        }
        return innerLsIdDep.isEmpty() ? OperandOutcome.NONE : OperandOutcome.DROP_INNER;
    }

    /**
     * Pure (JUnit): the receiver-cap decision at one call site: decisions sorted non-ID-DEP first (stable; at objret=0
     * exactly {@link #crossRepPriority} order), the first {@code max} reps retained, every decision of another rep
     * disabled. So an ID-DEP admit never takes a retained rep a non-ID-DEP decision would have kept.
     */
    static Set<InstrumentationDecision> receiverCapDisabled(java.util.Collection<InstrumentationDecision> conflicting, int max, Set<String> retainedOut) {
        List<InstrumentationDecision> sorted = new ArrayList<>(conflicting);
        sorted.sort(Comparator.comparing((InstrumentationDecision d) -> d.getCandidate().isIdDep()).thenComparingInt(HeuristicOrchestrator::crossRepPriority));
        Set<InstrumentationDecision> toDisable = new LinkedHashSet<>();
        for (InstrumentationDecision d : sorted) {
            String rep = repTypeOf(d);
            if (rep == null) {
                continue;
            }
            if (retainedOut.size() < max) {
                retainedOut.add(rep);
            } else if (!retainedOut.contains(rep)) {
                toDisable.add(d);
            }
        }
        return toDisable;
    }

    /**
     * Receiver-rep cap: a call site reached by more than this many receiver reps disables the lower-priority decisions.
     * Knob {@code svm.stringanalysis.orch.maxreceiverreps} (default 5, the plugin's chain cap).
     */
    static final int MAX_RECEIVER_CUSTOM_REPS = Integer.getInteger("svm.stringanalysis.orch.maxreceiverreps", 5);

    private void runValidationPass(List<InstrumentationDecision> candidates) {
        long reachBudget = 0L;
        Map<SugVertex, Set<InstrumentationDecision>> reachingDecisions = new HashMap<>();
        int forwardCalls = candidates.size();
        long totalVisited = 0;
        long maxVisited = 0;

        boolean allCached = !candidates.isEmpty();
        Map<SugVertex, Set<SugVertex>> cache = null;
        if (allCached) {
            cache = graph.getReachabilityCache();
            for (InstrumentationDecision d : candidates) {
                if (!cache.containsKey(d.getCandidate())) {
                    allCached = false;
                    break;
                }
            }
        }

        long fb = System.nanoTime();
        if (allCached) {
            for (int i = 0; i < candidates.size(); i++) {
                InstrumentationDecision d = candidates.get(i);
                Set<SugVertex> reachable = cache.get(d.getCandidate());
                totalVisited += reachable.size();
                if (reachable.size() > maxVisited) {
                    maxVisited = reachable.size();
                }
                for (SugVertex v : reachable) {
                    reachingDecisions.computeIfAbsent(v, k -> new LinkedHashSet<>()).add(d);
                }
            }
        } else {
            List<SugVertex> seeds = new ArrayList<>(candidates.size());
            for (InstrumentationDecision d : candidates) {
                seeds.add(d.getCandidate());
            }
            Map<SugVertex, BitSet> reachingIndices = new HashMap<>();
            List<Set<SugVertex>> reachableByDecision = new ArrayList<>(candidates.size());
            for (int i = 0; i < candidates.size(); i++) {
                reachableByDecision.add(new HashSet<>());
            }
            graph.computeMultiSourceForwardReachability(seeds, reachingIndices, reachableByDecision);
            for (int i = 0; i < candidates.size(); i++) {
                int sz = reachableByDecision.get(i).size();
                totalVisited += sz;
                if (sz > maxVisited) {
                    maxVisited = sz;
                }
            }
            for (Map.Entry<SugVertex, BitSet> e : reachingIndices.entrySet()) {
                SugVertex v = e.getKey();
                BitSet bs = e.getValue();
                Set<InstrumentationDecision> decs = new LinkedHashSet<>();
                for (int i = bs.nextSetBit(0); i >= 0; i = bs.nextSetBit(i + 1)) {
                    decs.add(candidates.get(i));
                }
                reachingDecisions.put(v, decs);
            }
        }
        reachBudget = System.nanoTime() - fb;
        System.out.println("[string-analysis-timing]     runValidationPass reachability: " + (reachBudget / 1_000_000) + "ms (forwardReachable calls=" + forwardCalls + ", candidates=" + candidates
                        .size() + ", avgVisited=" + (forwardCalls == 0 ? 0 : totalVisited / forwardCalls) + ", maxVisited=" + maxVisited + ")");

        Set<InstrumentationDecision> disabled = new HashSet<>();
        Map<SugVertex, InstrumentationDecision> decisionByCandidate = new HashMap<>();
        for (InstrumentationDecision d : candidates) {
            decisionByCandidate.put(d.getCandidate(), d);
        }
        for (SugVertex v : graph.getCallSiteVertices()) {
            if (EqualsMatrixHeuristic.isEqualsVertex(v)) {
                continue;
            }
            Map<String, Set<InstrumentationDecision>> receiverReps = collectReceiverRepsAtVertex(v, decisionByCandidate, reachingDecisions);
            if (receiverReps.size() <= MAX_RECEIVER_CUSTOM_REPS) {
                continue;
            }
            Set<InstrumentationDecision> allConflicting = new LinkedHashSet<>();
            for (Set<InstrumentationDecision> ds : receiverReps.values()) {
                allConflicting.addAll(ds);
            }
            // Non-ID-DEP decisions first (stable; the identity at objret=0), so an ID-DEP admit never
            // takes a retained rep a non-ID-DEP decision would have kept (the pure receiverCapDisabled)
            Set<String> retainedReps = new LinkedHashSet<>();
            Set<InstrumentationDecision> toDisable = receiverCapDisabled(allConflicting, MAX_RECEIVER_CUSTOM_REPS, retainedReps);
            disabled.addAll(toDisable);
            if (idDepMixed(allConflicting)) {
                for (InstrumentationDecision d : toDisable) {
                    idDepDropped += d.getCandidate().isIdDep() ? 1 : 0;
                }
            }
            if (!toDisable.isEmpty()) {
                conflicts.add("CONFLICT at V" + v.getId() + " @ " + v.getSourceLocation() +
                                ": receiverReps=" + receiverReps.keySet() +
                                " (exceeds max " + MAX_RECEIVER_CUSTOM_REPS + ")" +
                                " retained=" + retainedReps +
                                " disabled=" + describeDecisions(toDisable));
            }
        }
        for (InstrumentationDecision d : candidates) {
            if (!disabled.contains(d)) {
                validated.add(d);
            } else {
                conflictSuppressed.add(d);
            }
        }
    }

    private Map<String, Set<InstrumentationDecision>> collectReceiverRepsAtVertex(SugVertex v,
                    Map<SugVertex, InstrumentationDecision> decisionByCandidate,
                    Map<SugVertex, Set<InstrumentationDecision>> reachingDecisions) {
        Map<String, Set<InstrumentationDecision>> receiverReps = new LinkedHashMap<>();
        boolean anyReceiverRecord = false;
        BitSet siteTags = v.getSourceTags();
        for (int i = siteTags.nextSetBit(0); i >= 0; i = siteTags.nextSetBit(i + 1)) {
            SourceTag tag = graph.getSourceTag(i);
            if (tag.role() != UsageRole.RECEIVER) {
                continue;
            }
            // Only a non-ID-DEP tag switches the counted set from the reachability fallback to the tags, so a delivery's
            // RECEIVER tag never changes the set the non-ID-DEP decisions are capped against (the objret=0 pass)
            if (!tag.creationSite().isIdDep()) {
                anyReceiverRecord = true;
            }
            InstrumentationDecision d = decisionByCandidate.get(tag.creationSite());
            if (d == null) {
                continue;
            }
            String rep = repTypeOf(d);
            if (rep == null) {
                continue;
            }
            receiverReps.computeIfAbsent(rep, k -> new LinkedHashSet<>()).add(d);
        }
        if (!anyReceiverRecord) {
            // the fallback keeps the ID-DEP tagged decisions collected above (empty at objret=0) and adds the reaching ones
            Set<InstrumentationDecision> connecting = reachingDecisions.get(v);
            if (connecting != null) {
                for (InstrumentationDecision d : connecting) {
                    String rep = repTypeOf(d);
                    if (rep == null) {
                        continue;
                    }
                    receiverReps.computeIfAbsent(rep, k -> new LinkedHashSet<>()).add(d);
                }
            }
        }
        return receiverReps;
    }

    /**
     * The cross-rep equals conflict pass (SB on either side is no conflict, {@link #isCrossRepEqualsConflict}), on the
     * equals sites' source tags alone (SUG reachability never holds the receiver-side decision). At an
     * {@code equals(Object)} vertex, an admitted rep tagged RECEIVER and an admitted rep of a different class tagged PARAMETER at slot 1 conflict ({@link #isCrossRepEqualsConflict}); the highest-priority
     * involved decision keeps its rep, every involved decision of another rep is reverted with a REJECT line. Sites run in
     * source-location order; a reverted decision no longer counts. A JDK-internal site is one vertex for the whole image,
     * so reps that never meet at run time can conflict there (a sound precision limit).
     * <p>
     * The pass also runs at every String-declared {@code compareTo(String)} vertex ({@link EqualsMatrixHeuristic#isCompareToStringCall}) with the
     * equals rule on its RECEIVER and slot-1 PARAMETER tags (same image-wide-vertex precision limit). It guards no run-time
     * behaviour (every rep's {@code compareTo} is content-exact for every argument); it is a design guarantee.
     * <p>
     * The SB exemption applies here too: an SB x rep {@code compareTo} is correct through the
     * {@code maybeCustomStringCompareTo} discipline: an SB receiver inherits {@code String.maybeCustomStringCompareTo},
     * which deflects a rep argument to {@code -rep.compareTo(sb)}; a value-null rep receiver runs its own {@code compareTo}
     * (IC arm) or {@code maybeCustomStringCompareTo} override (virtual residual), both reading the SB argument by
     * {@code length()/charAt()}.
     */
    private void runCrossRepConflictPass() {
        Map<SugVertex, InstrumentationDecision> decisionByCandidate = new HashMap<>();
        for (InstrumentationDecision d : validated) {
            if (repTypeOf(d) != null) {
                decisionByCandidate.put(d.getCandidate(), d);
            }
        }
        List<SugVertex> sites = new ArrayList<>(graph.getEqualsVerticesForCrossRep());
        // Location, then signature (id-free for every site an invoke produces), the id only as a last resort
        sites.sort(Comparator.comparing((SugVertex v) -> String.valueOf(v.getSourceLocation())).thenComparing((SugVertex v) -> String.valueOf(v.getMethodSignature())).thenComparingInt(
                        SugVertex::getId));
        Set<InstrumentationDecision> disabled = new LinkedHashSet<>();
        for (SugVertex c : sites) {
            boolean cmp = EqualsMatrixHeuristic.isCompareToStringCall(c);
            if (!EqualsMatrixHeuristic.isEqualsObjectCall(c) && !cmp) {
                continue;
            }
            List<InstrumentationDecision> recv = new ArrayList<>();
            List<InstrumentationDecision> arg = new ArrayList<>();
            BitSet ct = c.getSourceTags();
            for (int i = ct.nextSetBit(0); i >= 0; i = ct.nextSetBit(i + 1)) {
                SourceTag tag = graph.getSourceTag(i);
                InstrumentationDecision d = decisionByCandidate.get(tag.creationSite());
                if (d == null || disabled.contains(d)) {
                    continue;
                }
                if (tag.role() == UsageRole.RECEIVER) {
                    recv.add(d);
                } else if (tag.role() == UsageRole.PARAMETER && tag.paramIndex() == 1) {
                    arg.add(d);
                }
            }
            List<InstrumentationDecision> revert = crossRepEqualsRevertsIdDep(recv, arg);
            if (revert.isEmpty()) {
                continue;
            }
            Set<InstrumentationDecision> inv = crossRepEqualsInvolved(recv, arg);
            if (idDepMixed(inv)) {
                for (InstrumentationDecision d : revert) {
                    idDepDropped += d.getCandidate().isIdDep() ? 1 : 0;
                }
            }
            String keep = revert.containsAll(inv) ? "none" : repTypeOf(pickHighestPriority(new LinkedHashSet<>(inv.stream().filter(d -> !revert.contains(d)).toList())));
            disabled.addAll(revert);
            crossRepEqualsReverted.addAll(revert);
            for (InstrumentationDecision d : revert) {
                SugVertex v = d.getCandidate();
                String kind = d.getType() == OptimizationType.LAZY_CONCAT ? "concat" : d.getType() == OptimizationType.STRING_VIEW ? v.getMethodName() : "candidate";
                conflicts.add("REJECT V" + v.getId() + " (" + kind + " @ " + v.getSourceLocation() + "): cross-rep " + (cmp ? "compareTo" : "equals") + " conflict at " + c.getSourceLocation() +
                                " (" + repTypeOf(d) + " reverted, " + keep + " kept)");
            }
        }
        if (disabled.isEmpty()) {
            return;
        }
        List<InstrumentationDecision> kept = new ArrayList<>();
        for (InstrumentationDecision d : validated) {
            if (disabled.contains(d)) {
                conflictSuppressed.add(d);
            } else {
                kept.add(d);
            }
        }
        validated.clear();
        validated.addAll(kept);
    }

    /**
     * Pure (JUnit): whether an admitted receiver rep {@code recvRep} and argument rep {@code argRep} conflict at one
     * {@code equals(Object)} site: a pair with SB on either side is no conflict. Every rep's equals path
     * (Java body and parent intrinsic) compares a String argument of another class by content ({@code stringrep.RepEquals}),
     * so SB as the argument is correct; SB as the receiver is correct too: its {@code equals} reads the argument by
     * {@code length()/charAt()}, and at a REDIRECT site its inherited {@code String.maybeCustomStringEquals} deflects to
     * {@code arg.equals(sb)} ({@code RepEqualsMatrixTest}). Two non-SB reps still conflict.
     */
    static boolean isCrossRepEqualsConflict(String recvRep, String argRep) {
        if (recvRep.equals(argRep)) {
            return false;
        }
        return !("SBS".equals(argRep) || "SBS".equals(recvRep));
    }

    /** Pure: the decisions of every conflicting (receiver, argument) pair at one site, in encounter order. */
    static Set<InstrumentationDecision> crossRepEqualsInvolved(List<InstrumentationDecision> recv, List<InstrumentationDecision> arg) {
        Set<InstrumentationDecision> involved = new LinkedHashSet<>();
        for (InstrumentationDecision r : recv) {
            for (InstrumentationDecision a : arg) {
                if (isCrossRepEqualsConflict(repTypeOf(r), repTypeOf(a))) {
                    involved.add(r);
                    involved.add(a);
                }
            }
        }
        return involved;
    }

    /**
     * Pure: the decisions to revert at one site: every involved decision whose rep differs from the rep of the
     * highest-priority involved decision ({@link #crossRepPriority}), sorted by source location.
     */
    static List<InstrumentationDecision> crossRepEqualsReverts(List<InstrumentationDecision> recv, List<InstrumentationDecision> arg) {
        Set<InstrumentationDecision> involved = crossRepEqualsInvolved(recv, arg);
        if (involved.isEmpty()) {
            return List.of();
        }
        String keep = repTypeOf(pickHighestPriority(involved));
        List<InstrumentationDecision> revert = new ArrayList<>();
        for (InstrumentationDecision d : involved) {
            if (!repTypeOf(d).equals(keep)) {
                revert.add(d);
            }
        }
        revert.sort(Comparator.comparing((InstrumentationDecision d) -> String.valueOf(d.getCandidate().getSourceLocation())));
        return revert;
    }

    /** ID-DEP precedence: an involved set with both an ID-DEP and a non-ID-DEP decision. */
    static boolean idDepMixed(java.util.Collection<InstrumentationDecision> ds) {
        boolean dep = false;
        boolean non = false;
        for (InstrumentationDecision d : ds) {
            dep |= d.getCandidate().isIdDep();
            non |= !d.getCandidate().isIdDep();
        }
        return dep && non;
    }

    /**
     * The cross-candidate ID-DEP precedence: {@link #crossRepEqualsReverts}, unless the involved set mixes ID-DEP
     * decisions (admits reading a rule-U delivery, objret=1) with non-ID-DEP ones. Then the non-ID-DEP decisions are
     * resolved among themselves as without the ID-DEP ones, and every involved ID-DEP decision is reverted: an ID-DEP
     * admit never demotes a non-ID-DEP one.
     */
    static List<InstrumentationDecision> crossRepEqualsRevertsIdDep(List<InstrumentationDecision> recv, List<InstrumentationDecision> arg) {
        Set<InstrumentationDecision> involved = crossRepEqualsInvolved(recv, arg);
        if (!idDepMixed(involved)) {
            return crossRepEqualsReverts(recv, arg);
        }
        List<InstrumentationDecision> recvNon = recv.stream().filter(d -> !d.getCandidate().isIdDep()).toList();
        List<InstrumentationDecision> argNon = arg.stream().filter(d -> !d.getCandidate().isIdDep()).toList();
        Set<InstrumentationDecision> out = new LinkedHashSet<>(crossRepEqualsReverts(recvNon, argNon));
        for (InstrumentationDecision d : involved) {
            if (d.getCandidate().isIdDep()) {
                out.add(d);
            }
        }
        List<InstrumentationDecision> revert = new ArrayList<>(out);
        revert.sort(Comparator.comparing((InstrumentationDecision d) -> String.valueOf(d.getCandidate().getSourceLocation())));
        return revert;
    }

    private static InstrumentationDecision pickHighestPriority(Set<InstrumentationDecision> decisions) {
        InstrumentationDecision best = null;
        for (InstrumentationDecision d : decisions) {
            if (best == null || crossRepPriority(d) < crossRepPriority(best)) {
                best = d;
            }
        }
        return best;
    }

    static int crossRepPriority(InstrumentationDecision d) {
        if (d.getType() == OptimizationType.SINGLE_BYTE) {
            return 1;
        }
        if (d.getType() == OptimizationType.STRING_VIEW) {
            return 2;
        }
        if (d.getType() == OptimizationType.LAZY_CONCAT) {
            // Ranked by the minted rep (LazyConcatMint), the class the cap/conflict passes reason about
            String rep = repTypeOf(d);
            if (rep == null) {
                return 3;
            }
            return switch (rep) {
                case "ROPE" -> 3;
                case "THREE_WAY" -> 4;
                case "FIXED4" -> 5;
                case "ARRAY_LAZY" -> 6;
                case "INTERLEAVED" -> 7;
                default -> 3;
            };
        }
        if (d.getType() == OptimizationType.EQUALS_MATRIX) {
            return 8;
        }
        return Integer.MAX_VALUE;
    }

    /**
     * The rep name ({@link InlineCacheRegistry} / profile namespace) a replacing decision mints, or {@code null} when the
     * parent does not replace the site. For LAZY_CONCAT this is the class the parent really constructs
     * ({@link LazyConcatMint#mintedRep}), not the decision variant: a ROPE-labelled {@code a + "_" + b} mints an
     * ArrayLazyString, and every consumer (INLINE_CACHE rep lists, receiver-rep cap, cross-rep equals pass) must see that
     * class.
     */
    static String repTypeOf(InstrumentationDecision d) {
        if (d.getType() == OptimizationType.SINGLE_BYTE) {
            return "SBS";
        }
        if (d.getType() == OptimizationType.STRING_VIEW) {
            return "SV";
        }
        if (d.getType() == OptimizationType.LAZY_CONCAT) {
            String variant = d.getVariant();
            if (variant == null) {
                return "ROPE";
            }
            return LazyConcatMint.mintedRep(d.getCandidate(), variant);
        }
        return null;
    }

    static String repClassOfFqn(String fqn) {
        return switch (fqn) {
            // TrivialString shares the name SBS, but InlineCacheRegistry.REP_CLASSES maps SBS to SingleByteString only, so
            // an exact-SBS compare (IC arm, type-check IC list term) would miss a TrivialString. Moot while
            // TrivialString.create has no production caller; a production TrivialString needs its own kind name first.
            case "com.oracle.svm.core.stringrep.SingleByteString",
                            "com.oracle.svm.core.stringrep.TrivialString" -> "SBS";
            case "com.oracle.svm.core.stringrep.StringView" -> "SV";
            case "com.oracle.svm.core.stringrep.RopeString" -> "ROPE";
            case "com.oracle.svm.core.stringrep.ThreeWayString" -> "THREE_WAY";
            case "com.oracle.svm.core.stringrep.FixedConcat4" -> "FIXED4";
            case "com.oracle.svm.core.stringrep.ArrayLazyString" -> "ARRAY_LAZY";
            case "com.oracle.svm.core.stringrep.InterleavedStringArray" -> "INTERLEAVED";
            default -> fqn;
        };
    }

    private static String describeDecisions(Collection<InstrumentationDecision> decisions) {
        List<String> parts = new ArrayList<>();
        for (InstrumentationDecision d : decisions) {
            parts.add(d.getType() + "(V" + d.getCandidate().getId() + ")");
        }
        return String.join(", ", parts);
    }
}
