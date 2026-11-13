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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Which lazy rep kinds the kind-terminal concat group lists, and the inner/outer pairing that makes omitting the other
 * kinds sound. Computed in the child from the final validated decisions; the parent only reads the result (the
 * INLINE_CACHE {@code KT:} variants and the {@link #PAIR_TYPE} lines).
 * <p>
 * <b>The rule.</b> A lazy decision admitted as a non-copying concat operand reaches the stock concat machinery only
 * through an outer site that stays stock. Its kind is listed iff at least one of its recorded outer sites is not a kept
 * lazy outer ({@link #isKeptLazyOuter}). A decision whose outers are all kept lazy is held as a part of those outers and
 * never reaches the stock machinery, so it does not list its kind.
 * <p>
 * <b>The pairing contract.</b> The omission is sound only if every such outer is in fact lowered lazily. The child
 * writes one {@code <inner> LAZY_PAIR <outer>} line per (unlisted inner, outer); the parent (1) lowers an inner only
 * when every paired outer has a lazy LAZY_CONCAT profile entry (otherwise the inner stays a plain String), and (2)
 * treats a decline of a paired outer as a build error. The child predicts the parent's site-local declines with the
 * same mint function ({@link LazyConcatMint#mintedRep}); the context-dependent decline (a deopt-capable parse) exists
 * only with deoptimization support, where the child does not pair and lists every lazy-operand kind.
 * <p>
 * Knob {@code -Dsvm.stringanalysis.ic.ktprecise=0} lists every lazy-operand kind image-wide and writes no pair line. It
 * changes only the listing and pairing: the lazy-operand site recording through internal calls
 * ({@code LazyConcatHeuristic.validateUsages}, which prevents under-listing) and the raw-flow BFS recording stay. A
 * listed kind never needs a pair.
 */
final class LazyOperandPairing {

    /** Knob {@code ic.ktprecise}: 1 (default) = the precise rule; 0 = every lazy-operand kind listed, no pairs. */
    static final boolean PRECISE = Integer.getInteger("svm.stringanalysis.ic.ktprecise", 1) != 0;

    /** The profile line type of a pair: {@code <innerKey> LAZY_PAIR <outerKey>}. */
    static final String PAIR_TYPE = "LAZY_PAIR";

    /**
     * @param listedKinds the lazy kinds the concat group lists (sorted)
     * @param pairs unlisted inner key -> its kept lazy outer keys (sorted)
     * @param pairedOnlyKinds the lazy-operand kinds no longer listed (all their lazy-operand decisions are paired)
     * @param mode a short description for the child log
     */
    record Result(Set<String> listedKinds, Map<String, Set<String>> pairs, Set<String> pairedOnlyKinds, String mode) {
    }

    private LazyOperandPairing() {
    }

    /** Whether the image can deoptimize at all (a deopt-capable parse is the one parent decline the child cannot predict per site). */
    static boolean deoptPossible() {
        try {
            return com.oracle.svm.core.deopt.DeoptimizationSupport.enabled();
        } catch (Throwable t) {
            return true; // outside an image build: conservative
        }
    }

    static Result compute(List<InstrumentationDecision> validated) {
        return compute(validated, PRECISE, deoptPossible());
    }

    static Result compute(List<InstrumentationDecision> validated, boolean precise, boolean deoptPossible) {
        // the first LAZY_CONCAT decision per key: the one dumpProfile writes (it keeps the first of one key and type)
        Map<String, InstrumentationDecision> lcByKey = new LinkedHashMap<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.LAZY_CONCAT && d.getSourceLocation() != null) {
                lcByKey.putIfAbsent(d.getSourceLocation(), d);
            }
        }
        boolean pairing = precise && !deoptPossible;
        Set<String> listed = new TreeSet<>();
        Map<String, Set<String>> candidatePairs = new TreeMap<>();
        Map<String, String> candidateKind = new LinkedHashMap<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() != OptimizationType.LAZY_CONCAT || d.getCandidate().getLazyOperandSites().isEmpty()) {
                continue;
            }
            String rep = HeuristicOrchestrator.repTypeOf(d);
            if (rep == null) {
                continue;
            }
            Set<String> outers = new TreeSet<>(d.getCandidate().getLazyOperandSites());
            String key = d.getSourceLocation();
            boolean allKept = pairing && key != null && lcByKey.get(key) == d;
            for (String outer : outers) {
                if (!allKept) {
                    break;
                }
                allKept = !outer.equals(key) && isKeptLazyOuter(lcByKey.get(outer));
            }
            if (allKept) {
                candidatePairs.computeIfAbsent(key, k -> new TreeSet<>()).addAll(outers);
                candidateKind.put(key, rep);
            } else {
                listed.add(rep);
            }
        }
        Map<String, Set<String>> pairs = new TreeMap<>();
        Set<String> pairedOnly = new TreeSet<>();
        for (Map.Entry<String, Set<String>> e : candidatePairs.entrySet()) {
            String rep = candidateKind.get(e.getKey());
            if (!listed.contains(rep)) {
                pairs.put(e.getKey(), Collections.unmodifiableSet(e.getValue()));
                pairedOnly.add(rep);
            }
        }
        String mode = !precise ? "image-wide (ktprecise=0)" : deoptPossible ? "image-wide (deoptimization support: no pairing)" : "precise";
        return new Result(Collections.unmodifiableSet(listed), Collections.unmodifiableMap(pairs), Collections.unmodifiableSet(pairedOnly), mode);
    }

    /**
     * Whether the parent lowers the LAZY_CONCAT decision {@code d} lazily at its site: an indy concat site with a recorded
     * operand shape whose lazy variant mints a rep (the parent's own site-local checks
     * ({@code StringRepresentationReplacementPlugin.convertInvokeDynamic}: lazy variant, {@code dyn >= 1}, the same
     * {@link LazyConcatMint#mintedRep})). String.concat and String.join decisions are never a lazy operand's outer
     * ({@link LazyConcatHeuristic#isLazyOperandOk} needs an indy concat usage).
     */
    static boolean isKeptLazyOuter(InstrumentationDecision d) {
        if (d == null || d.getType() != OptimizationType.LAZY_CONCAT) {
            return false;
        }
        SugVertex v = d.getCandidate();
        String variant = d.getVariant();
        if (variant == null || !LazyConcatMint.isLazyVariant(variant) || v.getNodeType() != SugNodeType.CONCAT_EXPRESSION || v.isStringConcatCall() ||
                        LazyConcatMint.isJoinSource(v)) {
            return false;
        }
        int dyn = v.getDynamicOperandCount();
        return dyn >= 1 && LazyConcatMint.mintedRep(variant, dyn, v.getConcatRecipe()) != null;
    }

    /**
     * The pair lines the profile dump writes, from the same computation the concat group's listing was built from
     * ({@code icTime}; null when the concat group is off). A pair is written only when its inner is a LAZY_CONCAT decision
     * of the (possibly mode-filtered) dump: a pair of a dropped inner constrains nothing, and the listing is never
     * re-derived from a filtered list.
     */
    static List<String> dumpLines(Result icTime, List<InstrumentationDecision> toDump) {
        if (icTime == null || icTime.pairs().isEmpty()) {
            return List.of();
        }
        Set<String> lcKeys = new TreeSet<>();
        for (InstrumentationDecision d : toDump) {
            if (d.getType() == OptimizationType.LAZY_CONCAT && d.getSourceLocation() != null) {
                lcKeys.add(d.getSourceLocation());
            }
        }
        List<String> lines = new ArrayList<>();
        for (Map.Entry<String, Set<String>> e : icTime.pairs().entrySet()) {
            if (lcKeys.contains(e.getKey())) {
                for (String outer : e.getValue()) {
                    lines.add(e.getKey() + " " + PAIR_TYPE + " " + outer);
                }
            }
        }
        return lines;
    }

    /** The profile lines of the pairs, sorted: {@code <inner> LAZY_PAIR <outer>}. */
    static List<String> profileLines(Result r) {
        List<String> lines = new ArrayList<>();
        for (Map.Entry<String, Set<String>> e : r.pairs().entrySet()) {
            for (String outer : e.getValue()) {
                lines.add(e.getKey() + " " + PAIR_TYPE + " " + outer);
            }
        }
        return lines;
    }
}
