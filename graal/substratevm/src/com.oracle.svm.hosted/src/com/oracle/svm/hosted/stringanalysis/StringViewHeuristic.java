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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public final class StringViewHeuristic implements Heuristic {

    private final List<String> rejections = new ArrayList<>();
    private final List<String> warnings = new ArrayList<>();

    @Override
    public List<InstrumentationDecision> apply(StringUtilizationGraph graph) {
        UsageSourceBuilder.ensureBuilt(graph);
        rejections.clear();
        warnings.clear();
        List<InstrumentationDecision> decisions = new ArrayList<>();
        int stored = 0;
        int confined = 0;
        int constShort = 0;
        Set<String> constShortKeys = new HashSet<>();
        for (SugVertex v : graph.getVertices()) {
            if (!isCandidate(v)) {
                continue;
            }
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            String reason = canOptimizeToView(graph, v);
            if (reason == null) {
                // A stored substring (heap-escape event, or a leak-marked usage outside W_view: the accumulator
                // view's rule) is STRING_VIEW STORED (the parent lowers StringView.createStored: runtime copy checks)
                boolean isStored = v.isStored() || AccumulatorHeuristic.leakMarkedOutsideWhitelist(graph, v, new HashSet<>()) != null;
                String variant = svVariant(isStored);
                if (refusesConstShortRange(variant, v.getConstRangeLength())) {
                    // only SV is refused here; the other heuristics (SBS) still decide the site
                    constShort++;
                    constShortKeys.add(v.getSourceLocation());
                    System.out.println("[sug-sv-constshort] " + v.getSourceKey() + " @ " + v.getSourceLocation() + " len=" + v.getConstRangeLength() + " REJECT " + SV_CONST_SHORT_RANGE);
                    rejections.add("REJECT V" + v.getId() + " (" + v.getMethodName() + " @ " + v.getSourceLocation() + "): " + SV_CONST_SHORT_RANGE +
                                    " (constant range length " + v.getConstRangeLength() + " <= " + CONST_SHORT_RANGE_MAX + ")");
                    continue;
                }
                if (isStored) {
                    stored++;
                } else {
                    confined++;
                }
                decisions.add(new InstrumentationDecision(v, OptimizationType.STRING_VIEW, variant));
            } else {
                rejections.add("REJECT V" + v.getId() + " (" + v.getMethodName() + " @ " + v.getSourceLocation() + "): " + reason);
            }
        }
        System.out.println("[sug-sv-stored] stored=" + stored + " confined=" + confined); // stored-view census
        // A confined duplicate vertex at a refused key must not lower the key as an unchecked view (the
        // stored one would get it): the refusal covers the key (the range length is a fact of the site, so equal there)
        decisions.removeIf(d -> {
            boolean drop = constShortKeys.contains(d.getSourceLocation());
            if (drop) {
                rejections.add("REJECT V" + d.getCandidate().getId() + " (" + d.getCandidate().getMethodName() + " @ " + d.getSourceLocation() + "): " + SV_CONST_SHORT_RANGE + " (key)");
            }
            return drop;
        });
        System.out.println("[sug-sv-constshort] refused=" + constShort); // const-short census
        // The element-source calls (ElementSources): their atom is the elements of the fresh stream/array; the
        // String View check and the stored rule as for a substring; the variant tells the parent's factory which view
        int elemAdmit = 0;
        int elemReject = 0;
        for (SugVertex x : graph.elemSources()) {
            String why = canOptimizeToView(graph, x);
            if (why != null) {
                elemReject++;
                System.out.println("[sug-elem] " + x.getSourceLocation() + " " + x.getLabel() + " REJECT " + why + " stored=" + x.isStored());
                rejections.add("REJECT V" + x.getId() + " (element source " + x.getMethodName() + " @ " + x.getSourceLocation() + "): " + why);
                continue;
            }
            boolean isStored = x.isStored() || AccumulatorHeuristic.leakMarkedOutsideWhitelist(graph, x, new HashSet<>()) != null;
            String variant = ElementSources.variant(isStored);
            elemAdmit++;
            System.out.println("[sug-elem] " + x.getSourceLocation() + " " + x.getLabel() + " ADMIT variant=" + variant + " stored=" + x.isStored());
            decisions.add(new InstrumentationDecision(x, OptimizationType.STRING_VIEW, variant));
        }
        System.out.println("[sug-elem] admit=" + elemAdmit + " reject=" + elemReject); // element-source census
        return decisions;
    }

    /** The variant word of a stored substring-view admit (the 3-token line {@code <key> STRING_VIEW STORED}). */
    static final String STORED = "STORED";

    /**
     * The variant of an admitted substring site (pure): {@code STORED} iff the substring is stored; otherwise none (the
     * plain {@code STRING_VIEW} line, an unchecked view).
     */
    static String svVariant(boolean stored) {
        return stored ? STORED : null;
    }

    /** The named refusal of a stored substring view whose range length is a constant <= {@link #CONST_SHORT_RANGE_MAX}. */
    static final String SV_CONST_SHORT_RANGE = "SV_CONST_SHORT_RANGE";

    /** At most 4 chars (<= 8 bytes): the view (56 B) saves nothing over a copy, see below. */
    static final int CONST_SHORT_RANGE_MAX = 4;

    /**
     * Refuse a {@code STRING_VIEW STORED} admit whose range length is a compile-time constant {@code <= 4} (pure;
     * {@code constRange} -1 = unknown). Such a view saves no memory, {@code StringView.createStored}'s occupancy rule
     * copies on any backing string of more than 8 chars, and every consumer would still pay the view arms. A run-time
     * length is never refused; an unchecked (confined) view is not touched.
     */
    static boolean refusesConstShortRange(String variant, int constRange) {
        return STORED.equals(variant) && constRange >= 0 && constRange <= CONST_SHORT_RANGE_MAX;
    }

    public List<String> getRejections() {
        return rejections;
    }

    /** The no-usage warnings of admitted candidates. */
    public List<String> getWarnings() {
        return warnings;
    }

    private boolean isCandidate(SugVertex v) {
        if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL) {
            return false;
        }
        return "substring".equals(v.getMethodName()) || "subSequence".equals(v.getMethodName());
    }

    /* package-private: the accumulator heuristic reuses the String View check for its extractions. */
    String canOptimizeToView(StringUtilizationGraph graph, SugVertex candidate) {
        if (candidate.getBudgetRefusal() != null) {
            // A budget-class refusal takes precedence over the usage validation: the delivered usages are a
            // schedule-dependent subset.
            if (ForwardFixpoint.D2_ALL_TOKEN.equals(candidate.getBudgetRefusal())) {
                // Any refusal of the recursive tracking; the names are schedule-dependent and go to the raw facts line.
                return "rtrack refusal — usages suppressed";
            }
            return "budget refusal " + candidate.getBudgetRefusal() + " — usages suppressed";
        }
        String rejection = validateUsages(graph, candidate, new HashSet<>());
        if (rejection != null) {
            return rejection;
        }
        if (candidate.isIncompleteTrace()) {
            return "incomplete downstream trace — conservatively rejected";
        }
        if (AdmissionProof.hasNoUsage(candidate)) {
            warnings.add(AdmissionProof.noUsageWarning(candidate, candidate.getMethodName())); // the no-usage detector
        }
        return null; // a no-usage candidate is admitted (see AdmissionProof)
    }

    private String validateUsages(StringUtilizationGraph graph, SugVertex creationSite, Set<SugVertex> visited) {
        if (!visited.add(creationSite)) {
            return null;
        }
        BitSet tags = creationSite.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                continue;
            }
            SugVertex usage = tag.usageSite();
            if (usage.getNodeType() == SugNodeType.STRING_METHOD_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    String sub = validateUsages(graph, usage, visited);
                    if (sub != null) {
                        return sub;
                    }
                    continue;
                }
                if (!StringViewWhitelist.isWhitelistedUsage(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature())) {
                    return "non-whitelisted call " + usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")";
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    String sub = validateUsages(graph, usage, visited);
                    if (sub != null) {
                        return sub;
                    }
                    continue;
                }
                if (!StringViewWhitelist.isWhitelistedUsage(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature())) {
                    return "non-whitelisted JDK library call " + usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")";
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.CONCAT_EXPRESSION) {
                if (usage.isScfNoCopy()) {
                    // An operand of a concat whose JDK strategy reads it through length() / isLatin1() /
                    // coder() / getBytes([BIB) / toString() only (StringAtoms.scfCopiesOperand): supported by StringView
                    continue;
                }
                if (isLowerableCopySite(usage)) {
                    // An operand of a copying concat in user code: the parent replaces exactly this indy with
                    // RepConcat (the profile's CONCAT_COPY line, copyingConcatSites), which never reads value()
                    continue;
                }
                return "concat expression @ " + usage.getSourceLocation() + " (V" + usage.getId() + ")";
            }
        }
        return null;
    }

    /**
     * The source locations of the non-copying concat sites the candidate is an operand of (its usage tags as
     * {@link #validateUsages} reads them: PARAMETER tags skipped, internal calls followed). The orchestrator disables a Lazy
     * Concat decision at such a site: a lazy rep holds its children and reads them directly ({@code RopeString.childEquals}:
     * {@code value()}, null for a StringView).
     */
    static java.util.Set<String> concatOperandSites(StringUtilizationGraph graph, SugVertex candidate) {
        java.util.Set<String> out = new java.util.LinkedHashSet<>();
        collectConcatOperandSites(graph, candidate, new HashSet<>(), out);
        return out;
    }

    private static void collectConcatOperandSites(StringUtilizationGraph graph, SugVertex v, Set<SugVertex> visited, java.util.Set<String> out) {
        if (!visited.add(v)) {
            return;
        }
        BitSet tags = v.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                continue;
            }
            SugVertex usage = tag.usageSite();
            if (usage == null) {
                continue;
            }
            if ((usage.getNodeType() == SugNodeType.STRING_METHOD_CALL || usage.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) && StringAnalysisPolicy.isInternalCall(usage)) {
                collectConcatOperandSites(graph, usage, visited, out);
            } else if (usage.getNodeType() == SugNodeType.CONCAT_EXPRESSION && usage.isScfNoCopy() && usage.getSourceLocation() != null) {
                out.add(usage.getSourceLocation());
            }
        }
    }

    /**
     * A String View operand usage at {@code usage} is accepted as a copying concat operand (pure): the site is an indy
     * concat with a lowerable copying shape ({@link StringAtoms#scfCopyShape}), it has a profile key, and its enclosing
     * class is user code (an indy inside a JDK-internal body is never rewritten).
     */
    static boolean isLowerableCopySite(SugVertex usage) {
        return usage.getNodeType() == SugNodeType.CONCAT_EXPRESSION && usage.getScfCopyShape() != null && usage.getSourceLocation() != null &&
                        StringAnalysisPolicy.isUserCodeClass(StringAnalysisPolicy.enclosingClassName(usage));
    }

    /**
     * The copying concat sites (key -> shape) the candidate is an operand of, collected as
     * {@link #concatOperandSites} collects the non-copying ones. The nested-concat pass counts them like the non-copying
     * sites (an LC decision there is dropped, or the view by the ID-DEP precedence).
     */
    static java.util.Map<String, StringAtoms.CopyShape> copyingConcatSites(StringUtilizationGraph graph, SugVertex candidate) {
        java.util.Map<String, StringAtoms.CopyShape> out = new java.util.LinkedHashMap<>();
        collectCopyingConcatSites(graph, candidate, new HashSet<>(), out);
        return out;
    }

    /** The profile line type of a copying concat site lowered with RepConcat: {@code <key> CONCAT_COPY UNARY|BINARY}. */
    static final String CONCAT_COPY_TYPE = "CONCAT_COPY";

    /**
     * The {@code CONCAT_COPY} profile lines (sorted) of the copying concat sites reached by a dumped String View decision.
     * A key that also has a dumped LAZY_CONCAT decision is an invariant violation (the nested-concat pass drops one of
     * the two): it fails.
     */
    static List<String> concatCopyLines(StringUtilizationGraph graph, List<InstrumentationDecision> toDump) {
        java.util.Map<String, StringAtoms.CopyShape> sites = new java.util.TreeMap<>();
        Set<String> lcKeys = new HashSet<>();
        for (InstrumentationDecision d : toDump) {
            if (d.getType() == OptimizationType.STRING_VIEW && d.getSourceLocation() != null) {
                sites.putAll(copyingConcatSites(graph, d.getCandidate()));
            } else if (d.getType() == OptimizationType.LAZY_CONCAT && d.getSourceLocation() != null) {
                lcKeys.add(d.getSourceLocation());
            }
        }
        List<String> lines = new ArrayList<>();
        for (java.util.Map.Entry<String, StringAtoms.CopyShape> e : sites.entrySet()) {
            if (lcKeys.contains(e.getKey())) {
                throw new IllegalStateException("[string-analysis] CONCAT_COPY site " + e.getKey() + " also has a kept LAZY_CONCAT decision (nested-concat pass invariant)");
            }
            lines.add(e.getKey() + " " + CONCAT_COPY_TYPE + " " + e.getValue().name());
        }
        return lines;
    }

    private static void collectCopyingConcatSites(StringUtilizationGraph graph, SugVertex v, Set<SugVertex> visited, java.util.Map<String, StringAtoms.CopyShape> out) {
        if (!visited.add(v)) {
            return;
        }
        BitSet tags = v.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                continue;
            }
            SugVertex usage = tag.usageSite();
            if (usage == null) {
                continue;
            }
            if ((usage.getNodeType() == SugNodeType.STRING_METHOD_CALL || usage.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) && StringAnalysisPolicy.isInternalCall(usage)) {
                collectCopyingConcatSites(graph, usage, visited, out);
            } else if (!usage.isScfNoCopy() && isLowerableCopySite(usage)) {
                out.put(usage.getSourceLocation(), usage.getScfCopyShape());
            }
        }
    }
}
