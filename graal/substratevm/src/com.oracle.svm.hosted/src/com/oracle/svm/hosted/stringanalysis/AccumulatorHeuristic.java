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

public final class AccumulatorHeuristic implements Heuristic {

    private final List<String> rejections = new ArrayList<>();
    private final List<String> warnings = new ArrayList<>();
    private int candidateCount;
    /** The two-pass Accumulator View on the walk's facts; false = the SUG-edge path (graph-fixture tests only). */
    private final boolean twoPass;
    /** Whether a StringJoiner extraction may admit (its rep is a lazy-concat rep: ALL and LC-only images; not SV/SB-only). */
    private boolean joinerAllowed = true;

    void setJoinerAllowed(boolean allowed) {
        joinerAllowed = allowed;
    }

    public AccumulatorHeuristic() {
        this(true);
    }

    /** {@code twoPass=false} pins the SUG-edge path (inert in the child) in the graph-fixture tests. */
    AccumulatorHeuristic(boolean twoPass) {
        this.twoPass = twoPass;
    }

    @Override
    public List<InstrumentationDecision> apply(StringUtilizationGraph graph) {
        UsageSourceBuilder.ensureBuilt(graph);
        rejections.clear();
        warnings.clear();
        candidateCount = 0;
        if (twoPass) {
            return applyTwoPass(graph);
        }
        List<InstrumentationDecision> decisions = new ArrayList<>();
        for (SugVertex v : graph.getVertices()) {
            if (v.getNodeType() != SugNodeType.NEW_ACCUMULATOR) {
                continue;
            }
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            candidateCount++;
            AccumulatorResult result = analyzeAccumulator(graph, v);
            if (result.rejection != null) {
                rejections.add("REJECT V" + v.getId() + " (accumulator @ " + v.getSourceLocation() + "): " + result.rejection);
                continue;
            }
            // This path has no backward receiver proof, so it attaches no exact class; the parent declines a class-less
            // ACCUMULATOR_VIEW entry (the site stays stock)
            for (SugVertex extraction : result.extractions) {
                decisions.add(new InstrumentationDecision(extraction, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW", null));
            }
        }
        return decisions;
    }

    /**
     * The Accumulator View on the walk's facts. Pass 1: a seeded accumulator (an emitted NEW_ACCUMULATOR atom) is only
     * growing iff its trace is complete and every usage is GROWING or READ ({@link AccumulatorWhitelist#accumulatorUsageRow}).
     * Pass 2: each extraction the walk seeded ({@code StringUtilizationGraph.accExtractionReceivers}) admits as STRING_VIEW
     * ACCUMULATOR_VIEW iff every accumulator its receiver comes from passed pass 1 and the extracted string passes the
     * String View check ({@link StringViewHeuristic#canOptimizeToView}: W_view, signature gates, complete trace).
     */
    private List<InstrumentationDecision> applyTwoPass(StringUtilizationGraph graph) {
        List<InstrumentationDecision> decisions = new ArrayList<>();
        int shared = 0;
        int notShared = 0;
        Set<SugVertex> growing = new HashSet<>();
        for (SugVertex v : graph.getVertices()) {
            if (v.getNodeType() != SugNodeType.NEW_ACCUMULATOR || !v.isEmittedAtom()) {
                continue;
            }
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            candidateCount++;
            String why = onlyGrowing(graph, v);
            if (why != null) {
                rejections.add("REJECT V" + v.getId() + " (accumulator @ " + v.getSourceLocation() + "): " + why);
            } else {
                growing.add(v);
            }
        }
        StringViewHeuristic sv = new StringViewHeuristic();
        LazyConcatHeuristic lc = new LazyConcatHeuristic();
        int joinerAdmit = 0;
        int joinerReject = 0;
        for (java.util.Map.Entry<SugVertex, Set<SugVertex>> e : graph.accExtractionReceivers().entrySet()) {
            SugVertex x = e.getKey();
            if (!ownersAllGrowing(growing, e.getValue())) {
                rejections.add("REJECT V" + x.getId() + " (extraction @ " + x.getSourceLocation() + "): its accumulator is not only growing");
                continue;
            }
            if (AccumulatorWhitelist.JOINER.equals(exactAccumulatorClass(e.getValue()))) {
                // A StringJoiner extraction mints an interleaved string (InterleavedStringArray.ofJoiner): the
                // lazy-concat check of that rep (W_lazy, INTERLEAVED), not the String View check
                String jwhy = joinerAllowed ? joinerExtractionRejection(lc, graph, x) : "joiner extraction: its rep (an interleaved string) is minted in ALL and LC-only mode";
                System.out.println("[sug-acc-joiner] " + x.getSourceLocation() + (jwhy == null ? " ADMIT" : " REJECT " + jwhy) + " stored=" + x.isStored());
                if (jwhy != null) {
                    joinerReject++;
                    rejections.add("REJECT V" + x.getId() + " (extraction @ " + x.getSourceLocation() + "): " + jwhy);
                } else {
                    joinerAdmit++;
                    decisions.add(new InstrumentationDecision(x, OptimizationType.LAZY_CONCAT, LazyConcatMint.INTERLEAVED, AccumulatorWhitelist.JOINER));
                }
                continue;
            }
            String why = sv.canOptimizeToView(graph, x);
            if (why != null) {
                rejections.add("REJECT V" + x.getId() + " (extraction @ " + x.getSourceLocation() + "): " + why);
                continue;
            }
            // Unified lowering: the profile entry carries the receivers' exact class (the parent lowers on it alone)
            String exact = exactAccumulatorClass(e.getValue());
            if (exact == null) {
                rejections.add("REJECT V" + x.getId() + " (extraction @ " + x.getSourceLocation() + "): its receivers are not of one exact accumulator class " +
                                ownerClasses(e.getValue()));
                continue;
            }
            // A stack-confined extraction (no heap-escape event, no leak-marked terminal outside W_view) is SHARED
            String leak = leakMarkedOutsideWhitelist(graph, x, new HashSet<>());
            String variant = accVariant(x.isStored() || leak != null);
            if (ACCUMULATOR_VIEW_SHARED.equals(variant)) {
                shared++;
            } else {
                notShared++;
            }
            System.out.println("[sug-acc-share] " + x.getSourceLocation() + " variant=" + variant + " stored=" + x.isStored() + (leak != null ? " leak=" + leak : ""));
            decisions.add(new InstrumentationDecision(x, OptimizationType.STRING_VIEW, variant, exact));
        }
        System.out.println("[sug-acc-share] shared=" + shared + " notShared=" + notShared); // share census
        System.out.println("[sug-acc-joiner] admit=" + joinerAdmit + " reject=" + joinerReject); // joiner census
        warnings.addAll(sv.getWarnings());
        warnings.addAll(lc.getWarnings());
        for (java.util.Map.Entry<SugVertex, String> e : graph.accExtractionUnseeded().entrySet()) {
            rejections.add("REJECT V" + e.getKey().getId() + " (extraction @ " + e.getKey().getSourceLocation() + "): " + e.getValue());
        }
        for (SugVertex v : growing) {
            if (!hasExtraction(graph, v)) {
                rejections.add("REJECT V" + v.getId() + " (accumulator @ " + v.getSourceLocation() + "): no seedable user-code extraction (toString) among its usages");
            }
        }
        return decisions;
    }

    /**
     * Null when the StringJoiner extraction {@code x} admits, else the reason. The extracted string is an interleaved
     * string ({@code ofJoiner}), so its usages pass that rep's lazy-concat check. A stored extraction (a heap escape or a
     * leak-marked usage outside W_view) stays stock: the interleaved string retains the joiner's array and parts, which
     * the flat JDK result does not. The REJECT text is kept verbatim (pinned).
     */
    static String joinerExtractionRejection(LazyConcatHeuristic lc, StringUtilizationGraph graph, SugVertex x) {
        String why = lc.validateJoinerExtraction(graph, x);
        if (why != null) {
            return why;
        }
        String leak = leakMarkedOutsideWhitelist(graph, x, new HashSet<>());
        if (x.isStored() || leak != null) {
            return "stored joiner extraction (an interleaved string would retain the joiner's parts)" +
                            (leak != null ? " leak=" + leak : "");
        }
        return null;
    }

    /** The variant word of a stack-confined admitted extraction (the existing 4-token profile line). */
    static final String ACCUMULATOR_VIEW_SHARED = "ACCUMULATOR_VIEW_SHARED";

    /**
     * Pure (JUnit): {@code ACCUMULATOR_VIEW_SHARED} iff the extracted string is not stored (stack-confined: the parent
     * lowers {@code StringView.createSkipCheck}, no occupancy check); else {@code ACCUMULATOR_VIEW}.
     */
    static String accVariant(boolean stored) {
        return !stored ? ACCUMULATOR_VIEW_SHARED : "ACCUMULATOR_VIEW";
    }

    /**
     * Conservative "stored": the first usage of {@code x} (internal calls followed, every role) that is a leak-marked
     * hand-list terminal ({@link StringTerminalHandList}: the default body may retain {@code this}) not in W_view; null
     * when none. Such a usage already fails the String View check at a non-PARAMETER role; this keeps a retention route
     * out of SHARED whatever the role. The leak-marked W_view entries are StringView overrides that never retain
     * {@code this} ({@code HandListLeakWhitelistTest.leakMarkedEntriesAreNeverWhitelistedOntoADefaultBody}).
     */
    static String leakMarkedOutsideWhitelist(StringUtilizationGraph graph, SugVertex x, Set<SugVertex> visited) {
        if (!visited.add(x)) {
            return null;
        }
        BitSet tags = x.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            SugVertex usage = graph.getUsageTag(i).usageSite();
            if (usage.getNodeType() != SugNodeType.STRING_METHOD_CALL && usage.getNodeType() != SugNodeType.JDK_LIBRARY_CALL) {
                continue;
            }
            if (StringAnalysisPolicy.isInternalCall(usage)) {
                String sub = leakMarkedOutsideWhitelist(graph, usage, visited);
                if (sub != null) {
                    return sub;
                }
                continue;
            }
            if (isLeakMarkedOutsideWhitelist(usage.getDeclaringClass(), usage.getMethodName(), usage.getMethodSignature())) {
                return usage.getDeclaringClass() + "." + usage.getMethodName() + "(" + usage.getMethodSignature() + ")";
            }
        }
        return null;
    }

    /** A leak-marked hand-list terminal outside W_view (pure; pinned by JUnit). */
    static boolean isLeakMarkedOutsideWhitelist(String declaringClass, String name, String signature) {
        for (StringTerminalHandList.Entry e : StringTerminalHandList.leakMarked()) {
            if (e.declaringClass().equals(declaringClass) && e.name().equals(name) && e.signature().equals(signature)) {
                return !StringViewWhitelist.isWhitelistedUsage(name, declaringClass, signature);
            }
        }
        return false;
    }

    /** Pure (JUnit): the owners qualify iff there is at least one and every one passed pass 1 (no atom rejects). */
    static <V> boolean ownersAllGrowing(Set<V> growing, Set<V> owners) {
        return !owners.isEmpty() && growing.containsAll(owners);
    }

    /**
     * Pure (JUnit): the exact class of an extraction's receivers. The receiver proof holds every receiver to be born at
     * a {@code new <T>} of one of {@code owners} (allocated type exactly the seed's type,
     * {@code ForwardFixpoint.seedAccumulatorAtoms}), so the run-time class is exactly {@code T} when every owner has type
     * {@code T}; null when the owners are empty, untyped or of more than one class.
     */
    static String exactAccumulatorClass(Set<SugVertex> owners) {
        List<String> names = new ArrayList<>(owners.size());
        for (SugVertex o : owners) {
            names.add(o.getJavaType() == null ? null : o.getJavaType().toJavaName(true));
        }
        return exactClassOf(names);
    }

    /** The one class all {@code ownerTypes} name; null for none, an untyped (null) owner or two classes. */
    static String exactClassOf(List<String> ownerTypes) {
        String exact = null;
        for (String t : ownerTypes) {
            if (t == null || (exact != null && !exact.equals(t))) {
                return null;
            }
            exact = t;
        }
        return exact;
    }

    private static String ownerClasses(Set<SugVertex> owners) {
        java.util.TreeSet<String> names = new java.util.TreeSet<>();
        for (SugVertex o : owners) {
            names.add(o.getJavaType() == null ? "<untyped>" : o.getJavaType().toJavaName(true));
        }
        return names.toString();
    }

    /** Pass 1 on the emitted facts: null = only growing, else the reason. */
    static String onlyGrowing(StringUtilizationGraph graph, SugVertex acc) {
        if (acc.getBudgetRefusal() != null || acc.isIncompleteTrace()) {
            return "incomplete downstream trace — conservatively rejected";
        }
        BitSet tags = acc.getUsageTags();
        // The reported usage is the least by its text (deterministic: not the tag index order)
        String first = null;
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            SugVertex u = tag.usageSite();
            String owner = u == null ? null : AccumulatorWhitelist.classifyingOwner(u.getDeclaringClass(), tag.dispatchOwner());
            if (u == null || AccumulatorWhitelist.accumulatorUsageRow(owner, u.getMethodName(), tag.role()) == AccumulatorWhitelist.AccRow.REJECT) {
                String d = (u == null ? "null site"
                                : owner + "." + u.getMethodName() + "(" + u.getMethodSignature() + ") @ " +
                                                u.getSourceLocation()) + " role=" + tag.role() + (tag.dispatchOwner() != null ? " (dispatched; declared " + u.getDeclaringClass() + ")" : "");
                if (first == null || d.compareTo(first) < 0) {
                    first = d;
                }
            }
        }
        return first == null ? null : "not only growing: " + first;
    }

    private static boolean hasExtraction(StringUtilizationGraph graph, SugVertex acc) {
        for (java.util.Map.Entry<SugVertex, Set<SugVertex>> e : graph.accExtractionReceivers().entrySet()) {
            if (e.getValue().contains(acc)) {
                return true;
            }
        }
        BitSet tags = acc.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            if (graph.accExtractionUnseeded().containsKey(graph.getUsageTag(i).usageSite())) {
                return true;
            }
        }
        return false;
    }

    public List<String> getRejections() {
        return rejections;
    }

    /** The no-usage warnings of admitted extractions. */
    public List<String> getWarnings() {
        return warnings;
    }

    public int getCandidateCount() {
        return candidateCount;
    }

    private AccumulatorResult analyzeAccumulator(StringUtilizationGraph graph, SugVertex accumulator) {
        if (accumulator.isIncompleteTrace()) {
            return AccumulatorResult.reject("incomplete downstream trace — conservatively rejected");
        }
        List<SugVertex> extractions = new ArrayList<>();
        String rejection = collectAccumulatorUsages(graph, accumulator, new HashSet<>(), extractions);
        if (rejection != null) {
            return AccumulatorResult.reject(rejection);
        }
        if (extractions.isEmpty()) {
            return AccumulatorResult.reject("no whitelisted extraction method (toString/substring/subSequence) found among reachable accumulator calls");
        }
        for (SugVertex extraction : extractions) {
            if (extraction.isIncompleteTrace()) {
                return AccumulatorResult.reject("extraction at " + extraction.getSourceLocation() +
                                " has incomplete downstream trace — conservatively rejected");
            }
            String valRejection = validateExtractedString(graph, extraction, new HashSet<>());
            if (valRejection != null) {
                return AccumulatorResult.reject(valRejection);
            }
        }
        // No-usage detector: such extractions stay admitted, with a warning
        for (SugVertex extraction : extractions) {
            if (AdmissionProof.hasNoUsage(extraction)) {
                warnings.add(AdmissionProof.noUsageWarning(extraction, "extraction"));
            }
        }
        return AccumulatorResult.accept(extractions);
    }

    private String collectAccumulatorUsages(StringUtilizationGraph graph, SugVertex creationSite, Set<SugVertex> visited, List<SugVertex> extractions) {
        if (!visited.add(creationSite)) {
            return null;
        }
        BitSet tags = creationSite.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            SugVertex usage = graph.getUsageTag(i).usageSite();
            if (usage.getNodeType() != SugNodeType.STRING_METHOD_CALL && usage.getNodeType() != SugNodeType.JDK_LIBRARY_CALL) {
                continue;
            }
            if (StringAnalysisPolicy.isInternalCall(usage)) {
                String sub = collectAccumulatorUsages(graph, usage, visited, extractions);
                if (sub != null) {
                    return sub;
                }
                continue;
            }
            if (AccumulatorWhitelist.isAccumulatorType(usage.getDeclaringClass())) {
                if (!AccumulatorWhitelist.isWhitelisted(usage.getMethodName())) {
                    return "non-whitelisted accumulator call " +
                                    usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    " @ " + usage.getSourceLocation() + " (V" + usage.getId() + ")";
                }
                if (AccumulatorWhitelist.isExtraction(usage.getMethodName())) {
                    extractions.add(usage);
                }
            }
        }
        return null;
    }

    private String validateExtractedString(StringUtilizationGraph graph, SugVertex extraction, Set<SugVertex> visited) {
        if (!visited.add(extraction)) {
            return null;
        }
        BitSet tags = extraction.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                continue;
            }
            SugVertex usage = tag.usageSite();
            if (usage.getNodeType() == SugNodeType.STRING_METHOD_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    String sub = validateExtractedString(graph, usage, visited);
                    if (sub != null) {
                        return sub;
                    }
                    continue;
                }
                if (!StringViewWhitelist.isWhitelistedUsage(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature())) {
                    return "extracted string has non-whitelisted call " +
                                    usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")";
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) {
                if (StringAnalysisPolicy.isInternalCall(usage)) {
                    String sub = validateExtractedString(graph, usage, visited);
                    if (sub != null) {
                        return sub;
                    }
                    continue;
                }
                if (!StringViewWhitelist.isWhitelistedUsage(usage.getMethodName(), usage.getDeclaringClass(), usage.getMethodSignature())) {
                    return "extracted string has non-whitelisted JDK library call " +
                                    usage.getDeclaringClass() + "." + usage.getMethodName() +
                                    "(" + usage.getMethodSignature() + ") @ " + usage.getSourceLocation() +
                                    " (V" + usage.getId() + ")";
                }
                continue;
            }
            if (usage.getNodeType() == SugNodeType.CONCAT_EXPRESSION) {
                return "extracted string has concat expression @ " + usage.getSourceLocation() + " (V" + usage.getId() + ")";
            }
        }
        return null;
    }

    private static final class AccumulatorResult {
        final List<SugVertex> extractions;
        final String rejection;

        private AccumulatorResult(List<SugVertex> extractions, String rejection) {
            this.extractions = extractions;
            this.rejection = rejection;
        }

        static AccumulatorResult accept(List<SugVertex> extractions) {
            return new AccumulatorResult(extractions, null);
        }

        static AccumulatorResult reject(String reason) {
            return new AccumulatorResult(List.of(), reason);
        }
    }
}