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

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import org.graalvm.nativeimage.hosted.Feature;
import org.graalvm.nativeimage.hosted.Feature.AfterAnalysisAccess;
import org.graalvm.nativeimage.hosted.Feature.AfterRegistrationAccess;
import org.graalvm.nativeimage.hosted.Feature.AfterHeapLayoutAccess;
import org.graalvm.nativeimage.hosted.Feature.BeforeAnalysisAccess;
import org.graalvm.nativeimage.hosted.Feature.BeforeCompilationAccess;

import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.reports.ReportUtils;
import com.oracle.svm.core.ParsingReason;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.graal.RuntimeCompilation;
import com.oracle.svm.core.feature.AutomaticallyRegisteredFeature;
import com.oracle.svm.core.feature.InternalFeature;
import com.oracle.svm.core.option.HostedOptionValues;
import com.oracle.svm.core.util.UserError;
import com.oracle.svm.hosted.FeatureImpl;
import com.oracle.svm.hosted.NativeImageGenerator;
import com.oracle.svm.util.ReflectionUtil;

import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration.Plugins;
import jdk.graal.compiler.phases.util.Providers;

/**
 * Native-image feature that drives the in-GraalVM string utilization analysis. Gated by the
 * {@code StringAnalysis} hosted option (off by default): when enabled it registers a pre-lowering
 * capture plugin during points-to parsing and, at {@code afterAnalysis}, builds the SUG, runs the
 * heuristics, and publishes {@link StringAnalysisResults} plus report files.
 */
@AutomaticallyRegisteredFeature
public final class StringAnalysisFeature implements InternalFeature {

    static final Map<AnalysisMethod, List<CapturedSite>> CAPTURED = new ConcurrentHashMap<>();

    private static volatile long saProcessStartNanos;
    private static volatile long saBeforeAnalysisStartNanos;
    private static volatile long saBeforeAnalysisDoneNanos;
    private static volatile long saAfterAnalysisStartNanos;

    public static void clearCaptured() {
        CAPTURED.clear();
    }

    public static java.util.Map<AnalysisMethod, java.util.List<CapturedSite>> getCaptured() {
        return CAPTURED;
    }

    public static final class SugAnalysisContext {
        public final StringAnalysisResults results;
        public final StringUtilizationGraph sug;
        public final LengthPropagator propagator;
        public final SingleByteHeuristic singleByte;
        public final List<InstrumentationDecision> singleByteDecisions;
        public final StringViewHeuristic stringView;
        public final List<InstrumentationDecision> stringViewDecisions;
        public final LazyConcatHeuristic lazyConcat;
        public final List<InstrumentationDecision> lazyConcatDecisions;
        public final AccumulatorHeuristic accumulator;
        public final List<InstrumentationDecision> accumulatorDecisions;
        public final EqualsMatrixHeuristic equalsMatrix;
        public final List<InstrumentationDecision> equalsMatrixDecisions;
        public final HeuristicOrchestrator orchestrator;
        public final List<InstrumentationDecision> validated;
        /** The KT concat group's listing and pairs, computed once by the IC heuristic (may be null). */
        final LazyOperandPairing.Result lazyOperandPairing;
        /** Type-check IC: the IC heuristic of this run (its receiver rule and KT facts; null outside the pipeline). */
        InlineCacheProfilingHeuristic icHeuristic;

        public SugAnalysisContext(StringAnalysisResults results, StringUtilizationGraph sug, LengthPropagator propagator,
                        SingleByteHeuristic singleByte, List<InstrumentationDecision> singleByteDecisions,
                        StringViewHeuristic stringView, List<InstrumentationDecision> stringViewDecisions,
                        LazyConcatHeuristic lazyConcat, List<InstrumentationDecision> lazyConcatDecisions,
                        AccumulatorHeuristic accumulator, List<InstrumentationDecision> accumulatorDecisions,
                        EqualsMatrixHeuristic equalsMatrix, List<InstrumentationDecision> equalsMatrixDecisions,
                        HeuristicOrchestrator orchestrator, List<InstrumentationDecision> validated, LazyOperandPairing.Result lazyOperandPairing) {
            this.results = results;
            this.sug = sug;
            this.propagator = propagator;
            this.singleByte = singleByte;
            this.singleByteDecisions = singleByteDecisions;
            this.stringView = stringView;
            this.stringViewDecisions = stringViewDecisions;
            this.lazyConcat = lazyConcat;
            this.lazyConcatDecisions = lazyConcatDecisions;
            this.accumulator = accumulator;
            this.accumulatorDecisions = accumulatorDecisions;
            this.equalsMatrix = equalsMatrix;
            this.equalsMatrixDecisions = equalsMatrixDecisions;
            this.orchestrator = orchestrator;
            this.validated = validated;
            this.lazyOperandPairing = lazyOperandPairing;
        }
    }

    public static SugAnalysisContext buildSugAndRunHeuristics(
                    BigBang bb,
                    AnalysisUniverse universe,
                    Map<AnalysisMethod, List<CapturedSite>> captured) {
        StringAnalysisDiagnostics.printCapturedSites();

        long sugBuildStart = System.nanoTime();
        SugBuilderV2 v2Builder = new SugBuilderV2(bb);
        StringUtilizationGraph sug = v2Builder.build(universe, captured);
        System.out.println("[string-analysis-timing] SUG build (SugBuilderV2) done: " + ((System.nanoTime() - sugBuildStart) / 1_000_000) + "ms");

        LengthPropagator propagator = new LengthPropagator(sug, captured);
        long lpStart = System.nanoTime();
        propagator.propagate();
        System.out.println("[string-analysis-timing] LengthPropagator done: " + ((System.nanoTime() - lpStart) / 1_000_000) + "ms");

        // The unified forward fixpoint (ForwardFixpoint.runAndEmit, inside SugBuilderV2.phaseBDownstreamSearch) is the
        // sole source of usageTags/sourceTags/incompleteTrace; it is always on.

        long heuristicsStart = System.nanoTime();
        long t0 = System.nanoTime();
        SingleByteHeuristic singleByte = new SingleByteHeuristic();
        List<InstrumentationDecision> singleByteDecisions = singleByte.apply(sug);
        System.out.println("[string-analysis-timing] heuristic SingleByte done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (decisions=" + singleByteDecisions.size() + ")");

        t0 = System.nanoTime();
        StringViewHeuristic stringView = new StringViewHeuristic();
        List<InstrumentationDecision> stringViewDecisions = stringView.apply(sug);
        System.out.println("[string-analysis-timing] heuristic StringView done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (decisions=" + stringViewDecisions.size() + ")");

        t0 = System.nanoTime();
        LazyConcatHeuristic lazyConcat = new LazyConcatHeuristic();
        List<InstrumentationDecision> lazyConcatDecisions = lazyConcat.apply(sug);
        System.out.println("[string-analysis-timing] heuristic LazyConcat done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (decisions=" + lazyConcatDecisions.size() + ")");

        t0 = System.nanoTime();
        AccumulatorHeuristic accumulator = new AccumulatorHeuristic();
        // A StringJoiner extraction mints an interleaved string (a lazy-concat rep): ALL and LC-only mode
        accumulator.setJoinerAllowed(!SubstrateOptions.StringAnalysisStringViewOnly.getValue() && !SubstrateOptions.StringAnalysisSingleByteOnly.getValue());
        List<InstrumentationDecision> accumulatorDecisions = accumulator.apply(sug);
        System.out.println("[string-analysis-timing] heuristic Accumulator done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (decisions=" + accumulatorDecisions.size() + ")");

        printNoUsageWarnings(singleByte.getWarnings(), stringView.getWarnings(), lazyConcat.getWarnings(), accumulator.getWarnings());

        EqualsMatrixHeuristic equalsMatrix = new EqualsMatrixHeuristic();
        List<InstrumentationDecision> equalsMatrixDecisions;

        OrchestratorInputs modeInputs = orchestratorInputs(SubstrateOptions.StringAnalysisStringViewOnly.getValue(),
                        SubstrateOptions.StringAnalysisLazyConcatOnly.getValue(), SubstrateOptions.StringAnalysisSingleByteOnly.getValue(),
                        singleByteDecisions, stringViewDecisions, lazyConcatDecisions, accumulatorDecisions);
        List<InstrumentationDecision> sbForOrchestrator = modeInputs.sb();
        List<InstrumentationDecision> svForOrchestrator = modeInputs.sv();
        List<InstrumentationDecision> lcForOrchestrator = modeInputs.lc();
        List<InstrumentationDecision> accForOrchestrator = modeInputs.acc();

        t0 = System.nanoTime();
        HeuristicOrchestrator orchestrator = new HeuristicOrchestrator(sug);
        orchestrator.run(sbForOrchestrator, svForOrchestrator, lcForOrchestrator, accForOrchestrator, Collections.emptyList());
        List<InstrumentationDecision> validated = orchestrator.getValidatedDecisions();
        System.out.println("[string-analysis-timing] HeuristicOrchestrator#1 (applyPrecedence+validation+crossRep+singleCustomRep) done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (validated=" +
                        validated.size() + ")");
        System.out.println("[string-analysis-timing] Heuristics+Orchestrator done: " + ((System.nanoTime() - heuristicsStart) / 1_000_000) + "ms");

        t0 = System.nanoTime();
        Set<SugVertex> customRepCandidates = collectCustomRepCandidates(validated);
        equalsMatrixDecisions = equalsMatrix.apply(sug, customRepCandidates);
        System.out.println("[string-analysis-timing] heuristic EqualsMatrix done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (decisions=" + equalsMatrixDecisions.size() + ")");

        t0 = System.nanoTime();
        orchestrator.runSecondPhase(equalsMatrixDecisions);
        validated = orchestrator.getValidatedDecisions();
        EqualsConflictDiag.print(sug, validated, orchestrator); // print-only (eq.diag)
        if (LazyConcatMint.MINT_LOG) {
            printWithdrawnMints(lazyConcatDecisions, validated);
        }
        System.out.println("[string-analysis-timing] HeuristicOrchestrator#2 (with EqualsMatrix) done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms (validated=" + validated.size() + ")");

        t0 = System.nanoTime();
        InlineCacheProfilingHeuristic icHeuristic = new InlineCacheProfilingHeuristic();
        List<InstrumentationDecision> icDecisions = icHeuristic.apply(sug, validated);
        if (!icDecisions.isEmpty()) {
            List<InstrumentationDecision> withInlineCache = new ArrayList<>(validated);
            withInlineCache.addAll(icDecisions);
            validated = withInlineCache;
            System.out.println("[string-analysis] INLINE_CACHE entries = " + icHeuristic.getInlineCacheCount());
        }
        System.out.println("[string-analysis-timing] InlineCacheHeuristic+merge done: " + ((System.nanoTime() - t0) / 1_000_000) + "ms");

        int trueRawCount = singleByteDecisions.size() + stringViewDecisions.size() +
                        lazyConcatDecisions.size() + accumulatorDecisions.size() +
                        equalsMatrixDecisions.size();

        StringAnalysisResults results = new StringAnalysisResults(
                        validated,
                        trueRawCount,
                        validated.size(),
                        orchestrator.getConflicts().size(), // one per rejected decision (see getConflictCount)
                        orchestrator.getPrecedenceSuppressed().size());
        StringAnalysisResults.setInstance(results);

        SugAnalysisContext sac = new SugAnalysisContext(results, sug, propagator,
                        singleByte, singleByteDecisions,
                        stringView, stringViewDecisions,
                        lazyConcat, lazyConcatDecisions,
                        accumulator, accumulatorDecisions,
                        equalsMatrix, equalsMatrixDecisions,
                        orchestrator, validated, icHeuristic.getLazyOperandPairing());
        sac.icHeuristic = icHeuristic;
        return sac;
    }

    /**
     * Print-only (lc.mintlog): the {@code [lc-mintlog] child} prediction is printed by the LS heuristic before the
     * orchestrator may withdraw the decision; one {@code withdrawn} line per predicted LAZY_CONCAT decision missing from
     * the validated set, so predicted minus withdrawn = what the profile lists.
     */
    private static void printWithdrawnMints(List<InstrumentationDecision> predicted, List<InstrumentationDecision> validated) {
        Set<String> kept = new java.util.HashSet<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.LAZY_CONCAT && d.getCandidate().getSourceLocation() != null) {
                kept.add(d.getCandidate().getSourceLocation());
            }
        }
        List<String> lines = new ArrayList<>();
        for (InstrumentationDecision d : predicted) {
            String loc = d.getCandidate().getSourceLocation();
            if (d.getType() == OptimizationType.LAZY_CONCAT && loc != null && !kept.contains(loc)) {
                lines.add("[lc-mintlog] withdrawn " + loc + " variant=" + d.getVariant() + " minted=" + LazyConcatMint.mintedRep(d.getCandidate(), d.getVariant()));
            }
        }
        Collections.sort(lines);
        lines.forEach(System.out::println);
    }

    /**
     * The no-usage detector (candidates with no usage of any kind; they are admitted):
     * a census line and one sorted line per candidate in the child log.
     */
    private static void printNoUsageWarnings(List<String> sb, List<String> sv, List<String> lc, List<String> acc) {
        List<String> all = new ArrayList<>();
        all.addAll(sb);
        all.addAll(sv);
        all.addAll(lc);
        all.addAll(acc);
        Collections.sort(all);
        for (String w : all) {
            System.out.println("[string-analysis-nousage] " + w.replaceFirst("^WARNING V[0-9]+ ", "WARNING "));
        }
        System.out.println("[string-analysis-nousage] census warnings=" + all.size() + " singleByte=" + sb.size() + " stringView=" + sv.size() + " lazyConcat=" + lc.size() +
                        " accumulator=" + acc.size() + " (admitted)");
    }

    /** The per-family decision lists the orchestrator sees (factored out to be pinned by JUnit). */
    record OrchestratorInputs(List<InstrumentationDecision> sb, List<InstrumentationDecision> sv, List<InstrumentationDecision> lc,
                    List<InstrumentationDecision> acc) {
    }

    /**
     * The mode filter: a single-family mode hands the orchestrator only the decisions of the families it mints, so the
     * profile never names a rep (an INLINE_CACHE variant, an EQUALS_MATRIX REDIRECT) the parent cannot mint in that mode.
     * SBS mode seeds every user substring (its length is unknown at seed time), so the other heuristics can mint
     * decisions there; SBS keeps SINGLE_BYTE only.
     */
    static OrchestratorInputs orchestratorInputs(boolean svOnly, boolean lcOnly, boolean sbOnly, List<InstrumentationDecision> sb,
                    List<InstrumentationDecision> sv, List<InstrumentationDecision> lc, List<InstrumentationDecision> acc) {
        List<InstrumentationDecision> none = Collections.emptyList();
        if (svOnly) {
            return new OrchestratorInputs(none, sv, none, acc);
        } else if (lcOnly) {
            // The accumulator's LAZY_CONCAT decisions (the StringJoiner extractions) count as LS
            return new OrchestratorInputs(none, none, lc, acc.stream().filter(d -> d.getType() == OptimizationType.LAZY_CONCAT).collect(Collectors.toList()));
        } else if (sbOnly) {
            return new OrchestratorInputs(sb, none, none, none);
        }
        return new OrchestratorInputs(sb, sv, lc, acc);
    }

    private static Set<SugVertex> collectCustomRepCandidates(List<InstrumentationDecision> validated) {
        Set<SugVertex> candidates = new HashSet<>();
        for (InstrumentationDecision d : validated) {
            OptimizationType t = d.getType();
            if (t == OptimizationType.SINGLE_BYTE || t == OptimizationType.STRING_VIEW || t == OptimizationType.LAZY_CONCAT) {
                candidates.add(d.getCandidate());
            }
        }
        return candidates;
    }

    /**
     * The reps hard-code the Latin-1 coder (SingleByteString, StringView, the lazy reps, RepParts; SingleByteString's
     * exact-String equals arm compares coders), which is the JDK's representation only with compact strings. The image's
     * {@code String.COMPACT_STRINGS} is the builder's value (a build-time constant), so a build with reps requires it true
     * and fails here otherwise. Nothing in the emitted code tests it.
     */
    @Override
    public void afterRegistration(AfterRegistrationAccess access) {
        requireCompactStrings(SubstrateOptions.StringAnalysis.getValue() || SubstrateOptions.StringRepProfile.getValue() != null, builderCompactStrings());
        if (SubstrateOptions.StringAnalysis.getValue()) {
            requireLazyOperandMode(Integer.getInteger("svm.stringanalysis.lc.lazyoperand", LazyConcatHeuristic.DEFAULT_LAZY_OPERAND_MODE));
        }
    }

    /**
     * A clean build error for an out-of-range {@code -Dsvm.stringanalysis.lc.lazyoperand}, before
     * {@code LazyConcatHeuristic}'s static initializer fails with an ExceptionInInitializerError (must not initialize that
     * class; {@code DEFAULT_LAZY_OPERAND_MODE} is a compile-time constant, so reading it does not).
     */
    static void requireLazyOperandMode(int v) {
        if (v < 0 || v > 3) {
            throw UserError.abort("-Dsvm.stringanalysis.lc.lazyoperand must be 0, 1, 2 or 3, but is %d.", v);
        }
    }

    static boolean builderCompactStrings() {
        Boolean v = ReflectionUtil.readStaticField(String.class, "COMPACT_STRINGS");
        return v;
    }

    static void requireCompactStrings(boolean repsEnabled, boolean compactStrings) {
        if (repsEnabled && !compactStrings) {
            throw UserError.abort("The String representations of -H:+StringAnalysis / -H:StringRepProfile require compact strings, " +
                            "but the image builder runs with String.COMPACT_STRINGS = false (-J-XX:-CompactStrings). " +
                            "Remove -J-XX:-CompactStrings or build without -H:+StringAnalysis and -H:StringRepProfile.");
        }
    }

    @Override
    public void registerGraphBuilderPlugins(Providers providers, Plugins plugins, ParsingReason reason) {
        boolean enabled = SubstrateOptions.StringAnalysis.getValue();
        boolean fork = SubstrateOptions.StringAnalysisFork.getValue();
        /*
         * An image without string analysis and without a profile (OFF) binds String calls at parse time as stock does
         * with a final String (prepended, so the other node plugins see only the bound form, as in stock). Analysis parse
         * only, behind OffStringFinalBindingPlugin.appliesToThisBuild.
         */
        if (!OffStringFinalBindingPlugin.registerIfApplies(reason, OffStringFinalBindingPlugin::appliesToThisBuild, plugins)) {
            /* The same binding in a parent whose profile admits no rep (gated per invoke, ZeroAdmitStock) */
            OffStringFinalBindingPlugin.registerZeroAdmitIfApplies(reason, OffStringFinalBindingPlugin::appliesToZeroAdmitThisBuild, plugins);
        }
        if (reason == ParsingReason.PointsToAnalysis || (reason == ParsingReason.JITCompilation && RuntimeCompilation.isEnabled())) {
            /*
             * The stock appendChars(..., String, ...) in OFF/zero-admit images, the ranged-copy twin elsewhere;
             * with runtime compilation the twin everywhere, the runtime-compiled graphs included
             */
            plugins.appendNodePlugin(new RangeCopyRedirectPlugin());
            if (!fork && reason == ParsingReason.PointsToAnalysis) {
                /*
                 * The profile's MIRROR sites lowered to the rep-first chain in the analysis parse: mandatory, a MIRROR line
                 * the plugin cannot lower fails the build. Runtime compilation is not covered: with it, MIRROR lines fail
                 */
                plugins.prependNodePlugin(new AppendMirrorNodePlugin());
            }
        }
        if ((enabled || fork) && reason == ParsingReason.PointsToAnalysis) {
            plugins.appendNodePlugin(new StringAnalysisCapturePlugin());
        }
        /*
         * The replacement plugin must fire during the analysis parse: AOT compilation decodes the encoded analysis graph
         * (CompilationInfo.createGraph + GraphDecoder) instead of re-parsing bytecode, so AOTCompilation plugins never
         * fire for user methods.
         */
        if (reason == ParsingReason.PointsToAnalysis &&
                        (SubstrateOptions.StringAnalysisFork.getValue() ||
                                        !fork) &&
                        (SubstrateOptions.StringRepProfile.getValue() != null ||
                                        RepresentationProfileHolder.hasProfile() ||
                                        SubstrateOptions.StringAnalysis.getValue())) {
            plugins.appendNodePlugin(new StringRepresentationReplacementPlugin());
            if (!fork) {
                plugins.appendNodePlugin(new InlineCacheTrivialMethodNodePlugin());
                plugins.appendNodePlugin(new EqualsMatrixNodePlugin());
                if (TypeCheckIcNodePlugin.MODE != 0) {
                    plugins.appendNodePlugin(new TypeCheckIcNodePlugin()); // type-check IC (analysis parse; encoded for AOT)
                }
            }
        }
        if (enabled && !fork && reason == ParsingReason.PointsToAnalysis) {
            boolean svOnly = SubstrateOptions.StringAnalysisStringViewOnly.getValue();
            boolean lsOnly = SubstrateOptions.StringAnalysisLazyConcatOnly.getValue();
            boolean sbOnly = SubstrateOptions.StringAnalysisSingleByteOnly.getValue();
            boolean handleStringView = svOnly || (!sbOnly && !lsOnly);
            boolean handleLazyReps = lsOnly || (!sbOnly && !svOnly);
            StringLengthPluginRegistration.register(plugins, handleStringView, handleLazyReps);
        }
        if (enabled && !fork && reason == ParsingReason.AOTCompilation) {
            boolean svOnly = SubstrateOptions.StringAnalysisStringViewOnly.getValue();
            boolean lsOnly = SubstrateOptions.StringAnalysisLazyConcatOnly.getValue();
            boolean sbOnly = SubstrateOptions.StringAnalysisSingleByteOnly.getValue();
            boolean handleStringView = svOnly || (!sbOnly && !lsOnly);
            boolean handleLazyReps = lsOnly || (!sbOnly && !svOnly);
            plugins.appendNodePlugin(new InlineCacheTrivialMethodNodePlugin(false));
            StringLengthPluginRegistration.register(plugins, handleStringView, handleLazyReps);
        }
    }

    @Override
    public void registerInvocationPlugins(Providers providers, Plugins plugins, ParsingReason reason) {
        boolean enabled = SubstrateOptions.StringAnalysis.getValue();
        boolean fork = SubstrateOptions.StringAnalysisFork.getValue();
        if (reason == ParsingReason.PointsToAnalysis || reason == ParsingReason.AOTCompilation) {
            SingleByteStringPoolPluginRegistration.register(plugins); // the unchecked exact pool read
        }
        if (enabled && (reason == ParsingReason.PointsToAnalysis || reason == ParsingReason.AOTCompilation)) {
            StringEqualsPluginRegistration.register(plugins, fork);
        }
        if (enabled && !fork && (reason == ParsingReason.PointsToAnalysis || reason == ParsingReason.AOTCompilation)) {
            RepEqualsPluginRegistration.register(plugins);
        }
    }

    @Override
    public void beforeAnalysis(BeforeAnalysisAccess access) {
        saProcessStartNanos = System.nanoTime();
        saBeforeAnalysisStartNanos = saProcessStartNanos;
        InlineCacheTrivialMethodNodePlugin.resetCensus(); // the census counts one build
        TypeCheckIcNodePlugin.resetCensus(); // type-check IC census, per build
        System.out.println("[string-analysis-timing] beforeAnalysis start: 0ms (process start)");
        waitForForkedProfile();
        loadRepresentationProfile();
        if (com.oracle.svm.core.stringrep.RepConcat.COUNT && RepresentationProfileHolder.hasProfile() && !RepresentationProfileHolder.getInstance().getConcatCopy().isEmpty()) {
            // Diagnostic (svm.stringanalysis.repconcat.count, default off): the RepConcat path counts at exit
            com.oracle.svm.core.jdk.RuntimeSupport.getRuntimeSupport().addShutdownHook(com.oracle.svm.core.stringrep.RepConcat.countHook());
        }
        ExtraRootsDiscovery.registerExtraRoots(access);
        saBeforeAnalysisDoneNanos = System.nanoTime();
        System.out.println("[string-analysis-timing] beforeAnalysis done: " + ((saBeforeAnalysisDoneNanos - saProcessStartNanos) / 1_000_000) + "ms");
    }

    @Override
    public void afterAnalysis(AfterAnalysisAccess access) {
        if (OffStringFinalBindingPlugin.registered || (ZeroAdmitStock.USED.get() && OffStringFinalBindingPlugin.ENABLED)) {
            /* Soundness: the parse-time String binding needs a String without instantiated subtypes */
            System.out.println(OffStringFinalBindingPlugin.censusLine());
            FeatureImpl.AfterAnalysisAccessImpl a = (FeatureImpl.AfterAnalysisAccessImpl) access;
            OffStringFinalBindingPlugin.checkNoInstantiatedStringSubtype(a.getUniverse().getTypes(), a.getMetaAccess().lookupJavaType(String.class),
                            com.oracle.graal.pointsto.meta.AnalysisType::isInstantiated);
        }
        if (InlineCacheTrivialMethodNodePlugin.EXACT_FIRST_SUPER_CHECK != 0 && RepresentationProfileHolder.hasProfile() &&
                        ((FeatureImpl.AfterAnalysisAccessImpl) access).getBigBang() instanceof PointsToAnalysis pta) {
            /* Debug probe: the parent's points-to state at every D1Check site (exact-first super check) */
            ExactReceiverSites.parentCheckLines(pta, pta.getUniverse()).forEach(System.out::println);
        }
        saAfterAnalysisStartNanos = System.nanoTime();
        long gapMs = (saBeforeAnalysisDoneNanos > 0) ? ((saAfterAnalysisStartNanos - saBeforeAnalysisDoneNanos) / 1_000_000) : -1;
        System.out.println("[string-analysis-timing] afterAnalysis start: " + ((saAfterAnalysisStartNanos - saProcessStartNanos) / 1_000_000) + "ms (gap since beforeAnalysis done: " + gapMs + "ms)");
        if (!SubstrateOptions.StringAnalysis.getValue()) {
            return;
        }
        if (!SubstrateOptions.StringAnalysisFork.getValue()) {
            return;
        }
        try {
            runAnalysis(access);
        } catch (Throwable t) {
            System.err.println("[string-analysis] Analysis failed, continuing build: " + t);
            t.printStackTrace(System.err);
        }
        System.out.println("[string-analysis-timing] afterAnalysis done: " + ((System.nanoTime() - saProcessStartNanos) / 1_000_000) + "ms total");
    }

    /** The zero-cost exact filter: the marked-guard counters, after StrengthenGraphs. */
    @Override
    public void beforeCompilation(BeforeCompilationAccess access) {
        if (InlineCacheTrivialMethodNodePlugin.EXACT_PI || InlineCacheTrivialMethodNodePlugin.EMITTED_ACC.get() > 0) {
            System.out.println(InlineCacheTrivialMethodNodePlugin.trustedFilterSummary());
        }
        if (RepresentationProfileHolder.hasProfile()) {
            System.out.println(InlineCacheTrivialMethodNodePlugin.widenSummary());
            System.out.println(InlineCacheTrivialMethodNodePlugin.flatStockSummary());
            System.out.println(InlineCacheTrivialMethodNodePlugin.codegenKnobSummary());
            System.out.println(InlineCacheTrivialMethodNodePlugin.csfinalSummary()); // print-only
            // The profile's CONCAT_COPY sites and the indy parses lowered with RepConcat (print-only)
            System.out.println("[string-analysis] concat-copy: sites=" + RepresentationProfileHolder.getInstance().getConcatCopy().size() + " lowered-parses=" +
                            StringRepresentationReplacementPlugin.concatCopyLowered.get() + " count.diag=" + com.oracle.svm.core.stringrep.RepConcat.COUNT);
            System.out.println(AppendMirrorNodePlugin.summary()); // print-only
            System.out.println(TypeCheckIcNodePlugin.summary()); // type-check IC (print-only)
        }
        /* Rep-arm dispatch nodes do not count in the post-analysis trivial-method test (profile images only) */
        RepDispatchAccounting.constantReflection = ((FeatureImpl.BeforeCompilationAccessImpl) access).getRuntimeConfiguration().getProviders().getConstantReflection();
        RepDispatchAccounting.active = RepresentationProfileHolder.hasProfile();
    }

    /** The trivial-inliner discount census (profile images only). */
    @Override
    public void afterCompilation(AfterCompilationAccess access) {
        if (RepresentationProfileHolder.hasProfile()) {
            System.out.println(RepDispatchAccounting.censusLine());
        }
    }

    /** No custom string representation object is in the image heap except a rep class's own static pool (fails the build). */
    @Override
    public void afterHeapLayout(AfterHeapLayoutAccess access) {
        RepTypeChecks.printClinitSimulationRepAborts();
        RepTypeChecks.checkImageHeap(((FeatureImpl.AfterHeapLayoutAccessImpl) access).getHeap());
    }

    private void loadRepresentationProfile() {
        String profilePath = SubstrateOptions.StringRepProfile.getValue();
        if (profilePath != null) {
            try {
                RepresentationProfile profile = RepresentationProfileLoader.load(profilePath);
                RepresentationProfileHolder.setInstance(profile);
                System.out.println("[string-rep-profile] Loaded " + profile.getTotalCount() + " entries from " + profilePath);
            } catch (Exception e) {
                throw new RuntimeException("Failed to load string representation profile from " + profilePath, e);
            }
        }
    }

    private void waitForForkedProfile() {
        if (!StringAnalysisForkSupport.forkStarted()) {
            return;
        }
        Path profilePath = StringAnalysisForkSupport.getProfilePath();
        Process child = StringAnalysisForkSupport.getChildProcess();
        long timeoutMs = SubstrateOptions.StringAnalysisForkTimeout.getValue() * 1000L;
        long deadline = System.currentTimeMillis() + timeoutMs;
        System.out.println("[string-analysis-fork] Waiting for child profile: " + profilePath);
        boolean ready = false;
        while (System.currentTimeMillis() < deadline) {
            try {
                if (Files.exists(profilePath)) {
                    long size = Files.size(profilePath);
                    if (size > 0) {
                        ready = true;
                        break;
                    }
                    if (child != null && !child.isAlive() && child.exitValue() == 0) {
                        ready = true;
                        break;
                    }
                }
            } catch (java.nio.file.NoSuchFileException e) {
            } catch (IOException e) {
                System.out.println("[string-analysis-fork] Error checking profile file " + profilePath + ": " + e + "; retrying.");
            }
            if (child != null && !child.isAlive() && child.exitValue() == 0) {
                try {
                    Process rerun = StringAnalysisForkSupport.rerunIfRequested(); // the objret=0 rerun, if requested
                    if (rerun != null) {
                        child = rerun;
                        // The rerun gets its own deadline (else a timeout drops silently to no profile)
                        deadline = System.currentTimeMillis() + timeoutMs;
                        System.out.println("[objret-rerun] the rerun's deadline re-armed: " + timeoutMs / 1000 + "s from now");
                        continue;
                    }
                } catch (IOException e) {
                    System.out.println("[objret-rerun] failed to start the rerun: " + e);
                }
            }
            if (child != null && !child.isAlive()) {
                int exit = child.exitValue();
                if (exit != 0) {
                    System.out.println("[string-analysis-fork] Child exited with error code " + exit + "; proceeding without forked profile.");
                    return;
                }
                if (!Files.exists(profilePath)) {
                    System.out.println("[string-analysis-fork] Child exited 0 but produced no profile; proceeding without.");
                    return;
                }
            }
            try {
                Thread.sleep(500);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                System.out.println("[string-analysis-fork] Interrupted while waiting for child profile; proceeding without.");
                return;
            }
        }
        if (!ready) {
            System.out.println("[string-analysis-fork] Timeout after " + (timeoutMs / 1000) + "s waiting for child profile; proceeding without forked profile.");
            return;
        }
        try {
            RepresentationProfile profile = RepresentationProfileLoader.load(profilePath.toString());
            RepresentationProfileHolder.setInstance(profile);
            System.out.println("[string-analysis-fork] Loaded " + profile.getTotalCount() + " entries from child profile: " + profilePath);
        } catch (Exception e) {
            System.out.println("[string-analysis-fork] Failed to load child profile from " + profilePath + ": " + e + "; proceeding without.");
        } finally {
            try {
                if (SubstrateOptions.StringAnalysisKeepProfile.getValue()) {
                    System.out.println("[string-analysis-fork] KeepProfile: profile retained at " + profilePath);
                } else {
                    Files.deleteIfExists(profilePath);
                }
            } catch (IOException ignored) {
            }
        }
    }

    /**
     * Pure (JUnit): at one profile key the later decision {@code next} replaces the kept one iff the kept one is a
     * stack-confined {@code ACCUMULATOR_VIEW_SHARED} and {@code next} is the stored {@code ACCUMULATOR_VIEW}: SHARED is
     * the memory-retention relaxation, so a duplicate vertex that was stored must keep the occupancy check. Every other
     * conflict keeps the first.
     */
    static boolean storedAccumulatorWins(String keptVariant, String nextVariant) {
        return AccumulatorHeuristic.ACCUMULATOR_VIEW_SHARED.equals(keptVariant) && "ACCUMULATOR_VIEW".equals(nextVariant) ||
                        keptVariant == null && StringViewHeuristic.STORED.equals(nextVariant); // a stored substring wins too
    }

    public static void dumpProfile(List<InstrumentationDecision> decisions, String path) {
        dumpProfile(decisions, path, List.of());
    }

    /** {@code extraLines} (the per-site side lines: lazy pairs, concat copy, mirror, exact-receiver, flat delivery) go after the decisions. */
    public static void dumpProfile(List<InstrumentationDecision> decisions, String path, List<String> extraLines) {
        long dpStart = System.nanoTime();
        int count = 0;
        Map<String, InstrumentationDecision> seen = new LinkedHashMap<>();
        for (InstrumentationDecision d : decisions) {
            if (d.getType() == OptimizationType.NONE) {
                continue;
            }
            String source = d.getSourceLocation();
            String key = source + "\0" + d.getType().name();
            InstrumentationDecision first = seen.get(key);
            if (first != null) {
                if (!java.util.Objects.equals(first.getVariant(), d.getVariant())) {
                    // At one key a stored accumulator decision wins over a SHARED one, whatever
                    // the order (two SUG vertices can share one class#method@bci key)
                    InstrumentationDecision keep = storedAccumulatorWins(first.getVariant(), d.getVariant()) ? d : first;
                    InstrumentationDecision skip = keep == d ? first : d;
                    System.err.println("[string-analysis] Conflicting decisions at " + source +
                                    ": keeping " + keep.getType() + (keep.getVariant() != null ? " " + keep.getVariant() : "") +
                                    ", skipping " + skip.getType() + (skip.getVariant() != null ? " " + skip.getVariant() : ""));
                    seen.put(key, keep); // an existing key keeps its position
                }
                continue;
            }
            seen.put(key, d);
        }
        Path out = Paths.get(path);
        Path tmp = Paths.get(path + ".tmp");
        try (BufferedWriter writer = Files.newBufferedWriter(tmp, StandardCharsets.UTF_8)) {
            for (InstrumentationDecision d : seen.values()) {
                if (d.getSourceLocation() == null) {
                    continue;
                }
                writer.write(d.getSourceLocation());
                writer.write(" ");
                writer.write(d.getType().name());
                if (d.getVariant() != null) {
                    writer.write(" ");
                    writer.write(d.getVariant());
                    if (d.getAccumulatorClass() != null) {
                        writer.write(" ");
                        writer.write(d.getAccumulatorClass());
                    }
                }
                writer.newLine();
                count++;
            }
            for (String extra : extraLines) {
                writer.write(extra);
                writer.newLine();
            }
        } catch (IOException e) {
            try {
                Files.deleteIfExists(tmp);
            } catch (IOException suppressed) {
                e.addSuppressed(suppressed);
            }
            throw new RuntimeException("Failed to dump string analysis profile to " + path, e);
        }
        try {
            Files.move(tmp, out, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            try {
                Files.deleteIfExists(tmp);
            } catch (IOException suppressed) {
                e.addSuppressed(suppressed);
            }
            throw new RuntimeException("Failed to atomically move string analysis profile from " + tmp + " to " + path, e);
        }
        System.out.println("[string-analysis] Dumped " + count + " profile entries to " + path);
        System.out.println("[string-analysis-timing] dumpProfile done: " + ((System.nanoTime() - dpStart) / 1_000_000) + "ms");
    }

    private void runAnalysis(AfterAnalysisAccess access) {
        FeatureImpl.AfterAnalysisAccessImpl impl = (FeatureImpl.AfterAnalysisAccessImpl) access;
        BigBang bb = impl.getBigBang();
        AnalysisUniverse universe = impl.getUniverse();
        // The analysis child's universe is rep-free (rtypes=unreachable)
        RepTypeChecks.recordChildRepTypes(universe);

        long sugStart = System.nanoTime();
        SugAnalysisContext ctx = buildSugAndRunHeuristics(bb, universe, CAPTURED);
        System.out.println("[string-analysis-timing] buildSugAndRunHeuristics done: " + ((System.nanoTime() - sugStart) / 1_000_000) + "ms");
        StringAnalysisResults results = ctx.results;
        HeuristicOrchestrator orchestrator = ctx.orchestrator;
        List<InstrumentationDecision> validated = ctx.validated;

        String dumpPath = SubstrateOptions.StringAnalysisDumpProfile.getValue();
        if (dumpPath != null) {
            List<InstrumentationDecision> toDump = validated;
            if (SubstrateOptions.StringAnalysisStringViewOnly.getValue()) {
                toDump = validated.stream().filter(d -> d.getType() == OptimizationType.STRING_VIEW || d.getType() == OptimizationType.EQUALS_MATRIX || d.getType() == OptimizationType.INLINE_CACHE)
                                .collect(Collectors.toList());
            } else if (SubstrateOptions.StringAnalysisSingleByteOnly.getValue()) {
                toDump = validated.stream().filter(d -> d.getType() == OptimizationType.SINGLE_BYTE || d.getType() == OptimizationType.EQUALS_MATRIX || d.getType() == OptimizationType.INLINE_CACHE)
                                .collect(Collectors.toList());
            } else if (SubstrateOptions.StringAnalysisLazyConcatOnly.getValue()) {
                toDump = validated.stream().filter(d -> d.getType() == OptimizationType.LAZY_CONCAT || d.getType() == OptimizationType.EQUALS_MATRIX || d.getType() == OptimizationType.INLINE_CACHE)
                                .collect(Collectors.toList());
            }
            // KT precision: the inner/outer pairs of the lazy operands whose kind the concat group does not list; the
            // pairs of the IC-time computation (one computation for the listing and the pairs)
            List<String> extraLines = new ArrayList<>(LazyOperandPairing.dumpLines(ctx.lazyOperandPairing, toDump));
            // The copying concat sites a dumped String View reaches (the parent lowers them with RepConcat)
            List<String> concatCopy = StringViewHeuristic.concatCopyLines(ctx.sug, toDump);
            System.out.println("[sug-concat-copy] sites=" + concatCopy.size() + " " + concatCopy);
            extraLines.addAll(concatCopy);
            // The mirrored builder entry-point sites an admitted value-null rep reaches as the string argument
            AppendMirror.Emission am = AppendMirror.emit(ctx.sug, toDump);
            am.logLines().forEach(System.out::println);
            extraLines.addAll(am.profileLines());
            if (bb instanceof PointsToAnalysis pta) {
                // The rep-list supertype sites whose receiver state is exactly {String} (stock devirtualizes them)
                ExactReceiverSites.Emission xr = ExactReceiverSites.compute(pta, universe, toDump, RepTypeChecks.childRepTypesUnreachable(), RepTypeChecks.childRepTypesStatus());
                xr.logLines().forEach(System.out::println);
                extraLines.addAll(xr.profileLines());
            }
            // Flat delivery: the flat hand-off members left undelivered for admitted SINGLE_BYTE seeds
            Set<String> admittedSb = new java.util.HashSet<>();
            for (InstrumentationDecision d : toDump) {
                if (d.getType() == OptimizationType.SINGLE_BYTE && d.getCandidate().getSourceLocation() != null) {
                    admittedSb.add(d.getCandidate().getSourceLocation());
                }
            }
            List<String> undelivered = RecursiveTracking.flatUndeliveredProfileLines(admittedSb);
            System.out.println(RecursiveTracking.flatUndeliveredCensus() + " admitted-SB lines=" + undelivered);
            extraLines.addAll(undelivered);
            if (bb instanceof PointsToAnalysis pta && ctx.icHeuristic != null) {
                // Type-check IC: the checkcast/instanceof String sites with the IC receiver rule (observations only)
                TypeCheckSites.Emission tc = TypeCheckSites.compute(pta, universe, ctx.sug, ctx.icHeuristic, undelivered);
                tc.logLines().forEach(System.out::println);
                extraLines.addAll(tc.profileLines());
            }
            if (StringAnalysisForkSupport.objretRerunRequested() && SubstrateOptions.StringAnalysisFork.getValue()) {
                // Rule U was active and the evaluation guard tripped: no profile, the marker asks the driver
                // for the objret=0 rerun (whose profile is the one used)
                try {
                    Files.writeString(StringAnalysisForkSupport.rerunMarker(Path.of(dumpPath)), "EVALUATION_GUARD\n");
                    System.out.println("[objret-rerun] reason=EVALUATION_GUARD: no profile written; marker " + StringAnalysisForkSupport.rerunMarker(Path.of(dumpPath)));
                } catch (IOException e) {
                    throw new RuntimeException("[objret-rerun] cannot write the rerun marker", e);
                }
            } else {
                dumpProfile(toDump, dumpPath, extraLines);
            }
        }

        long reportsStart = System.nanoTime();
        InstrumentationReport report = new InstrumentationReport(results, orchestrator.getConflicts());

        System.out.println("[string-analysis] raw=" + results.getRawCandidateCount() +
                        " validated=" + validated.size() +
                        " conflicts=" + orchestrator.getConflicts().size() +
                        " precedence_suppressed=" + orchestrator.getPrecedenceSuppressed().size());

        Path reportsPath = NativeImageGenerator.generatedFiles(HostedOptionValues.singleton()).resolve("reports");
        ReportUtils.report("string analysis report (filtered)", reportsPath.resolve("string_analysis_report_filtered.txt"),
                        writer -> writer.write(StringAnalysisDiagnostics.reportFiltered(report, validated, SubstrateOptions.StringAnalysisDumpFilter.getValue())));
        ReportUtils.report("string analysis report (full)", reportsPath.resolve("string_analysis_report_full.txt"),
                        writer -> writer.write(report.dumpMachineReadable()));
        ReportUtils.report("string analysis diagnostics", reportsPath.resolve("string_analysis_diagnostics.txt"),
                        writer -> writer.write(StringAnalysisDiagnostics.buildDiagnostics(ctx.sug, ctx.propagator, ctx.singleByte, ctx.singleByteDecisions,
                                        ctx.stringView, ctx.stringViewDecisions, ctx.lazyConcat, ctx.lazyConcatDecisions,
                                        ctx.accumulator, ctx.accumulatorDecisions, ctx.equalsMatrix, ctx.equalsMatrixDecisions,
                                        orchestrator, validated, report)));
        int dotVertexCap = 100_000;
        if (ctx.sug.getVertices().size() < dotVertexCap) {
            ReportUtils.report("string utilization graph (filtered)", reportsPath.resolve("sug_filtered.dot"),
                            writer -> writer.write(ctx.sug.dumpDotFiltered(SubstrateOptions.StringAnalysisDumpFilter.getValue())));
            ReportUtils.report("string utilization graph (full)", reportsPath.resolve("sug_full.dot"),
                            writer -> writer.write(ctx.sug.dumpDot()));
        } else {
            System.out.println("[string-analysis] Skipping DOT dump (graph too large: " + ctx.sug.getVertices().size() + " vertices >= cap " + dotVertexCap + ")");
        }
        System.out.println("[string-analysis-timing] reportWriting done: " + ((System.nanoTime() - reportsStart) / 1_000_000) + "ms");
    }

}
