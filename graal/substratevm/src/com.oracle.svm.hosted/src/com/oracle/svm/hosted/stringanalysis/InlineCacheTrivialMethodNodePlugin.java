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

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import com.oracle.svm.core.graal.snippets.DeoptHostedSnippets;
import com.oracle.svm.core.nodes.SubstrateMethodCallTargetNode;

import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.GraalError;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.AbstractBeginNode;
import jdk.graal.compiler.nodes.AbstractMergeNode;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.FixedGuardNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.spi.SimplifierTool;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.vm.ci.meta.DeoptimizationAction;
import jdk.vm.ci.meta.DeoptimizationReason;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.meta.SpeculationLog;

/**
 * The inline-cache node plugin for the trivial String methods ({@link #TRIVIAL_METHODS}). Fires only at invokes whose
 * declaring class is exactly {@code java.lang.String}, keyed by the site's {@code INLINE_CACHE} profile entry.
 * {@code UNKNOWN} and {@code EXACT_STRING} are both a proof of rep-freeness (the trust principle: a rep receiver would
 * have been tracked and tagged), so both emit one direct ({@code InvokeKind.Special}) call to {@code String.<m>} instead
 * of a decline (stock: a vtable call at polluted cones). The direct target then reaches the most-lowered form: decoder
 * inlining of the trivial body, or Graal's parse-time invocation plugins, which {@link #emitFlatCall} applies by
 * emitting the flat call through the parser's own invoke path ({@code StringEqualsInvocationPlugin} is parser-only; it
 * has no {@code getClass} guard and reads the argument's {@code value}/{@code coder}). Its soundness rests on the premise
 * "no {@code EQUALS_MATRIX REDIRECT} entry ⇒ the equals argument is rep-free": a rep argument would have produced a
 * REDIRECT entry (or the walk refuses with {@code EQUALS_ARG_NO_SITE}). This premise is the only defence at every
 * non-REDIRECT IC {@code equals}; {@code ic.flatstock=2} checks it at run time ({@link #FLAT_STOCK_MODE}). Claiming the
 * node pre-empts {@code StringLengthNodePlugin} at {@code length} sites, which is equivalent (the same field math).
 * <p>
 * At a site with a rep-list variant every branch is direct: one {@code getClass() == RepX.class} branch per listed rep
 * that overrides {@code <m>} (a special-invoke {@code RepX.<m>}), no String branch, and a direct {@code String.<m>}
 * else (the {@code directElse} form). The rep list is exhaustive by the refusal discipline, so the else sees exactly
 * plain Strings and non-overriding reps, and every non-overriding rep is flat by invariant (a real backing array; only
 * {@code SingleByteString} inherits any trivial method, pinned by {@code ElseDirectPremiseTest}), so the inherited
 * body is correct on it. A list with no overriding rep collapses to one direct call. A non-redirect {@code equals} else
 * stays plain {@code String.equals}: no REDIRECT means the argument is rep-free, so the stock intrinsic is exact.
 * <p>
 * Always-virt ({@code StringAnalysisPolicy.alwaysVirtJdkTrivialApplies}): at a site whose enclosing method is a
 * terminal body ({@code StringAnalysisPolicy.isTerminalBodyClass}) this plugin makes no claim. The site
 * rides the stock pipeline (virtual, or devirtualized only where stock points-to recovers it, which is rep-safe since a
 * rep in the sound cone suppresses single-callee devirtualization). Wrong-UNKNOWN entries arise in that population (the
 * concat machinery, the valueOf model's result drop); user-code sites are unaffected. At a REDIRECT site in that scope
 * the decline falls to {@link EqualsMatrixNodePlugin}'s virtual {@code maybeCustomStringEquals} residual.
 * <p>
 * Redirect table: at an {@code EQUALS_MATRIX REDIRECT} site, where the equals invoke is replaced by
 * {@code maybeCustomStringEquals}, this plugin owns the String-declared lowering and follows the receiver's entry
 * (rep-free: one special {@code String.maybeCustomStringEquals}; rep list up to {@link #MAX_REDIRECT_CUSTOM_REPS}: the
 * chain with that call as else). Declining leaves the site to {@link EqualsMatrixNodePlugin}'s virtual residual.
 * Registered for PointsToAnalysis (before that plugin) and for AOTCompilation.
 */
public final class InlineCacheTrivialMethodNodePlugin implements NodePlugin {

    static final String STRING_CLASS = "java.lang.String";

    /*
     * The method set is StringIcMethods, shared by child and parent (every non-private instance method declared by
     * String, by name + descriptor). Per (rep, method): a rep that implements the method gets its own branch; a rep that
     * inherits String's body rides the direct else. That body's correctness on the rep is the rep classes' guarantee,
     * pinned by FlatRepPremiseTest / RepInheritedBodyTest / ValueNullOverrideTest.
     */

    private static final String EXACT_STRING = "EXACT_STRING";
    private static final String UNKNOWN = "UNKNOWN";
    /**
     * Knob {@code svm.stringanalysis.ic.maxreps} (default 5): the rep-list cap at non-REDIRECT sites, kept equal to
     * {@code svm.stringanalysis.orch.maxreceiverreps}. Above it the site declines.
     */
    private static final int MAX_CUSTOM_REPS = Integer.getInteger("svm.stringanalysis.ic.maxreps", 5);

    /** Distinct declined sites per reason, and distinct lowered sites per form (diagnostic only). */
    static final Map<String, Set<String>> DECLINED = new ConcurrentHashMap<>();
    static final Map<String, Set<String>> LOWERED = new ConcurrentHashMap<>();
    /**
     * Print-only census of the condition of a former {@code value-null-inherits} decline: a listed value-null rep that
     * inherits the site's method outside its pinned field-only entry bodies, or inherits {@code compareTo}. Expected 0.
     */
    static final Set<String> VALUE_NULL_INHERITS = ConcurrentHashMap.newKeySet();
    /** Part-B else filters with two or more inheriting-rep arms (site, method, the reps). */
    static final Set<String> MULTI_FLAT_SITES = ConcurrentHashMap.newKeySet();

    private static boolean decline(String reason, String loc, String nd) {
        DECLINED.computeIfAbsent(reason, k -> ConcurrentHashMap.newKeySet()).add(loc + " " + nd);
        return false;
    }

    private static void lowered(String form, String loc, String nd) {
        String f = StringIcMethods.LEGACY_TRIVIAL_NAMES.contains(nd.substring(0, nd.indexOf('('))) || nd.equals(StringIcMethods.GETBYTES_CODER_KEY) ? form : form + "/widened";
        LOWERED.computeIfAbsent(f, k -> ConcurrentHashMap.newKeySet()).add(loc + " " + nd);
    }

    static String widenSummary() {
        StringBuilder sb = new StringBuilder("[string-analysis] ic-widen: maxreps=" + MAX_CUSTOM_REPS + " lowered sites:");
        new java.util.TreeMap<>(LOWERED).forEach((k, v) -> sb.append(' ').append(k).append('=').append(v.size()));
        sb.append("; declined sites:");
        new java.util.TreeMap<>(DECLINED).forEach((k, v) -> sb.append(' ').append(k).append('=').append(v.size()));
        for (String reason : new String[]{"no-entry", "terminal-body-unmarked"}) {
            Set<String> sites = DECLINED.get(reason);
            if (sites != null) {
                Map<String, Integer> byMethod = new java.util.TreeMap<>();
                for (String site : sites) {
                    byMethod.merge(site.substring(site.indexOf(' ') + 1), 1, Integer::sum);
                }
                sb.append("\n[ic-widen-decline-by-method] ").append(reason).append(' ').append(byMethod);
            }
        }
        sb.append("\n[ic-widen-multiflat] Part-B else filters with >=2 flat arms: ").append(MULTI_FLAT_SITES.size());
        sb.append("\n[ic-widen-value-null-inherits] sites (print-only, expected 0): ").append(VALUE_NULL_INHERITS.size());
        return sb.toString();
    }

    /**
     * The rep-list cap at {@code EQUALS_MATRIX REDIRECT} sites (validation skips equals vertices, so their variants can
     * exceed {@link #MAX_CUSTOM_REPS}). 8 guarded class compares are still cheaper than a lost inline; above the cap the
     * plugin declines and {@link EqualsMatrixNodePlugin} applies the sound virtual residual.
     */
    private static final int MAX_REDIRECT_CUSTOM_REPS = 8;

    /**
     * Knob {@code svm.stringanalysis.ic.exactpi}: zero-cost exact filter. Two emitters of {@link #TRUSTED_FILTER}-marked
     * guards exist: this plugin's IC filters (Part A/B below) and the accumulator lowering's {@link #trustedExactFilter},
     * which is emitted in every mode:
     * <ul>
     * <li>0 = no IC filter; accumulator filters are still emitted and removed after points-to as in mode 1. So mode 0
     * does not revert the accumulator filter.</li>
     * <li>1 (default) = marked guards exist only for the points-to analysis;
     * {@code SubstrateStrengthenGraphs.simplifyDelegate} turns them into tautologies, so the run-time code is the direct
     * call with no class check.</li>
     * <li>2 = check mode: every marked guard stays and lowers to a ClassCastException throw (a wrong exact class throws
     * instead of being trusted).</li>
     * </ul>
     * The census ({@link #countTrustedFilters}) runs in modes 1/2, and in mode 0 when an accumulator filter was emitted.
     * <p>
     * Part A: where the receiver domain is exactly plain {@code java.lang.String} by the trust principle (the
     * UNKNOWN/EXACT_STRING directs and the rep-free-receiver mCSE direct) the receiver goes through a marked
     * {@code FixedGuardNode(InstanceOf exact String, null allowed)} + {@code PiNode}: the PTA builder turns the guard into
     * a {@code FilterTypeFlow} (a bare PiNode filters nothing), so {@code String.<m>}'s formal {@code this} stays
     * {@code {String}}. After the analysis the guard becomes a ValueAnchor; the Pi stays (true under the trust principle).
     * <p>
     * Part B (with exactpi != 0): the rep chain
     * dispatches with {@code InstanceOf exact RepX} instead of {@code getClass() == RepX} (the same hub compare; points-to
     * filters each branch), and the else carries an analysis-only filter: for every listed inheriting rep F an empty
     * {@code if (x instanceof exact F)} arm holding a marked guard, the final arm a marked exact-String guard, merged
     * before one direct {@code String.<m>(x)}. Points-to sees the else receiver as {String} + {listed inheriting reps};
     * afterwards the guards go and the Ifs fold, leaving a single direct call. No Pi in the else (its domain includes the
     * inheriting reps).
     */
    static final int EXACT_PI_MODE = Integer.getInteger("svm.stringanalysis.ic.exactpi", 1);
    static final boolean EXACT_PI = EXACT_PI_MODE != 0;

    /**
     * Knob {@code svm.stringanalysis.ic.exactfirst} (default 0 = the rep-first chain; 1 = experimental): a rep-list chain
     * tests the exact String class first and sends a plain String straight to the direct String call. With 0, the
     * rep-arm profile ({@link #repArmProfile}) already lays the plain path out as the fall-through. With 1 the extra test grows callers past
     * the inlining budget and, at exact-receiver super sites, leaves the else to the listed inheriting reps only (dead:
     * a ClassCastException throw).
     */
    static final int EXACT_FIRST = Integer.getInteger("svm.stringanalysis.ic.exactfirst", 0);
    /**
     * Debug only ({@code svm.stringanalysis.ic.exactfirst.super.check}, default 0): at an exact-receiver super site the
     * Part-B else filter is left out and the trusted String narrowing becomes a call of
     * {@code com.oracle.svm.core.stringrep.D1Check.check(receiver, site)}, which fails loudly on a non-String receiver;
     * the parent prints the points-to state of its argument ({@code [d1-check]}, {@link ExactReceiverSites#parentCheckLines}).
     */
    static final int EXACT_FIRST_SUPER_CHECK = Integer.getInteger("svm.stringanalysis.ic.exactfirst.super.check", 0);
    static final AtomicLong EXACT_FIRST_IFS = new AtomicLong();
    static final AtomicLong EMITTED_SUPER_CAST = new AtomicLong();
    static final Set<String> SUPER_SITES = ConcurrentHashMap.newKeySet();
    /** The chain rep-arm {@code If}s emitted (the census, {@link #codegenKnobSummary}). */
    static final AtomicLong REP_ARM_IFS = new AtomicLong();

    /**
     * The profile of the emitted chain rep-arm {@code If}s, counted: every rep test is {@code SLOW_PATH_PROFILE}, so the
     * else (plain Strings and non-overriding reps) is the likely successor. It is the value domain of every String site,
     * while a rep reaches a chain only from admitted creation sites; a likely rep arm would lay the plain String out cold
     * in shared JDK bodies (e.g. {@code AbstractStringBuilder.append(String)}). Only the {@code If} probabilities matter.
     */
    static jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData repArmProfile() {
        REP_ARM_IFS.incrementAndGet();
        return BranchProbabilityNode.SLOW_PATH_PROFILE;
    }

    /**
     * The codegen census of the IC chain and the LC rope factory (counters, plus the two codegen knobs that remain).
     */
    static String codegenKnobSummary() {
        return "[string-analysis] codegen-knobs: chain rep-arm ifs=" + REP_ARM_IFS.get() + " swap sites=" + EqualsMatrixNodePlugin.SWAP_SITES.get() +
                        " xd.rangecopy=" + RangeCopyRedirectPlugin.MODE + " ic.exactfirst=" + EXACT_FIRST + " (exact-first ifs=" + EXACT_FIRST_IFS.get() + ") super sites=" +
                        SUPER_SITES.size() + " super casts=" + EMITTED_SUPER_CAST.get();
    }

    static final String TRUSTED_FILTER_MESSAGE = "string-analysis trusted exact-type filter (analysis-only)";
    /** The marker of the analysis-only guards (identity is not relied on: graphs are re-encoded). */
    static final DeoptHostedSnippets.AnalysisSpeculation TRUSTED_FILTER = new DeoptHostedSnippets.AnalysisSpeculation(
                    new DeoptHostedSnippets.AnalysisSpeculationReason(TRUSTED_FILTER_MESSAGE));

    static final AtomicLong EMITTED_DIRECT = new AtomicLong();
    static final AtomicLong EMITTED_CHAIN_ELSE = new AtomicLong();
    static final AtomicLong EMITTED_CHAIN_FLAT = new AtomicLong();
    /** The marked exact-accumulator-class filters of the unified accumulator lowering (StringRepresentationReplacementPlugin). */
    static final AtomicLong EMITTED_ACC = new AtomicLong();
    static final AtomicLong CHAIN_SITES = new AtomicLong();
    static final AtomicLong AOT_PARSE_SITES = new AtomicLong();
    static final AtomicLong PRESENT_PRE = new AtomicLong();
    static final AtomicLong PRESENT_PRE_INLINED = new AtomicLong();
    static final AtomicLong REMOVED = new AtomicLong();
    static final AtomicLong REMOVED_INLINED = new AtomicLong();
    static final AtomicLong SURVIVING = new AtomicLong();
    static final AtomicLong SURVIVING_INLINED = new AtomicLong();
    /** A marked guard deleted with its dead branch (neither tautologised nor folded). */
    static final AtomicLong KILLED_DEAD = new AtomicLong();
    /** A marked guard whose condition folded to a constant failure (seen at the strengthen visit). */
    static final AtomicLong FOLDED_TO_THROW = new AtomicLong();
    /** Marked-speculation DeoptimizeNodes left after strengthen (the folded guards' throws). */
    static final AtomicLong MARKED_DEOPTS_POST = new AtomicLong();
    /** Part B's analysis-only arm Ifs at strengthen, and those left after it (must be 0). */
    static final AtomicLong PART_B_IFS_PRE = new AtomicLong();
    static final AtomicLong PART_B_IFS_LEFT = new AtomicLong();
    /** The graphs (root methods) whose own parse emitted a marked guard; a guard elsewhere is an inlined copy. */
    static final Set<Object> EMITTING_ROOTS = ConcurrentHashMap.newKeySet();

    /** The census is per build (a hosted JVM may run several); called at the feature's setup. */
    static void resetCensus() {
        for (AtomicLong c : new AtomicLong[]{EMITTED_DIRECT, EMITTED_CHAIN_ELSE, EMITTED_CHAIN_FLAT, EMITTED_ACC, CHAIN_SITES, AOT_PARSE_SITES, PRESENT_PRE, PRESENT_PRE_INLINED,
                        REMOVED, REMOVED_INLINED, SURVIVING, SURVIVING_INLINED, KILLED_DEAD, FOLDED_TO_THROW, MARKED_DEOPTS_POST, PART_B_IFS_PRE, PART_B_IFS_LEFT}) {
            c.set(0);
        }
        FLAT_STOCK_CALLS.set(0);
        FLAT_LEGACY_CALLS.set(0);
        FLAT_NULL_RECEIVER.set(0);
        for (AtomicLong c : new AtomicLong[]{FLAT_CHECK_SITES, FLAT_CHECK_GUARDS, FLAT_CHECK_EXCLUDED, FLAT_CHECK_PRE, FLAT_CHECK_POST}) {
            c.set(0);
        }
        FLAT_CHECK_LEFT_SITES.clear();
        EMITTING_ROOTS.clear();
        GRAPH_CENSUS.clear();
        DECLINED.clear();
        LOWERED.clear();
        MULTI_FLAT_SITES.clear();
        VALUE_NULL_INHERITS.clear();
        for (AtomicLong c : new AtomicLong[]{CSF_DIAMONDS, CSF_GUARDS, CSF_IFS_PRE, CSF_IFS_LEFT, CSF_DEAD_ARMS_PRE, CSF_DEAD_ARMS_FOLDED}) {
            c.set(0);
        }
        CSF_SITES.clear();
        CSF_DIAMONDS_BY_METHOD.clear();
        CSF_IBA_FREE.set(0);
        CSF_BY_DECL.clear();
        CSF_REPLIST_SITES.clear();
        CSF_UNPROVEN_SITES.clear();
        EXACT_FIRST_IFS.set(0);
        EMITTED_SUPER_CAST.set(0);
        SUPER_SITES.clear();
    }

    /**
     * The csfinal diamond's guard has its own reason (still a trusted filter, removed like every marked guard), so the
     * census matches only csfinal diamonds, never a user {@code instanceof} + Part-A guard.
     */
    static final String TRUSTED_FILTER_CSFINAL_MESSAGE = TRUSTED_FILTER_MESSAGE + " csfinal";
    static final DeoptHostedSnippets.AnalysisSpeculation TRUSTED_FILTER_CSFINAL = new DeoptHostedSnippets.AnalysisSpeculation(
                    new DeoptHostedSnippets.AnalysisSpeculationReason(TRUSTED_FILTER_CSFINAL_MESSAGE));

    static boolean isCsfinalSpeculation(SpeculationLog.Speculation s) {
        return s instanceof DeoptHostedSnippets.AnalysisSpeculation && s.getReason() instanceof DeoptHostedSnippets.AnalysisSpeculationReason r &&
                        TRUSTED_FILTER_CSFINAL_MESSAGE.equals(r.getMessage());
    }

    public static boolean isTrustedFilter(FixedGuardNode guard) {
        return isTrustedSpeculation(guard.getSpeculation());
    }

    static boolean isTrustedSpeculation(SpeculationLog.Speculation s) {
        return s instanceof DeoptHostedSnippets.AnalysisSpeculation && s.getReason() instanceof DeoptHostedSnippets.AnalysisSpeculationReason r &&
                        (TRUSTED_FILTER_MESSAGE.equals(r.getMessage()) || TRUSTED_FILTER_CSFINAL_MESSAGE.equals(r.getMessage()));
    }

    /**
     * The per-graph attribution of one strengthen run: every marked guard present before is afterwards exactly one of
     * removed (tautologised, or already a passing constant), folded-to-throw (a failing constant), killed-as-dead (deleted
     * with a dead branch), or surviving. Part B's arm Ifs (an If whose true successor starts with a marked guard on its own
     * condition) are recorded before and counted if left after.
     */
    static final class GraphCensus {
        final List<FixedGuardNode> guards = new ArrayList<>();
        final List<IfNode> partBIfs = new ArrayList<>();
        /** The csfinal rep-exclusion diamonds' analysis-only Ifs (must all fold). */
        final List<IfNode> csfinalIfs = new ArrayList<>();
        final Set<FixedGuardNode> removed = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        final Set<FixedGuardNode> folded = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
    }

    static final Map<StructuredGraph, GraphCensus> GRAPH_CENSUS = java.util.Collections.synchronizedMap(new java.util.IdentityHashMap<>());

    /** SubstrateStrengthenGraphs pre/post hook: record (pre) and attribute (post) the marked guards of one graph. */
    public static void countTrustedFilters(StructuredGraph graph, boolean pre) {
        if (FLAT_STOCK_MODE == 2) {
            // ic.flatstock=2 check: the flat-call equals argument guards present before strengthen and left after it
            for (FixedGuardNode g : graph.getNodes(FixedGuardNode.TYPE)) {
                if (isFlatCheckGuard(g)) {
                    (pre ? FLAT_CHECK_PRE : FLAT_CHECK_POST).incrementAndGet();
                    if (!pre) {
                        String site = ((DeoptHostedSnippets.AnalysisSpeculationReason) g.getSpeculation().getReason()).getMessage().substring(FLAT_CHECK_MESSAGE.length()) +
                                        " in " + (graph.method() == null ? "?" : graph.method().format("%H.%n(%p)")) + " rep " +
                                        (g.getCondition() instanceof InstanceOfNode io ? io.type().getType().toJavaName(false) : "?");
                        FLAT_CHECK_LEFT_SITES.computeIfAbsent(site, k -> new AtomicLong()).incrementAndGet();
                    }
                }
            }
        }
        // Accumulator guards exist in every mode; mode 0 with no accumulator filter skips the census.
        if (!EXACT_PI && EMITTED_ACC.get() == 0) {
            return;
        }
        boolean inlined = graph.method() == null || !EMITTING_ROOTS.contains(graph.method());
        if (pre) {
            GraphCensus gc = null;
            for (FixedGuardNode g : graph.getNodes(FixedGuardNode.TYPE)) {
                if (!isTrustedFilter(g)) {
                    continue;
                }
                if (gc == null) {
                    gc = new GraphCensus();
                }
                gc.guards.add(g);
                PRESENT_PRE.incrementAndGet();
                if (inlined) {
                    PRESENT_PRE_INLINED.incrementAndGet();
                }
                if (g.predecessor() instanceof AbstractBeginNode begin && begin.predecessor() instanceof IfNode ifNode && ifNode.trueSuccessor() == begin &&
                                ifNode.condition() == g.getCondition()) {
                    gc.partBIfs.add(ifNode);
                    PART_B_IFS_PRE.incrementAndGet();
                } else if (isCsfinalIf(g)) {
                    gc.csfinalIfs.add((IfNode) g.predecessor().predecessor());
                    CSF_IFS_PRE.incrementAndGet();
                }
            }
            for (IfNode i : graph.getNodes(IfNode.TYPE)) {
                if (isCsfinalDeadArm(i)) {
                    if (gc == null) {
                        gc = new GraphCensus();
                    }
                    gc.csfinalIfs.add(i);
                    CSF_IFS_PRE.incrementAndGet();
                    CSF_DEAD_ARMS_PRE.incrementAndGet();
                }
            }
            if (gc != null) {
                GRAPH_CENSUS.put(graph, gc);
            }
            return;
        }
        GraphCensus gc = GRAPH_CENSUS.remove(graph);
        for (jdk.graal.compiler.nodes.DeoptimizeNode d : graph.getNodes(jdk.graal.compiler.nodes.DeoptimizeNode.TYPE)) {
            if (isTrustedSpeculation(d.getSpeculation())) {
                MARKED_DEOPTS_POST.incrementAndGet();
            }
        }
        if (gc == null) {
            return;
        }
        for (FixedGuardNode g : gc.guards) {
            if (gc.removed.contains(g)) {
                REMOVED.incrementAndGet();
                if (inlined) {
                    REMOVED_INLINED.incrementAndGet();
                }
            } else if (gc.folded.contains(g)) {
                FOLDED_TO_THROW.incrementAndGet();
            } else if (g.isDeleted()) {
                KILLED_DEAD.incrementAndGet();
            } else {
                SURVIVING.incrementAndGet();
                if (inlined) {
                    SURVIVING_INLINED.incrementAndGet();
                }
            }
        }
        for (IfNode i : gc.partBIfs) {
            if (!i.isDeleted()) {
                PART_B_IFS_LEFT.incrementAndGet();
            }
        }
        for (IfNode i : gc.csfinalIfs) {
            if (!i.isDeleted()) {
                CSF_IFS_LEFT.incrementAndGet();
            }
        }
    }

    /**
     * The guard is the true arm of a csfinal diamond: {@code If(x instanceof String)} whose true successor
     * starts with the marked {@code x instanceof exact String} guard on the same value.
     */
    static boolean isCsfinalIf(FixedGuardNode g) {
        if (!(isCsfinalSpeculation(g.getSpeculation()) && g.predecessor() instanceof AbstractBeginNode begin && begin.predecessor() instanceof IfNode ifNode && ifNode.trueSuccessor() == begin &&
                        ifNode.condition() instanceof InstanceOfNode outer && !outer.type().isExact() && g.getCondition() instanceof InstanceOfNode inner && inner.type().isExact() && !inner
                                        .allowsNull() &&
                        outer.getValue() == inner.getValue() && outer.type().getType().equals(inner.type().getType()) && g.next() instanceof EndNode trueEnd)) {
            return false;
        }
        /* the exact emitted shape: the false arm is Begin nodes only, ending in the same merge (excludes a stock instanceof If + Part-A guard) */
        Node n = ifNode.falseSuccessor();
        while (n instanceof AbstractBeginNode b) {
            n = b.next();
        }
        return n instanceof EndNode falseEnd && falseEnd.merge() != null && falseEnd.merge() == trueEnd.merge();
    }

    /**
     * A csfinal diamond whose marked guard was folded to a failing constant before strengthen (a dominating fact excludes
     * exact String, e.g. the else of {@code value.getClass() == String.class}), leaving
     * {@code If(x instanceof String) -> Begin -> marked DeoptimizeNode}. Under the trust principle that arm admits only a
     * strict String subtype (a rep), which the child's rep-free entry excludes, so it is dead.
     */
    static boolean isCsfinalDeadArm(IfNode ifNode) {
        return ifNode.condition() instanceof InstanceOfNode io && !io.type().isExact() && STRING_CLASS.equals(io.type().getType().toJavaName()) &&
                        ifNode.trueSuccessor().next() instanceof jdk.graal.compiler.nodes.DeoptimizeNode d && isCsfinalSpeculation(d.getSpeculation());
    }

    /** SubstrateStrengthenGraphs.simplifyDelegate: fold a dead-arm diamond to its false successor (modes 0/1; check keeps it). */
    public static boolean strengthenCsfinalDeadArm(IfNode ifNode, SimplifierTool tool) {
        if (EXACT_PI_MODE == 2 || !isCsfinalDeadArm(ifNode)) {
            return false;
        }
        StructuredGraph graph = ifNode.graph();
        AbstractBeginNode killed = ifNode.trueSuccessor();
        AbstractBeginNode survivor = ifNode.falseSuccessor();
        if (survivor.hasUsages()) {
            jdk.graal.compiler.nodes.extended.ValueAnchorNode anchor = graph.add(new jdk.graal.compiler.nodes.extended.ValueAnchorNode());
            graph.addAfterFixed(survivor, anchor);
            survivor.replaceAtUsages(anchor, jdk.graal.compiler.nodeinfo.InputType.Guard, jdk.graal.compiler.nodeinfo.InputType.Anchor);
        }
        graph.removeSplit(ifNode, survivor);
        jdk.graal.compiler.nodes.util.GraphUtil.killCFG(killed);
        CSF_DEAD_ARMS_FOLDED.incrementAndGet();
        return true;
    }

    /**
     * SubstrateStrengthenGraphs.simplifyDelegate: mode 1 turns a marked guard into a tautology, so
     * {@code FixedGuardNode.simplify} removes it (or leaves a ValueAnchor for Part A's Pi), and re-queues the enclosing
     * analysis-only Ifs so their empty arms fold. Mode 2 keeps it (returns false). A guard whose condition is already a
     * constant is left to {@code FixedGuardNode.simplify} and only attributed.
     */
    public static boolean strengthenTrustedFilter(FixedGuardNode guard, SimplifierTool tool) {
        GraphCensus gc = GRAPH_CENSUS.get(guard.graph());
        if (guard.getCondition() instanceof LogicConstantNode c) {
            if (gc != null) {
                (c.getValue() == guard.isNegated() ? gc.folded : gc.removed).add(guard);
            }
            return false;
        }
        if (EXACT_PI_MODE == 2) {
            // Check mode keeps every marked guard; accumulator filters are removed in modes 0 and 1 alike.
            return false;
        }
        if (gc != null) {
            gc.removed.add(guard);
        }
        guard.setCondition(LogicConstantNode.tautology(guard.graph()), false);
        tool.addToWorkList(guard);
        Node p = guard.predecessor();
        while (p instanceof AbstractBeginNode || p instanceof IfNode) {
            if (p instanceof IfNode) {
                tool.addToWorkList(p);
            }
            p = p.predecessor();
        }
        return true;
    }

    static String trustedFilterSummary() {
        return "[string-analysis] exactpi mode=" + EXACT_PI_MODE + " chain=" + (EXACT_PI ? 1 : 0) +
                        " marked guards emitted: direct=" + EMITTED_DIRECT.get() + " chain-else=" + EMITTED_CHAIN_ELSE.get() + " chain-flat=" + EMITTED_CHAIN_FLAT.get() + " acc=" + EMITTED_ACC.get() +
                        " (chain sites=" + CHAIN_SITES.get() + ", aot-parse sites=" + AOT_PARSE_SITES.get() + ")" +
                        "; at strengthen: present=" + PRESENT_PRE.get() + " (inlined copies=" + PRESENT_PRE_INLINED.get() + ")" +
                        " removed=" + REMOVED.get() + " (inlined copies=" + REMOVED_INLINED.get() + ")" +
                        " killed-dead=" + KILLED_DEAD.get() + " folded-throw=" + FOLDED_TO_THROW.get() + " (marked deopts left=" + MARKED_DEOPTS_POST.get() + ")" +
                        " surviving=" + SURVIVING.get() + " (inlined copies=" + SURVIVING_INLINED.get() + ")" +
                        "; partB-ifs=" + PART_B_IFS_PRE.get() + " partB-ifs-left=" + PART_B_IFS_LEFT.get() +
                        "; attributed=" + (PRESENT_PRE.get() == REMOVED.get() + KILLED_DEAD.get() + FOLDED_TO_THROW.get() + SURVIVING.get() ? "ok" : "MISMATCH");
    }

    private static FixedGuardNode addTrustedGuard(GraphBuilderContext b, LogicNode condition) {
        EMITTING_ROOTS.add(b.getGraph().method());
        return b.add(new FixedGuardNode(condition, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, TRUSTED_FILTER, false));
    }

    /** Appends a node at the parse position (a {@code GraphBuilderContext::add}); an interface so the JUnit can drive it. */
    interface NodeAdder {
        <T extends jdk.graal.compiler.graph.Node> T add(T node);
    }

    /**
     * Accumulator lowering: the zero-cost exact-type filter for an admitted {@code ACCUMULATOR_VIEW} extraction's
     * receiver, by Part A's mechanism (a marked {@code FixedGuardNode(InstanceOf exact <class>, null allowed)} +
     * {@code PiNode}). Points-to sees the receiver as exactly {@code <class>} (the child's receiver proof); the guard is
     * removed in modes 0 and 1. Returns the receiver itself when its stamp already proves the type (a final builder
     * class), null when the stamp excludes it (a profile/IR mismatch: the caller declines).
     */
    static ValueNode trustedExactFilter(StructuredGraph graph, NodeAdder adder, ValueNode receiver, ResolvedJavaType exactClass) {
        ValueNode r = receiver.isUnregistered() ? adder.add(receiver) : receiver;
        TypeReference exact = TypeReference.createExactTrusted(exactClass);
        LogicNode isExact = InstanceOfNode.createAllowNull(exact, r, null, null);
        if (isExact instanceof LogicConstantNode c) {
            return c.getValue() ? r : null;
        }
        isExact = adder.add(isExact);
        EMITTING_ROOTS.add(graph.method());
        FixedGuardNode guard = adder.add(new FixedGuardNode(isExact, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, TRUSTED_FILTER, false));
        EMITTED_ACC.incrementAndGet();
        return graph.addOrUnique(new PiNode(r, StampFactory.object(exact), guard));
    }

    private static TypeReference exactType(GraphBuilderContext b, Class<?> c) {
        return TypeReference.createExactTrusted(b.getMetaAccess().lookupJavaType(c));
    }

    /** True for the analysis-parse instance (the AOT-parse instance never narrows: no StrengthenGraphs follows). */
    private final boolean analysisParse;

    public InlineCacheTrivialMethodNodePlugin() {
        this(true);
    }

    public InlineCacheTrivialMethodNodePlugin(boolean analysisParse) {
        this.analysisParse = analysisParse;
    }

    private ValueNode[] narrowReceiverToExactString(GraphBuilderContext b, ValueNode[] args) {
        if (!EXACT_PI) {
            return args;
        }
        if (!analysisParse) {
            AOT_PARSE_SITES.incrementAndGet();
            return args;
        }
        ValueNode receiver = args[0];
        if (receiver.isUnregistered()) {
            receiver = b.add(receiver);
        }
        TypeReference exact = exactType(b, String.class);
        LogicNode isString = InstanceOfNode.createAllowNull(exact, receiver, null, null);
        if (isString instanceof LogicConstantNode) {
            return args;
        }
        isString = b.add(isString);
        FixedGuardNode guard = addTrustedGuard(b, isString);
        EMITTED_DIRECT.incrementAndGet();
        ValueNode pi = b.getGraph().addOrUnique(new PiNode(receiver, StampFactory.object(exact), guard));
        ValueNode[] narrowed = args.clone();
        narrowed[0] = pi;
        return narrowed;
    }

    private boolean chainActive() {
        if (EXACT_PI && !analysisParse) {
            AOT_PARSE_SITES.incrementAndGet();
        }
        return EXACT_PI && analysisParse;
    }

    /**
     * Part B: the analysis-only else filter, emitted at the parser's live position; returns with the parser live again.
     * The receiver is passed on unchanged: its merged flow is {String} + {listed inheriting reps}.
     */
    private static void emitTrustedElseFilter(GraphBuilderContext b, ValueNode receiver, List<Class<?>> inheritingReps, ValueNode[] args, ResolvedJavaMethod target) {
        StructuredGraph graph = b.getGraph();
        List<EndNode> ends = new ArrayList<>();
        if (inheritingReps.size() >= 2) {
            /* the multi-arm elses, counted for the objdump check */
            StringBuilder reps = new StringBuilder();
            for (Class<?> f : inheritingReps) {
                reps.append(reps.length() == 0 ? "" : ",").append(f.getSimpleName());
            }
            MULTI_FLAT_SITES.add(sourceLocation(b) + " " + target.getName() + target.getSignature().toMethodDescriptor() + " [" + reps + "]");
        }
        for (Class<?> flat : inheritingReps) {
            LogicNode isFlat = InstanceOfNode.create(exactType(b, flat), receiver);
            if (isFlat instanceof LogicConstantNode) {
                continue;
            }
            isFlat = graph.addOrUniqueWithInputs(isFlat);
            BeginNode flatBegin = graph.add(new BeginNode());
            BeginNode otherBegin = graph.add(new BeginNode());
            b.add(new IfNode(isFlat, flatBegin, otherBegin, BranchProbabilityNode.SLOW_PATH_PROFILE));
            FixedGuardNode flatGuard = graph.add(new FixedGuardNode(isFlat, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, TRUSTED_FILTER, false));
            EMITTING_ROOTS.add(graph.method());
            EMITTED_CHAIN_FLAT.incrementAndGet();
            flatBegin.setNext(flatGuard);
            EndNode flatEnd = graph.add(new EndNode());
            flatGuard.setNext(flatEnd);
            ends.add(flatEnd);
            BeginNode resume = b.append(new BeginNode());
            otherBegin.setNext(resume);
        }
        LogicNode isString = InstanceOfNode.createAllowNull(exactType(b, String.class), receiver, null, null);
        if (!(isString instanceof LogicConstantNode)) {
            addTrustedGuard(b, b.add(isString));
            EMITTED_CHAIN_ELSE.incrementAndGet();
        }
        if (!ends.isEmpty()) {
            ends.add(b.append(new EndNode()));
            MergeNode merge = b.append(new MergeNode());
            for (EndNode end : ends) {
                merge.addForwardEnd(end);
            }
            /* The state before the invoke: the arguments back on the stack for the merge's frame state. */
            JavaKind[] kinds = target.getSignature().toParameterKinds(true);
            for (int i = 0; i < args.length; i++) {
                b.push(kinds[i], args[i]);
            }
            b.setStateAfter(merge);
            for (int i = args.length - 1; i >= 0; i--) {
                b.pop(kinds[i]);
            }
        }
    }

    /** The state before the invoke at a merge the lowering made: the arguments back on the stack for the merge's frame state. */
    private static void setMergeState(GraphBuilderContext b, AbstractMergeNode merge, JavaKind[] kinds, ValueNode[] args) {
        assert kinds.length == args.length : "merge state: " + kinds.length + " kinds for " + args.length + " arguments";
        for (int i = 0; i < args.length; i++) {
            b.push(kinds[i], args[i]);
        }
        b.setStateAfter(merge);
        for (int i = args.length - 1; i >= 0; i--) {
            b.pop(kinds[i]);
        }
    }

    /**
     * Exact-receiver super site: narrows the receiver of a supertype-declared site to {@code String} (null allowed) for
     * the direct {@code String.<m>} call, by a marked guard + Pi (Part A; a ClassCastException check in check mode
     * ic.exactpi=2). The trust is the child's EXACT_RECV proof: its points-to receiver state here is exactly {String}
     * (reps are not instantiated in the child), so only String, the listed reps and null arrive.
     */
    private static ValueNode[] superReceiverToString(GraphBuilderContext b, ValueNode[] args, String site) {
        ValueNode receiver = args[0];
        if (EXACT_FIRST_SUPER_CHECK != 0) {
            ResolvedJavaMethod check = d1CheckMethod(b);
            ValueNode siteConst = b.add(ConstantNode.forConstant(b.getConstantReflection().forString(site), b.getMetaAccess()));
            emitCallAtParser(b, InvokeKind.Static, check, new ValueNode[]{receiver, siteConst}, JavaKind.Object);
            EMITTED_SUPER_CAST.incrementAndGet();
            ValueNode[] checked = args.clone();
            checked[0] = b.pop(JavaKind.Object);
            return checked;
        }
        TypeReference str = TypeReference.createTrustedWithoutAssumptions(b.getMetaAccess().lookupJavaType(String.class));
        LogicNode isStr = InstanceOfNode.createAllowNull(str, receiver, null, null);
        if (isStr instanceof LogicConstantNode c) {
            GraalError.guarantee(c.getValue(), "string-analysis IC exact-receiver super site: the receiver can never be a String at an EXACT_RECV site");
            return args;
        }
        FixedGuardNode guard = addTrustedGuard(b, b.add(isStr));
        EMITTED_SUPER_CAST.incrementAndGet();
        ValueNode[] narrowed = args.clone();
        narrowed[0] = b.getGraph().addOrUnique(new PiNode(receiver, StampFactory.object(str), guard));
        return narrowed;
    }

    private static ResolvedJavaMethod d1CheckMethod(GraphBuilderContext b) {
        try {
            return b.getMetaAccess().lookupJavaMethod(com.oracle.svm.core.stringrep.D1Check.class.getDeclaredMethod("check", Object.class, String.class));
        } catch (NoSuchMethodException e) {
            throw GraalError.shouldNotReachHere(e);
        }
    }

    /** The rep test of the chain: Part B's exact InstanceOf (a filter for points-to) or a getClass compare. */
    private LogicNode repTest(GraphBuilderContext b, ValueNode receiver, ValueNode[] receiverClassHolder, Class<?> repClass) {
        if (EXACT_PI && analysisParse) {
            return b.add(InstanceOfNode.create(exactType(b, repClass), receiver));
        }
        if (receiverClassHolder[0] == null) {
            receiverClassHolder[0] = b.add(new GetClassNode(
                            StampFactory.objectNonNull(TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(Class.class))), receiver));
        }
        ConstantNode repClassConst = ConstantNode.forConstant(
                        b.getConstantReflection().asJavaClass(b.getMetaAccess().lookupJavaType(repClass)), b.getMetaAccess());
        return b.add(new ObjectEqualsNode(receiverClassHolder[0], repClassConst));
    }

    private final Map<String, ResolvedJavaMethod> methodCache = new ConcurrentHashMap<>();

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (isFlatReentry(b, method)) {
            return false;
        }
        return handleInvoke0(b, method, args);
    }

    private boolean handleInvoke0(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (!RepresentationProfileHolder.hasProfile()) {
            return false;
        }
        jdk.graal.compiler.graph.Graph.Mark mark = b.getGraph().getMark();
        try {
            String decl = method.getDeclaringClass().toJavaName();
            if (!decl.equals(STRING_CLASS)) {
                /* exact-receiver super site: a rep-list supertype site that stock would devirtualize (the child's EXACT_RECV proof) */
                if (lowerExactReceiverSuperSite(b, method, args)) {
                    return true;
                }
                /* csfinal: analysis-only rep exclusion at a rep-free String-supertype site; the invoke stays stock */
                excludeRepsAtSupertypeSite(b, method, args);
                return false;
            }
            String name = method.getName();
            String nd = name + method.getSignature().toMethodDescriptor();
            Method member = StringIcMethods.lookup(nd);
            if (member == null) {
                return false;
            }

            /*
             * Always-virt: no claim at a terminal-body enclosing method; the stock pipeline owns the site
             * (a rep receiver then dispatches virtually to its own override, the rep-safe form).
             */
            String loc = sourceLocation(b);
            ProfileEntry entry = lookupInlineCacheEntry(loc);
            String variant = entry == null ? null : entry.getVariant();
            /*
             * Kind-level terminal-body entries (TerminalBodyKinds): a KT-marked entry is the child's complete kind-level
             * rep set for a site inside a terminal body, so the terminal-body decline does not apply; the lowering below
             * runs on the unmarked variant.
             */
            String unmarked = TerminalBodyKinds.stripMarker(variant);
            if (unmarked != null) {
                variant = unmarked;
            } else if (StringAnalysisPolicy.alwaysVirtJdkTrivialApplies(b)) {
                return variant == null ? decline("no-entry", loc, nd) : decline("terminal-body-unmarked", loc, nd);
            }
            if (variant == null) {
                return decline("no-entry", loc, nd);
            }

            /*
             * Redirect table: at an EQUALS_MATRIX REDIRECT site the equals invoke is replaced by maybeCustomStringEquals,
             * lowered per the receiver's INLINE_CACHE entry. UNKNOWN/EXACT_STRING prove rep-freeness, so one special
             * invoke of String.maybeCustomStringEquals (@ForceInline) is sound; a rep list chains one special invoke per
             * overriding rep with a special String.maybeCustomStringEquals else (the list is exhaustive by the refusal
             * discipline; plain Strings and non-overriding flat reps such as SingleByteString, which keeps {@code value}
             * set, are correct there). Declining leaves EqualsMatrixNodePlugin's sound virtual residual.
             */
            if (name.equals("equals") && isRedirectSite(loc)) {
                boolean r = handleRedirectEqualsSite(b, method, variant, args);
                return r ? mark("redirect", loc, nd) : decline("redirect-declined", loc, nd);
            }
            /*
             * compareTo mirror: the same rule for a String.compareTo(String) invoke at a REDIRECT site (a user site or
             * the bridge's internal compareTo(Object)@5), replaced by String.maybeCustomStringCompareTo. Declining leaves
             * EqualsMatrixNodePlugin's virtual maybeCustomStringCompareTo (sound for every receiver).
             */
            if (nd.equals(COMPARE_TO_STRING) && isRedirectSite(loc)) {
                boolean r = handleRedirectCompareToSite(b, method, variant, args);
                return r ? mark("redirect", loc, nd) : decline("redirect-declined", loc, nd);
            }

            /* The target is the invoke's own String method (descriptor-exact; no name lookup). */
            ResolvedJavaMethod stringMethod = method;

            /*
             * UNKNOWN and EXACT_STRING prove rep-freeness, so one direct call to String.<m> is sound. Equals sites with a
             * REDIRECT entry were routed above; a rep argument at a non-redirect equals site is impossible by the same
             * completeness discipline, so the field-reading stock equals intrinsic the flat call becomes is safe. That
             * premise is load-bearing (no getClass deflection is left) and is checked by ic.flatstock=2.
             */
            if (variant.equals(UNKNOWN) || variant.equals(EXACT_STRING)) {
                emitFlatCall(b, stringMethod, narrowReceiverToExactString(b, args));
                return mark("direct", loc, nd);
            }

            return lowerRepList(b, method, args, stringMethod, member, variant, loc, nd, false);
        } catch (Throwable t) {
            /*
             * Declining is only correct while the graph is untouched (the parser then emits the invoke itself). After a
             * node was added, a failure must not leave a half-built graph under a second invoke: rethrow loudly.
             */
            if (b.getGraph().getNewNodes(mark).isNotEmpty()) {
                if (t instanceof jdk.vm.ci.code.BailoutException bailout) {
                    throw bailout;
                }
                throw GraalError.shouldNotReachHere(t, "string-analysis IC: failure after the graph was changed at " + method.format("%H.%n(%p)") + " in " + b.getMethod().format("%H.%n(%p)") +
                                " bci " + b.bci());
            }
            return false;
        }
    }

    /**
     * The rep-list lowering: {@code stringMethod} is String's own implementation of the site's method, {@code member}
     * its reflective declaration. {@code superSite}: the invoke is declared by a proper supertype of String and the
     * child proved the receiver state exactly {String} (an exact-receiver super site).
     */
    private boolean lowerRepList(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args, ResolvedJavaMethod stringMethod, Method member, String variant, String loc, String nd,
                    boolean superSite) {
        boolean hasExact = variant.startsWith("EXACT,");
        List<String> repNames = parseRepNames(variant, hasExact);
        if (repNames.isEmpty()) {
            return decline("empty-rep-list", loc, nd);
        }
        if (repNames.size() > MAX_CUSTOM_REPS) {
            return decline("over-cap", loc, nd);
        }

        /*
         * Else-direct per (rep, method): a listed rep that implements the method (TerminalBodyKinds.implementingClass,
         * the JVM's selection, shared with the premise pins) gets a branch calling its own implementation; every other
         * listed rep joins the else (the direct String.<m>). Soundness is dispatch equivalence: the else is taken only
         * when implementingClass(rep, m) == String.class, so it binds the body the stock virtual call binds on that rep.
         * Whether that inherited body is correct on the rep is a separate premise, the same at a stock virtual site: a
         * value-carrying rep keeps String's value/coder (FlatRepPremiseTest); for a value-null rep the pins
         * (RepInheritedBodyTest, ValueNullOverrideTest) guard the whitelisted inherited usages.
         * VALUE_NULL_INHERITS counts the former decline condition (expected 0).
         */
        List<Class<?>> overridingReps = new ArrayList<>();
        List<ResolvedJavaMethod> overridingMethods = new ArrayList<>();
        List<Class<?>> inheritingReps = new ArrayList<>();
        for (String repName : repNames) {
            Class<?> repClass = InlineCacheRegistry.getRepClass(repName);
            if (repClass == null) {
                return decline("unknown-rep", loc, nd + " " + repName);
            }
            Class<?> impl = TerminalBodyKinds.implementingClass(repClass, member);
            if (impl == null) {
                return decline("rep-unresolved", loc, nd + " " + repName);
            }
            if (impl != String.class) {
                ResolvedJavaMethod repMethod = resolveDeclared(b, repClass, member);
                if (repMethod == null) {
                    return decline("rep-unresolved", loc, nd + " " + repName);
                }
                overridingReps.add(repClass);
                overridingMethods.add(repMethod);
            } else {
                inheritingReps.add(repClass); // no rep-implementation check here (see above)
                if (!InlineCacheRegistry.isValueCarryingFlatRep(repClass) && !TerminalBodyKinds.entryBodies(repName).contains(nd)) {
                    VALUE_NULL_INHERITS.add(loc + " " + nd + " " + repName); // print-only census (the former decline's condition)
                }
            }
        }
        // No listed rep implements <m>: the chain collapses to one direct String.<m> call.
        if (overridingReps.isEmpty()) {
            boolean r = emitCollapsedDirect(b, stringMethod, args, inheritingReps, true, superSite);
            return r ? mark(superSite ? "super-collapsed" : "collapsed", loc, nd) : false;
        }

        boolean r = buildMultiBranchDirectCallCache(b, method, args, stringMethod, overridingReps, overridingMethods, inheritingReps, true, superSite);
        return r ? mark(superSite ? "super-chain" : "chain", loc, nd) : false;
    }

    /**
     * Exact-receiver super site: a Virtual or Interface invoke declared by a proper supertype of String
     * ({@code CharSequence}, {@code Object}, …) on a String IC member, whose INLINE_CACHE entry is a rep list and whose key
     * carries the child's {@code EXACT_RECV STRING} proof ({@link ExactReceiverSites}: the child's points-to receiver state
     * is exactly {String}, so stock would bind the call to {@code String.<m>}). Lowered to the all-direct chain of
     * {@link #lowerRepList} on a receiver narrowed to String by a trusted filter. No virtual fallback: the proof says no
     * other class arrives. Without the proof the site is untouched. Analysis parse only, with Part B (ic.exactpi != 0).
     */
    private boolean lowerExactReceiverSuperSite(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (!EXACT_PI || !analysisParse || method.isStatic() || args.length == 0 || args[0].isNullConstant()) {
            return false;
        }
        InvokeKind kind = b.getInvokeKind();
        if (kind != InvokeKind.Interface && kind != InvokeKind.Virtual) {
            return false;
        }
        String loc = sourceLocation(b);
        if (!RepresentationProfileHolder.getInstance().hasExactReceiver(loc)) {
            return false;
        }
        String nd = method.getName() + method.getSignature().toMethodDescriptor();
        ResolvedJavaType stringType = b.getMetaAccess().lookupJavaType(String.class);
        ResolvedJavaType declType = method.getDeclaringClass();
        Method member = StringIcMethods.lookup(nd);
        if (member == null || declType.equals(stringType) || !declType.isAssignableFrom(stringType)) {
            return decline("super-not-member", loc, nd);
        }
        if (isRedirectSite(loc)) {
            return decline("super-redirect", loc, nd);
        }
        String variant = siteVariant(loc, StringAnalysisPolicy.alwaysVirtJdkTrivialApplies(b));
        if (variant == null || variant.equals(UNKNOWN) || variant.equals(EXACT_STRING) || variant.equals(InlineCacheProfilingHeuristic.UNPROVEN)) {
            return decline("super-no-replist", loc, nd);
        }
        ResolvedJavaMethod stringImpl = stringType.resolveConcreteMethod(method, b.getMethod().getDeclaringClass());
        if (stringImpl == null || !stringImpl.equals(b.getMetaAccess().lookupJavaMethod(member))) {
            return decline("super-impl-not-string", loc, nd);
        }
        SUPER_SITES.add(loc + " " + nd);
        return lowerRepList(b, method, args, stringImpl, member, variant, loc, nd, true);
    }

    private static boolean mark(String form, String loc, String nd) {
        lowered(form, loc, nd);
        return true;
    }

    /**
     * csfinal ("as if String were still final"): at a virtual/interface invoke declared by a proper supertype of String
     * ({@code CharSequence}, {@code Comparable}, {@code Object}, …) whose site carries an UNKNOWN/EXACT_STRING entry (the
     * child's rep-freeness proof), the parent's points-to receiver state is cut back to what stock would see: the state
     * minus the rep classes. Expressed with the existing analysis-only filters:
     * <pre>
     * if (x instanceof String) { trusted guard (x instanceof exact String) } // true arm: {String}
     * // false arm: the If's negated filter, state minus every String-hierarchy type (keeps null, StringBuilder, …)
     * merge; then the original invoke (the plugin returns false)
     * </pre>
     * {@code StrengthenGraphs} then decides exactly as in stock. After points-to the guard is tautologised
     * ({@link #strengthenTrustedFilter}) and the If folds: no run-time check ({@code csfinal ifs left} must be 0). A
     * receiver stamped within the String hierarchy gets the single Part-A guard instead. Rep-list entries, REDIRECT sites,
     * JDK-terminal unmarked entries (always-virt) and sites without an entry are untouched. Requires ic.exactpi != 0
     * (exactpi=2 keeps the guard as a run-time ClassCastException).
     */
    static final AtomicLong CSF_DIAMONDS = new AtomicLong();
    static final AtomicLong CSF_GUARDS = new AtomicLong();
    static final Set<String> CSF_SITES = ConcurrentHashMap.newKeySet();
    static final Map<String, AtomicLong> CSF_BY_DECL = new ConcurrentHashMap<>();
    static final Set<String> CSF_REPLIST_SITES = ConcurrentHashMap.newKeySet();
    /** Sites whose entry is UNPROVEN (the child's walk was cut: no rep-freeness proof): left stock. */
    static final Set<String> CSF_UNPROVEN_SITES = ConcurrentHashMap.newKeySet();
    static final AtomicLong CSF_IFS_PRE = new AtomicLong();
    static final AtomicLong CSF_IFS_LEFT = new AtomicLong();
    /** Dead-arm diamonds (marked guard folded to a deopt before strengthen): seen at strengthen / folded by the hook. */
    static final AtomicLong CSF_DEAD_ARMS_PRE = new AtomicLong();
    static final AtomicLong CSF_DEAD_ARMS_FOLDED = new AtomicLong();

    /**
     * The csfinal decision (pure; JUnit-pinned): exclude the reps iff exactpi is on, the invoke is
     * virtual or interface (never {@code invokespecial}/static), its declaring class is a proper supertype of String,
     * the member (name + descriptor) is a String IC member, the site is not an equals/compareTo REDIRECT site, and the
     * site's variant (KT marker stripped; null for no entry or an unmarked entry at a JDK-terminal site) is UNKNOWN or
     * EXACT_STRING.
     */
    static boolean csfinalApplies(int exactPiMode, InvokeKind kind, boolean declProperStringSupertype, boolean stringMember, boolean redirect, String variant) {
        if (exactPiMode == 0 || (kind != InvokeKind.Interface && kind != InvokeKind.Virtual) || !declProperStringSupertype || !stringMember || redirect) {
            return false;
        }
        return variant != null && (variant.equals(UNKNOWN) || variant.equals(EXACT_STRING));
    }

    /** The INLINE_CACHE variant at {@code loc} with the KT marker stripped; null for no entry or an unmarked JDK-terminal entry. */
    static String siteVariant(String loc, boolean jdkTerminal) {
        ProfileEntry entry = lookupInlineCacheEntry(loc);
        String variant = entry == null ? null : entry.getVariant();
        String unmarked = TerminalBodyKinds.stripMarker(variant);
        if (unmarked != null) {
            return unmarked;
        }
        return jdkTerminal ? null : variant;
    }

    private void excludeRepsAtSupertypeSite(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (!EXACT_PI || !analysisParse || method.isStatic() || args.length == 0 || args[0].isNullConstant()) {
            return;
        }
        ResolvedJavaType stringType = b.getMetaAccess().lookupJavaType(String.class);
        ResolvedJavaType declType = method.getDeclaringClass();
        boolean properSuper = !declType.equals(stringType) && declType.isAssignableFrom(stringType);
        if (!properSuper) {
            return;
        }
        String nd = method.getName() + method.getSignature().toMethodDescriptor();
        boolean member = StringIcMethods.lookup(nd) != null;
        if (!member) {
            return;
        }
        String loc = sourceLocation(b);
        String variant = siteVariant(loc, StringAnalysisPolicy.alwaysVirtJdkTrivialApplies(b));
        if (!csfinalApplies(EXACT_PI_MODE, b.getInvokeKind(), true, true, isRedirectSite(loc), variant)) {
            if (InlineCacheProfilingHeuristic.UNPROVEN.equals(variant)) {
                CSF_UNPROVEN_SITES.add(loc + " " + nd);
            } else if (variant != null && !variant.equals(UNKNOWN) && !variant.equals(EXACT_STRING)) {
                CSF_REPLIST_SITES.add(loc + " " + nd);
            }
            return;
        }
        StructuredGraph graph = b.getGraph();
        ValueNode receiver = args[0];
        if (receiver.isUnregistered()) {
            receiver = b.add(receiver);
            args[0] = receiver;
        }
        TypeReference exact = exactType(b, String.class);
        ResolvedJavaType stampType = jdk.graal.compiler.nodes.type.StampTool.typeOrNull(receiver);
        if (stampType != null && stringType.isAssignableFrom(stampType)) {
            /*
             * Already within the String hierarchy: the Part-A filter states rep-freeness. A strict-subtype (rep) stamp is
             * rep code: untouched.
             */
            LogicNode isExact = InstanceOfNode.createAllowNull(exact, receiver, null, null);
            if (!stampType.equals(stringType) || !(isExact instanceof InstanceOfNode)) {
                return;
            }
            addTrustedGuard(b, b.add(isExact));
            CSF_GUARDS.incrementAndGet();
        } else {
            /* false for null: null stays in the false arm's state, as do all non-String types */
            LogicNode isStr = InstanceOfNode.create(TypeReference.createTrustedWithoutAssumptions(stringType), receiver);
            LogicNode isExact = InstanceOfNode.create(exact, receiver);
            if (!(isStr instanceof InstanceOfNode) || !(isExact instanceof InstanceOfNode)) {
                return;
            }
            isStr = graph.addOrUniqueWithInputs(isStr);
            isExact = graph.addOrUniqueWithInputs(isExact);
            BeginNode strBegin = graph.add(new BeginNode());
            BeginNode otherBegin = graph.add(new BeginNode());
            b.add(new IfNode(isStr, strBegin, otherBegin, BranchProbabilityNode.NOT_FREQUENT_PROFILE));
            FixedGuardNode guard = graph.add(new FixedGuardNode(isExact, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, TRUSTED_FILTER_CSFINAL, false));
            EMITTING_ROOTS.add(graph.method());
            strBegin.setNext(guard);
            EndNode strEnd = graph.add(new EndNode());
            guard.setNext(strEnd);
            BeginNode resume = b.append(new BeginNode());
            otherBegin.setNext(resume);
            EndNode otherEnd = b.append(new EndNode());
            MergeNode merge = b.append(new MergeNode());
            merge.addForwardEnd(strEnd);
            merge.addForwardEnd(otherEnd);
            /* The state before the invoke: the arguments back on the stack for the merge's frame state. */
            JavaKind[] kinds = method.getSignature().toParameterKinds(true);
            for (int i = 0; i < args.length; i++) {
                b.push(kinds[i], args[i]);
            }
            b.setStateAfter(merge);
            for (int i = args.length - 1; i >= 0; i--) {
                b.pop(kinds[i]);
            }
            CSF_DIAMONDS.incrementAndGet();
            CSF_DIAMONDS_BY_METHOD.computeIfAbsent(graph.method(), k -> new AtomicLong()).incrementAndGet();
        }
        CSF_SITES.add(loc + " " + nd);
        CSF_BY_DECL.computeIfAbsent(declType.toJavaName(false) + "." + method.getName(), k -> new AtomicLong()).incrementAndGet();
    }

    /** The csfinal diamonds emitted per method (its own bytecode), for the IBA budget discount. */
    static final Map<ResolvedJavaMethod, AtomicLong> CSF_DIAMONDS_BY_METHOD = new ConcurrentHashMap<>();
    static final AtomicLong CSF_IBA_FREE = new AtomicLong();

    /** The IBA credit of {@code method}: its diamonds' If + two InstanceOf nodes (the marked guard is free by itself). */
    public static int csfinalIbaCredit(ResolvedJavaMethod method) {
        AtomicLong n = method == null ? null : CSF_DIAMONDS_BY_METHOD.get(method);
        return n == null ? 0 : (int) Math.min(Integer.MAX_VALUE / 4, n.get()) * 3;
    }

    /**
     * The IBA predicate: a csfinal-marked guard (always), or, while the method still has credit, an
     * {@code InstanceOf String} (exact or not) or an {@code If} on a non-exact {@code InstanceOf String}.
     */
    public static boolean isCsfinalIbaFree(Node node, int credit) {
        boolean free;
        if (node instanceof FixedGuardNode g) {
            free = isCsfinalSpeculation(g.getSpeculation());
        } else if (credit <= 0) {
            free = false;
        } else if (node instanceof InstanceOfNode io) {
            free = STRING_CLASS.equals(io.type().getType().toJavaName()) && !io.allowsNull();
        } else if (node instanceof IfNode i) {
            free = i.condition() instanceof InstanceOfNode io && !io.type().isExact() && STRING_CLASS.equals(io.type().getType().toJavaName());
        } else {
            free = false;
        }
        if (free) {
            CSF_IBA_FREE.incrementAndGet();
        }
        return free;
    }

    /** csfinal: the print-only census line. */
    static String csfinalSummary() {
        return "[string-analysis] ic-csfinal: rep-excluded supertype sites=" + CSF_SITES.size() + " (diamonds=" + CSF_DIAMONDS.get() + " guards=" +
                        CSF_GUARDS.get() + ") by decl=" + new java.util.TreeMap<>(CSF_BY_DECL) + " rep-list sites left stock=" + CSF_REPLIST_SITES.size() + " unproven sites left stock=" +
                        CSF_UNPROVEN_SITES.size() + "; at strengthen: ifs=" +
                        CSF_IFS_PRE.get() + " (dead-arm=" + CSF_DEAD_ARMS_PRE.get() + " iba-free nodes=" + CSF_IBA_FREE.get() + " folded=" + CSF_DEAD_ARMS_FOLDED.get() + ") ifs left=" + CSF_IFS_LEFT
                                        .get();
    }

    private final Map<Method, ResolvedJavaMethod> declaredCache = new ConcurrentHashMap<>();

    /**
     * The declaration of {@code member} that virtual dispatch selects for a receiver of class {@code repClass} (the JVM
     * rule, {@link TerminalBodyKinds#selectedDeclaration}: descriptor-exact, bridges included).
     */
    private ResolvedJavaMethod resolveDeclared(GraphBuilderContext b, Class<?> repClass, Method member) {
        Method d = TerminalBodyKinds.selectedDeclaration(repClass, member);
        return d == null ? null : declaredCache.computeIfAbsent(d, m -> b.getMetaAccess().lookupJavaMethod(m));
    }

    /**
     * Redirect table: lowers a String-declared {@code equals} at an {@code EQUALS_MATRIX REDIRECT} site; the receiver's
     * variant decides the form of the replaced {@code maybeCustomStringEquals} call. Returns false (decline: the virtual
     * residual of {@link EqualsMatrixNodePlugin}) over {@link #MAX_REDIRECT_CUSTOM_REPS} entries, for a rep unknown to
     * {@link InlineCacheRegistry}, or when the target cannot be resolved.
     */
    private boolean handleRedirectEqualsSite(GraphBuilderContext b, ResolvedJavaMethod originalMethod, String variant, ValueNode[] args) {
        ResolvedJavaMethod mCse = resolveMethod(b, String.class, "maybeCustomStringEquals", getParamTypes("maybeCustomStringEquals"));
        if (mCse == null) {
            return false;
        }
        if (variant.equals(UNKNOWN) || variant.equals(EXACT_STRING)) {
            /* rep-free is a proof: one direct call, no guarded branch (the argument deflection is in the body). */
            return emitSingleCall(b, mCse, narrowReceiverToExactString(b, args), InvokeKind.Special);
        }
        boolean hasExact = variant.startsWith("EXACT,");
        List<String> repNames = parseRepNames(variant, hasExact);
        if (repNames.isEmpty()) {
            return false;
        }
        if (repNames.size() > MAX_REDIRECT_CUSTOM_REPS) {
            return false;
        }
        List<Class<?>> overridingReps = new ArrayList<>();
        List<ResolvedJavaMethod> overridingMethods = new ArrayList<>();
        List<Class<?>> inheritingReps = new ArrayList<>();
        Method mCseMember = StringIcMethods.lookup("maybeCustomStringEquals(Ljava/lang/Object;)Z");
        for (String repName : repNames) {
            Class<?> repClass = InlineCacheRegistry.getRepClass(repName);
            if (repClass == null) {
                return false;
            }
            if (InlineCacheRegistry.repOverrides(repClass, "maybeCustomStringEquals")) {
                ResolvedJavaMethod repMethod = mCseMember == null ? null : resolveDeclared(b, repClass, mCseMember);
                if (repMethod == null) {
                    return false;
                }
                overridingReps.add(repClass);
                overridingMethods.add(repMethod);
            } else {
                inheritingReps.add(repClass);
            }
        }
        if (overridingReps.isEmpty()) {
            // Every listed rep inherits maybeCustomStringEquals and keeps {@code value} set: one direct String call.
            return emitCollapsedDirect(b, mCse, args, inheritingReps, false);
        }
        return buildMultiBranchDirectCallCache(b, originalMethod, args, mCse, overridingReps, overridingMethods, inheritingReps, false, false);
    }

    static final String COMPARE_TO_STRING = "compareTo(Ljava/lang/String;)I";

    /**
     * compareTo mirror: the {@link #handleRedirectEqualsSite} rule with target {@code String.maybeCustomStringCompareTo}
     * (it deflects a non-String argument to the argument's own {@code compareTo}, negated): rep-free receiver = one
     * special mCSC; a rep list = one direct arm per rep that implements {@code compareTo} itself (its comparison is total
     * and exact over every argument class) and a special String mCSC else for plain Strings and inheriting reps (mCSC
     * deflects a rep argument before the stock body). Declines as {@link #handleRedirectEqualsSite}.
     */
    private boolean handleRedirectCompareToSite(GraphBuilderContext b, ResolvedJavaMethod originalMethod, String variant, ValueNode[] args) {
        ResolvedJavaMethod mCsc = resolveMethod(b, String.class, "maybeCustomStringCompareTo", getParamTypes("maybeCustomStringCompareTo"));
        Method cmpMember = StringIcMethods.lookup(COMPARE_TO_STRING);
        if (mCsc == null || cmpMember == null) {
            return false;
        }
        if (variant.equals(UNKNOWN) || variant.equals(EXACT_STRING)) {
            return emitSingleCall(b, mCsc, narrowReceiverToExactString(b, args), InvokeKind.Special);
        }
        boolean hasExact = variant.startsWith("EXACT,");
        List<String> repNames = parseRepNames(variant, hasExact);
        if (repNames.isEmpty() || repNames.size() > MAX_REDIRECT_CUSTOM_REPS) {
            return false;
        }
        List<Class<?>> overridingReps = new ArrayList<>();
        List<ResolvedJavaMethod> overridingMethods = new ArrayList<>();
        List<Class<?>> inheritingReps = new ArrayList<>();
        for (String repName : repNames) {
            Class<?> repClass = InlineCacheRegistry.getRepClass(repName);
            if (repClass == null) {
                return false;
            }
            Class<?> impl = TerminalBodyKinds.implementingClass(repClass, cmpMember);
            if (impl == null) {
                return false; // the selection cannot be resolved
            }
            if (impl != String.class) {
                ResolvedJavaMethod repMethod = resolveDeclared(b, repClass, cmpMember);
                if (repMethod == null) {
                    return false;
                }
                overridingReps.add(repClass);
                overridingMethods.add(repMethod);
            } else {
                inheritingReps.add(repClass); // no rep-implementation check (as lowerRepList)
                if (!InlineCacheRegistry.isValueCarryingFlatRep(repClass)) {
                    VALUE_NULL_INHERITS.add(sourceLocation(b) + " " + COMPARE_TO_STRING + " " + repName); // print-only census
                }
            }
        }
        if (overridingReps.isEmpty()) {
            return emitCollapsedDirect(b, mCsc, args, inheritingReps, false);
        }
        return buildMultiBranchDirectCallCache(b, originalMethod, args, mCsc, overridingReps, overridingMethods, inheritingReps, false, false);
    }

    /** The no-overrider rep list: one direct {@code String.<m>} call, preceded by the Part-B else filter. */
    private boolean emitCollapsedDirect(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args, List<Class<?>> inheritingReps, boolean stringFlat) {
        return emitCollapsedDirect(b, target, args, inheritingReps, stringFlat, false);
    }

    private boolean emitCollapsedDirect(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args, List<Class<?>> inheritingReps, boolean stringFlat, boolean superSite) {
        if (chainActive()) {
            ValueNode[] added = registered(b, args);
            CHAIN_SITES.incrementAndGet();
            if (!(superSite && EXACT_FIRST_SUPER_CHECK != 0)) {
                emitTrustedElseFilter(b, added[0], inheritingReps, added, target);
            }
            if (superSite) {
                added = superReceiverToString(b, added, sourceLocation(b));
            }
            return stringFlat ? emitFlat(b, target, added) : emitSingleCall(b, target, added, InvokeKind.Special);
        }
        GraalError.guarantee(!superSite, "string-analysis IC exact-receiver super site: a supertype-declared site is lowered only in the analysis parse");
        return stringFlat ? emitFlat(b, target, args) : emitSingleCall(b, target, args, InvokeKind.Special);
    }

    /**
     * The chain's flat else on the flat-call path; the result is popped for the merge. The else must stay live (a
     * result to merge): the null-constant receiver, where appendInvoke would end the block with a deopt, is kept on the
     * old emission by {@link #emitFlatCall}; any other way of ending the block here fails loudly.
     */
    private static ValueNode emitFlatElse(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args, JavaKind returnKind) {
        emitFlatCall(b, target, args);
        if (b.hasParseTerminated()) {
            throw GraalError.shouldNotReachHere("string-analysis IC: the chain's flat else call ended the block (no result to merge): " + target.format("%H.%n(%p)"));
        }
        return returnKind == JavaKind.Void ? null : b.pop(returnKind);
    }

    private static boolean emitFlat(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args) {
        emitFlatCall(b, target, args);
        return true;
    }

    static ValueNode[] registered(GraphBuilderContext b, ValueNode[] args) {
        ValueNode[] added = args.clone();
        for (int i = 0; i < added.length; i++) {
            if (added[i].isUnregistered()) {
                added[i] = b.add(added[i]);
            }
        }
        return added;
    }

    static List<String> parseRepNames(String variant, boolean hasExact) {
        String repPart = hasExact ? variant.substring("EXACT,".length()) : variant;
        List<String> reps = new ArrayList<>();
        for (String r : repPart.split(",")) {
            String trimmed = r.trim();
            if (!trimmed.isEmpty()) {
                reps.add(trimmed);
            }
        }
        return reps;
    }

    /**
     * Knob {@code svm.stringanalysis.ic.flatstock}: the flat call of a lowered site (the rep-free direct, the collapsed
     * direct and the chain's else) goes through the parser's normal invoke path ({@code appendInvoke}, via
     * {@link GraphBuilderContext#handleReplacedInvoke(InvokeKind, ResolvedJavaMethod, ValueNode[], boolean)}), so the stock
     * node plugins and parse-time invocation plugins (the {@code String.equals} intrinsic, constant folds) apply exactly
     * as at stock's direct {@code String.<m>} call. Our own node plugins do not fire again ({@link #isFlatReentry}). Rep
     * arms and the REDIRECT {@code maybeCustomStringEquals} calls keep the old emission ({@link #emitSingleCall}). 1
     * (default) = flat call, 0 = old emission (revert), 2 = check (verification only): as 1, plus a run-time guard on the
     * argument before every flat {@code equals} call ({@link #emitFlatEqualsCheck}).
     */
    static final int FLAT_STOCK_MODE = Integer.getInteger("svm.stringanalysis.ic.flatstock", 1);
    static final boolean FLAT_STOCK = FLAT_STOCK_MODE != 0;
    static final AtomicLong FLAT_STOCK_CALLS = new AtomicLong();
    static final AtomicLong FLAT_LEGACY_CALLS = new AtomicLong();
    /** Flat calls with a null-constant receiver, kept on the old emission ({@code appendInvoke} pushes no result). */
    static final AtomicLong FLAT_NULL_RECEIVER = new AtomicLong();
    /** The (parser, target) pair whose invoke this plugin is re-emitting on the stock path (per thread). */
    private static final ThreadLocal<Object[]> FLAT_REENTRY = new ThreadLocal<>();
    /** The number of re-emissions in progress on any thread: the plugins' fast path skips the ThreadLocal at 0. */
    private static final java.util.concurrent.atomic.AtomicInteger FLAT_ACTIVE = new java.util.concurrent.atomic.AtomicInteger();

    /**
     * True while {@code b} re-parses the flat call to {@code method} that one of our plugins emits on the stock path:
     * every string-analysis node plugin then declines, so only the stock plugins see the invoke (as in stock).
     */
    static boolean isFlatReentry(GraphBuilderContext b, ResolvedJavaMethod method) {
        if (FLAT_ACTIVE.get() == 0) {
            return false;
        }
        Object[] r = FLAT_REENTRY.get();
        return r != null && r[0] == b && r[1].equals(method);
    }

    /** Runs {@code emission} with {@code (b, target)} marked as the flat re-entry (the plugins decline it). */
    static void withFlatReentry(GraphBuilderContext b, ResolvedJavaMethod target, Runnable emission) {
        Object[] previous = FLAT_REENTRY.get();
        FLAT_REENTRY.set(new Object[]{b, target});
        FLAT_ACTIVE.incrementAndGet();
        try {
            emission.run();
        } finally {
            FLAT_ACTIVE.decrementAndGet();
            FLAT_REENTRY.set(previous);
        }
    }

    static String flatStockSummary() {
        String s = "[string-analysis] ic-flatstock: " + FLAT_STOCK_MODE + " stock-path flat calls=" + FLAT_STOCK_CALLS.get() + " legacy (interface caller)=" + FLAT_LEGACY_CALLS.get() +
                        " legacy (null receiver)=" + FLAT_NULL_RECEIVER.get();
        if (FLAT_STOCK_MODE == 2) {
            s += "; CHECK equals/compareTo sites=" + FLAT_CHECK_SITES.get() + " (of which compareTo(String): " + FLAT_CHECK_CMP_SITES.get() + ") guards emitted=" + FLAT_CHECK_GUARDS.get() +
                            " (argument stamp excluded the rep: " + FLAT_CHECK_EXCLUDED.get() + ")" +
                            "; at strengthen: present=" + FLAT_CHECK_PRE.get() + " left=" + FLAT_CHECK_POST.get();
            for (Map.Entry<String, AtomicLong> e : new java.util.TreeMap<>(FLAT_CHECK_LEFT_SITES).entrySet()) {
                s += "\n[string-analysis] ic-flatstock CHECK guard left:" + e.getKey() + " x" + e.getValue().get();
            }
        }
        return s;
    }

    @SuppressWarnings("deprecation")
    private static boolean callerIsInterface(GraphBuilderContext b) {
        ResolvedJavaType t = b.getMethod().getDeclaringClass();
        ResolvedJavaType host = t.getHostClass();
        return (host != null ? host : t).isInterface();
    }

    /**
     * The flat {@code String.<m>} call through the parser's own invoke path (result pushed). The parser's
     * {@code invokespecial} check for interface callers must not apply to a call that is {@code invokevirtual} in the
     * bytecode: in an interface method the call is passed as {@code Virtual}, which the parser binds directly when the
     * receiver stamp is exact (Part A's Pi); otherwise it keeps the old emission (counted). A null-constant receiver also
     * keeps the old emission ({@code appendInvoke} would append a deopt and push no result, which the chain's else cannot
     * merge).
     */
    private static void emitFlatCall(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args) {
        if (!FLAT_STOCK) {
            emitSingleCall(b, target, args, InvokeKind.Special);
            return;
        }
        ValueNode[] added = registered(b, args);
        if (added[0].isNullConstant()) {
            FLAT_NULL_RECEIVER.incrementAndGet();
            emitSingleCall(b, target, added, InvokeKind.Special);
            return;
        }
        InvokeKind kind = InvokeKind.Special;
        if (callerIsInterface(b)) {
            if (MethodCallTargetNode.findSpecialCallTarget(InvokeKind.Virtual, added[0], target, b.getMethod().getDeclaringClass()) == null) {
                FLAT_LEGACY_CALLS.incrementAndGet();
                emitSingleCall(b, target, added, InvokeKind.Special);
                return;
            }
            kind = InvokeKind.Virtual;
        }
        if (FLAT_STOCK_MODE == 2) {
            emitFlatEqualsCheck(b, target, added);
        }
        InvokeKind k = kind;
        /*
         * The nested appendInvoke resets currentInvoke to null while the outer appendInvoke is still running; nothing
         * reads it afterwards (this plugin returns true and the outer call returns at once).
         */
        withFlatReentry(b, target, () -> b.handleReplacedInvoke(k, target, added, false));
        FLAT_STOCK_CALLS.incrementAndGet();
    }

    /**
     * ic.flatstock=2 (verification only): the run-time check of the premise "no REDIRECT ⇒ the equals argument is
     * rep-free". Before a flat {@code String.equals} call, one guard {@code !(arg instanceof exact R)} per value-null rep
     * class R of {@link InlineCacheRegistry#REP_CLASSES} (a value-carrying argument is read correctly by the stock body);
     * a failing guard throws an UnsupportedFeatureError carrying {@link #FLAT_CHECK_MESSAGE}. Not marked, so strengthening
     * keeps it unless points-to proves R never reaches the argument (counted at strengthen as present/left).
     */
    private static void emitFlatEqualsCheck(GraphBuilderContext b, ResolvedJavaMethod target, ValueNode[] args) {
        String tnd = target.getName() + target.getSignature().toMethodDescriptor();
        // compareTo mirror: the flat compareTo(String) has the same premise, since no argument deflection is left
        if (args.length != 2 || !(tnd.equals("equals(Ljava/lang/Object;)Z") || tnd.equals(COMPARE_TO_STRING))) {
            return;
        }
        FLAT_CHECK_SITES.incrementAndGet();
        if (tnd.equals(COMPARE_TO_STRING)) {
            FLAT_CHECK_CMP_SITES.incrementAndGet(); // the compareTo share of the sites (census)
        }
        /* the site in the guard's speculation: named by the run-time error and by the census of surviving guards */
        DeoptHostedSnippets.AnalysisSpeculation spec = new DeoptHostedSnippets.AnalysisSpeculation(
                        new DeoptHostedSnippets.AnalysisSpeculationReason(FLAT_CHECK_MESSAGE + " at " + b.getMethod().format("%H.%n(%p)") + "@" + b.bci()));
        for (Class<?> rep : InlineCacheRegistry.REP_CLASSES.values()) {
            if (InlineCacheRegistry.isValueCarryingFlatRep(rep)) {
                continue;
            }
            LogicNode isRep = InstanceOfNode.create(exactType(b, rep), args[1]);
            if (isRep instanceof LogicConstantNode c && !c.getValue()) {
                FLAT_CHECK_EXCLUDED.incrementAndGet();
                continue;
            }
            isRep = b.add(isRep);
            b.add(new FixedGuardNode(isRep, DeoptimizationReason.UnreachedCode, DeoptimizationAction.None, spec, true));
            FLAT_CHECK_GUARDS.incrementAndGet();
        }
    }

    static final String FLAT_CHECK_MESSAGE = "string-analysis FLATSTOCK-CHECK: value-null rep argument at a flat String.equals site";
    /** ic.flatstock=2: the guards left after strengthen, per site (root graph method: guard site, checked rep). */
    static final Map<String, AtomicLong> FLAT_CHECK_LEFT_SITES = new ConcurrentHashMap<>();
    static final AtomicLong FLAT_CHECK_SITES = new AtomicLong();
    static final AtomicLong FLAT_CHECK_CMP_SITES = new AtomicLong();
    static final AtomicLong FLAT_CHECK_GUARDS = new AtomicLong();
    static final AtomicLong FLAT_CHECK_EXCLUDED = new AtomicLong();
    static final AtomicLong FLAT_CHECK_PRE = new AtomicLong();
    static final AtomicLong FLAT_CHECK_POST = new AtomicLong();

    static boolean isFlatCheckGuard(FixedGuardNode g) {
        return g.getSpeculation() instanceof DeoptHostedSnippets.AnalysisSpeculation && g.getSpeculation().getReason() instanceof DeoptHostedSnippets.AnalysisSpeculationReason r &&
                        r.getMessage().startsWith(FLAT_CHECK_MESSAGE);
    }

    private static boolean emitSingleCall(GraphBuilderContext b,
                    ResolvedJavaMethod targetMethod,
                    ValueNode[] args,
                    InvokeKind invokeKind) {
        StructuredGraph graph = b.getGraph();
        JavaKind returnKind = targetMethod.getSignature().getReturnKind();
        JavaType returnType = targetMethod.getSignature().getReturnType(targetMethod.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        ValueNode[] addedArgs = new ValueNode[args.length];
        for (int i = 0; i < args.length; i++) {
            ValueNode arg = args[i];
            if (arg.isUnregistered()) {
                arg = b.add(arg);
            }
            addedArgs[i] = arg;
        }
        MethodCallTargetNode callTarget = graph.add(
                        new SubstrateMethodCallTargetNode(invokeKind, targetMethod, addedArgs, returnStamp));
        /*
         * The parser's own invoke path (createNonInlinedInvoke with this bci's exception edge), so an exception reaches
         * the enclosing handler; a plain InvokeNode would unwind past the method's own try/catch. The call target is
         * already built, so no plugin runs again for it.
         */
        b.handleReplacedInvoke(callTarget, returnKind);
        return true;
    }

    private boolean buildMultiBranchDirectCallCache(GraphBuilderContext b, ResolvedJavaMethod originalMethod,
                    ValueNode[] args,
                    ResolvedJavaMethod stringMethod, List<Class<?>> repClasses, List<ResolvedJavaMethod> repMethods, List<Class<?>> inheritingReps,
                    boolean stringFlat, boolean superSite) {
        JavaKind returnKind = originalMethod.getSignature().getReturnKind();
        boolean chain = chainActive();
        if (chain || EXACT_FIRST != 0 || superSite) {
            args = registered(b, args);
        }
        if (chain) {
            CHAIN_SITES.incrementAndGet();
        }
        ValueNode receiver = args[0];
        StructuredGraph graph = b.getGraph();

        ValueNode[] receiverClass = new ValueNode[1];

        List<ValueNode> branchResults = new ArrayList<>();
        List<EndNode> branchEnds = new ArrayList<>();
        BeginNode currentBegin;
        /*
         * Exact-first (ic.exactfirst): the plain String (exact class, null allowed) is tested first and jumps to the
         * chain's direct String.<m> call; only the order of the tests changes. Null takes the String path too (the direct
         * call throws the NullPointerException, as the else did), so points-to folds the test where only String and null
         * arrive.
         */
        EndNode exactStringEnd = null;
        if (EXACT_FIRST != 0) {
            LogicNode isString = InstanceOfNode.createAllowNull(exactType(b, String.class), receiver, null, null);
            if (!(isString instanceof LogicConstantNode)) {
                isString = b.add(isString);
                BeginNode strBegin = graph.add(new BeginNode());
                BeginNode chainBegin = graph.add(new BeginNode());
                b.add(new IfNode(isString, strBegin, chainBegin, BranchProbabilityNode.FAST_PATH_PROFILE));
                exactStringEnd = graph.add(new EndNode());
                strBegin.setNext(exactStringEnd);
                BeginNode resume = b.append(new BeginNode());
                chainBegin.setNext(resume);
                EXACT_FIRST_IFS.incrementAndGet();
            }
        }
        {
            Class<?> firstRepClass = repClasses.get(0);
            ResolvedJavaMethod firstRepMethod = repMethods.get(0);
            LogicNode isFirstRep = repTest(b, receiver, receiverClass, firstRepClass);

            BeginNode firstRepBegin = b.add(new BeginNode());
            FixedWithNextNode predecessor = (FixedWithNextNode) firstRepBegin.predecessor();
            predecessor.setNext(null);
            BeginNode notFirstRepBegin = b.add(new BeginNode());
            firstRepBegin.setNext(null);
            IfNode firstRepIf = b.add(new IfNode(isFirstRep, firstRepBegin, notFirstRepBegin, repArmProfile()));
            notFirstRepBegin.setNext(null);
            predecessor.setNext(firstRepIf);

            TypeReference firstRepTypeRef = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(firstRepClass));
            Stamp firstRepStamp = StampFactory.objectNonNull(firstRepTypeRef);
            ValueNode firstPiReceiver = graph.addOrUnique(new PiNode(receiver, firstRepStamp, firstRepBegin));
            ValueNode[] firstRepArgs = new ValueNode[args.length];
            firstRepArgs[0] = firstPiReceiver;
            for (int j = 1; j < args.length; j++) {
                firstRepArgs[j] = args[j];
            }
            ValueNode firstRepResult = emitBranchCall(b, firstRepBegin, InvokeKind.Special, firstRepMethod, firstRepArgs, returnKind);
            EndNode firstRepEnd = b.append(new EndNode());

            branchResults.add(firstRepResult);
            branchEnds.add(firstRepEnd);
            currentBegin = notFirstRepBegin;
        }

        for (int i = 1; i < repClasses.size(); i++) {
            Class<?> repClass = repClasses.get(i);
            ResolvedJavaMethod repMethod = repMethods.get(i);

            LogicNode isRep = repTest(b, receiver, receiverClass, repClass);

            BeginNode repBegin = graph.add(new BeginNode());
            BeginNode nextBegin = graph.add(new BeginNode());
            IfNode repIf = graph.add(new IfNode(isRep, repBegin, nextBegin, repArmProfile()));
            currentBegin.setNext(repIf);

            TypeReference repTypeRef = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(repClass));
            Stamp repStamp = StampFactory.objectNonNull(repTypeRef);
            ValueNode piReceiver = graph.addOrUnique(new PiNode(receiver, repStamp, repBegin));
            ValueNode[] repArgs = new ValueNode[args.length];
            repArgs[0] = piReceiver;
            for (int j = 1; j < args.length; j++) {
                repArgs[j] = args[j];
            }
            ValueNode repResult = emitBranchCall(b, repBegin, InvokeKind.Special, repMethod, repArgs, returnKind);
            EndNode repEnd = b.append(new EndNode());

            branchResults.add(repResult);
            branchEnds.add(repEnd);

            currentBegin = nextBegin;
        }

        /*
         * Else-direct: the else is a direct String.<m> call, not a virtual fallback; the rep list is exhaustive, so the
         * remaining receivers (plain Strings, listed inheriting reps) are exactly the inherited body's domain. At a
         * non-redirect equals site the target is plain String.equals (the argument is rep-free without REDIRECT); at a
         * REDIRECT site it is String.maybeCustomStringEquals (the argument deflection lives in that body).
         */
        // Part B: the else serves plain Strings and the listed non-overriding reps, so no exact-String stamp.
        ValueNode fallbackResult;
        if (exactStringEnd != null || superSite) {
            /*
             * The chain's fall-through (Part-B filter first) and the exact-String arm merge before the one direct
             * String.<m> call. At an exact-receiver super site the receiver is then narrowed to String (EXACT_RECV proof).
             */
            BeginNode entry = b.append(new BeginNode());
            currentBegin.setNext(entry);
            if (chain && !(superSite && EXACT_FIRST_SUPER_CHECK != 0)) {
                emitTrustedElseFilter(b, receiver, inheritingReps, args, stringMethod);
            }
            if (exactStringEnd != null) {
                EndNode chainEnd = b.append(new EndNode());
                MergeNode m1 = b.append(new MergeNode());
                m1.addForwardEnd(exactStringEnd);
                m1.addForwardEnd(chainEnd);
                setMergeState(b, m1, stringMethod.getSignature().toParameterKinds(true), args);
            }
            ValueNode[] elseArgs = superSite ? superReceiverToString(b, args, sourceLocation(b)) : args;
            if (stringFlat) {
                fallbackResult = emitFlatElse(b, stringMethod, elseArgs, returnKind);
            } else {
                fallbackResult = emitCallHere(b, InvokeKind.Special, stringMethod, elseArgs, returnKind);
            }
        } else if (chain) {
            BeginNode entry = b.append(new BeginNode());
            currentBegin.setNext(entry);
            emitTrustedElseFilter(b, receiver, inheritingReps, args, stringMethod);
            if (stringFlat) {
                fallbackResult = emitFlatElse(b, stringMethod, args, returnKind);
            } else {
                fallbackResult = emitCallHere(b, InvokeKind.Special, stringMethod, args, returnKind);
            }
        } else if (stringFlat) {
            assert b.hasParseTerminated() : "the else call must start after a control split";
            BeginNode entry = b.append(new BeginNode());
            currentBegin.setNext(entry);
            fallbackResult = emitFlatElse(b, stringMethod, args, returnKind);
        } else {
            fallbackResult = emitBranchCall(b, currentBegin, InvokeKind.Special, stringMethod, args, returnKind);
        }
        EndNode fallbackEnd = b.append(new EndNode());
        branchResults.add(fallbackResult);
        branchEnds.add(fallbackEnd);

        AbstractMergeNode merge = b.append(new MergeNode());
        for (EndNode end : branchEnds) {
            merge.addForwardEnd(end);
        }
        if (returnKind != JavaKind.Void) {
            ValuePhiNode phi = new ValuePhiNode(StampFactory.forKind(returnKind), merge,
                            branchResults.toArray(new ValueNode[0]));
            graph.addOrUnique(phi);
            b.push(returnKind, phi);
        }
        b.setStateAfter(merge);

        return true;
    }

    /**
     * Emits one branch's call through the parser's own invoke path, so it gets this bci's exception edge like any other
     * invoke. The dispatch has already ended the current block, so a new {@link BeginNode} is appended after
     * {@code branchBegin} and the invoke after it. The result is popped; the caller appends the branch's {@link EndNode}.
     */
    static ValueNode emitBranchCall(GraphBuilderContext b,
                    BeginNode branchBegin,
                    InvokeKind invokeKind,
                    ResolvedJavaMethod targetMethod,
                    ValueNode[] args,
                    JavaKind returnKind) {
        assert b.hasParseTerminated() : "a branch call must start after a control split or an end";
        StructuredGraph graph = b.getGraph();
        JavaType returnType = targetMethod.getSignature().getReturnType(targetMethod.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        ValueNode[] addedArgs = new ValueNode[args.length];
        for (int i = 0; i < args.length; i++) {
            ValueNode arg = args[i];
            if (arg.isUnregistered()) {
                arg = graph.add(arg);
            }
            addedArgs[i] = arg;
        }
        MethodCallTargetNode callTarget = graph.add(
                        new SubstrateMethodCallTargetNode(invokeKind, targetMethod, addedArgs, returnStamp));
        BeginNode entry = b.append(new BeginNode());
        branchBegin.setNext(entry);
        b.handleReplacedInvoke(callTarget, returnKind);
        return returnKind == JavaKind.Void ? null : b.pop(returnKind);
    }

    /** The invoke at the parser's live position, its result left on the stack (no plugin runs again for it). */
    static void emitCallAtParser(GraphBuilderContext b, InvokeKind invokeKind, ResolvedJavaMethod targetMethod, ValueNode[] args, JavaKind returnKind) {
        JavaType returnType = targetMethod.getSignature().getReturnType(targetMethod.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        b.handleReplacedInvoke(b.getGraph().add(new SubstrateMethodCallTargetNode(invokeKind, targetMethod, args, returnStamp)), returnKind);
    }

    /** The invoke at the parser's live position (Part B's else, after the analysis-only filter); result popped. */
    private static ValueNode emitCallHere(GraphBuilderContext b, InvokeKind invokeKind, ResolvedJavaMethod targetMethod, ValueNode[] args, JavaKind returnKind) {
        JavaType returnType = targetMethod.getSignature().getReturnType(targetMethod.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        MethodCallTargetNode callTarget = b.getGraph().add(new SubstrateMethodCallTargetNode(invokeKind, targetMethod, args, returnStamp));
        b.handleReplacedInvoke(callTarget, returnKind);
        return returnKind == JavaKind.Void ? null : b.pop(returnKind);
    }

    private static Class<?>[] getParamTypes(String methodName) {
        return InlineCacheRegistry.getParamTypes(methodName);
    }

    private ResolvedJavaMethod resolveMethod(GraphBuilderContext b, Class<?> declaringClass, String methodName, Class<?>[] paramTypes) {
        String key = declaringClass.getName() + "#" + methodName;
        ResolvedJavaMethod cached = methodCache.get(key);
        if (cached != null) {
            return cached;
        }
        try {
            Method reflect = declaringClass.getDeclaredMethod(methodName, paramTypes);
            ResolvedJavaMethod resolved = b.getMetaAccess().lookupJavaMethod(reflect);
            methodCache.put(key, resolved);
            return resolved;
        } catch (NoSuchMethodException e) {
            return null;
        }
    }

    private static ProfileEntry lookupInlineCacheEntry(String sourceLocation) {
        if (RepresentationProfileHolder.hasProfile()) {
            return RepresentationProfileHolder.getInstance().getEntry(sourceLocation, OptimizationType.INLINE_CACHE);
        }
        return null;
    }

    private static boolean isRedirectSite(String sourceLocation) {
        if (RepresentationProfileHolder.hasProfile()) {
            ProfileEntry em = RepresentationProfileHolder.getInstance().getEntry(sourceLocation, OptimizationType.EQUALS_MATRIX);
            return em != null && EqualsMatrixHeuristic.VARIANT_REDIRECT.equals(em.getVariant());
        }
        return false;
    }

    private static String sourceLocation(GraphBuilderContext b) {
        return SiteKeys.profileKey(b.getMethod(), b.bci());
    }
}