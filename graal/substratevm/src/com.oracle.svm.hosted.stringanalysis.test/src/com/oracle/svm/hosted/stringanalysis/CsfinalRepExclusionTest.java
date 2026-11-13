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

import java.util.LinkedHashMap;
import java.util.Map;

import org.graalvm.collections.EconomicMap;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.FixedGuardNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.phases.util.Providers;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.DeoptimizationAction;
import jdk.vm.ci.meta.DeoptimizationReason;
import jdk.vm.ci.meta.MetaAccessProvider;

/**
 * The csfinal rep exclusion: the decision ({@code InlineCacheTrivialMethodNodePlugin.csfinalApplies} /
 * {@code siteVariant}) and the analysis-only rep-exclusion diamond. A proper-String-supertype-declared
 * virtual/interface invoke of a String IC member whose site carries an UNKNOWN/EXACT_STRING entry is rep-excluded; a
 * rep list, no entry (also a neighbour or prefix bci), an unmarked JDK-terminal entry, a REDIRECT site,
 * invokespecial/static, a non-member and ic.exactpi=0 are untouched. The diamond {@code If(x instanceof String){marked guard x instanceof exact String}} merged
 * collapses under the strengthen hook (mode 1): no If, no guard, no instanceof left.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases.tiers",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.util",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common",
                "jdk.graal.compiler/jdk.graal.compiler.phases.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.graal.compiler/jdk.graal.compiler.api.replacements",
                "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.spi"})
public class CsfinalRepExclusionTest {

    private static final String M = "com.google.common.base.Splitter$SplittingIterator#computeNext()Ljava/lang/String;";
    private static final String LOC = M + "@35";
    private static final String LOC_EXACT = M + "@118";
    private static final String LOC_REPS = M + "@200";
    private static final String LOC_KT = M + "@260";
    private static final InvokeKind IFACE = InvokeKind.Interface;

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    @Before
    public void installProfile() {
        Map<String, ProfileEntry> entries = new LinkedHashMap<>();
        entries.put(LOC, new ProfileEntry(LOC, OptimizationType.INLINE_CACHE, "UNKNOWN"));
        entries.put(LOC_EXACT, new ProfileEntry(LOC_EXACT, OptimizationType.INLINE_CACHE, "EXACT_STRING"));
        entries.put(LOC_REPS, new ProfileEntry(LOC_REPS, OptimizationType.INLINE_CACHE, "EXACT,StringView"));
        entries.put(LOC_KT, new ProfileEntry(LOC_KT, OptimizationType.INLINE_CACHE, TerminalBodyKinds.KT_PREFIX + "UNKNOWN"));
        RepresentationProfileHolder.setInstance(new RepresentationProfile(entries));
    }

    @After
    public void clearProfile() {
        RepresentationProfileHolder.clear();
    }

    private static boolean applies(InvokeKind kind, String loc, boolean jdkTerminal) {
        return InlineCacheTrivialMethodNodePlugin.csfinalApplies(1, kind, true, true, false, InlineCacheTrivialMethodNodePlugin.siteVariant(loc, jdkTerminal));
    }

    @Test
    public void repFreeEntryIsExcluded() {
        Assert.assertTrue(applies(IFACE, LOC, false));
        Assert.assertTrue(applies(IFACE, LOC_EXACT, false));
        Assert.assertTrue("Object/hashCode-style virtual site", applies(InvokeKind.Virtual, LOC, false));
        Assert.assertTrue("KT-marked entry at a JDK-terminal site", applies(IFACE, LOC_KT, true));
        Assert.assertTrue("CHECK mode keeps the (validating) filter", InlineCacheTrivialMethodNodePlugin.csfinalApplies(2, IFACE, true, true, false, "UNKNOWN"));
    }

    @Test
    public void everythingElseIsUntouched() {
        Assert.assertFalse("no entry", applies(IFACE, M + "@3", false));
        Assert.assertFalse("prefix bci", applies(IFACE, M + "@350", false));
        Assert.assertFalse("rep list", applies(IFACE, LOC_REPS, false));
        Assert.assertFalse("unmarked JDK-terminal", applies(IFACE, LOC, true));
        Assert.assertFalse("special", applies(InvokeKind.Special, LOC, false));
        Assert.assertFalse("static", applies(InvokeKind.Static, LOC, false));
        String v = "UNKNOWN";
        Assert.assertFalse("not a proper String supertype", InlineCacheTrivialMethodNodePlugin.csfinalApplies(1, IFACE, false, true, false, v));
        Assert.assertFalse("not a String IC member", InlineCacheTrivialMethodNodePlugin.csfinalApplies(1, IFACE, true, false, false, v));
        Assert.assertFalse("REDIRECT site", InlineCacheTrivialMethodNodePlugin.csfinalApplies(1, IFACE, true, true, true, v));
        Assert.assertFalse("exactpi=0", InlineCacheTrivialMethodNodePlugin.csfinalApplies(0, IFACE, true, true, false, v));
        RepresentationProfileHolder.clear();
        Assert.assertFalse("no profile", applies(IFACE, LOC, false));
    }

    @Test
    public void knobDefaultAndCensus() {
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.csfinalSummary().startsWith("[string-analysis] ic-csfinal: rep-excluded "));
    }

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    /** The emitted diamond, by hand: under the strengthen hook (mode 1) it collapses to the bare return. */
    @Test
    public void diamondCollapses() throws NoSuchMethodException {
        Assert.assertEquals("default mode", 1, InlineCacheTrivialMethodNodePlugin.EXACT_PI_MODE);
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(CsfinalRepExclusionTest.class.getDeclaredMethod("holder", Object.class))).build();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object(TypeReference.createTrustedWithoutAssumptions(META.lookupJavaType(CharSequence.class))))));
        LogicNode isStr = g.addOrUniqueWithInputs(InstanceOfNode.create(TypeReference.createTrustedWithoutAssumptions(META.lookupJavaType(String.class)), p));
        LogicNode isExact = g.addOrUniqueWithInputs(InstanceOfNode.create(TypeReference.createExactTrusted(META.lookupJavaType(String.class)), p));
        Assert.assertTrue(isStr instanceof InstanceOfNode && isExact instanceof InstanceOfNode);
        BeginNode strBegin = g.add(new BeginNode());
        BeginNode otherBegin = g.add(new BeginNode());
        IfNode ifNode = g.add(new IfNode(isStr, strBegin, otherBegin, BranchProbabilityNode.NOT_FREQUENT_PROFILE));
        g.start().setNext(ifNode);
        FixedGuardNode guard = g.add(new FixedGuardNode(isExact, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER_CSFINAL, false));
        strBegin.setNext(guard);
        EndNode strEnd = g.add(new EndNode());
        guard.setNext(strEnd);
        BeginNode resume = g.add(new BeginNode());
        otherBegin.setNext(resume);
        EndNode otherEnd = g.add(new EndNode());
        resume.setNext(otherEnd);
        MergeNode merge = g.add(new MergeNode());
        merge.addForwardEnd(strEnd);
        merge.addForwardEnd(otherEnd);
        merge.setNext(g.add(new ReturnNode(p)));
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.isCsfinalIf(guard));

        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, true);
        var backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
        Providers providers = new Providers(META, backend.getCodeCache(), backend.getConstantReflection(), null, null, null, null, null, null, null, null, null, null, null);
        CanonicalizerPhase.create().copyWithCustomSimplification((Node n, jdk.graal.compiler.nodes.spi.SimplifierTool tool) -> {
            if (n instanceof FixedGuardNode fg && InlineCacheTrivialMethodNodePlugin.isTrustedFilter(fg)) {
                InlineCacheTrivialMethodNodePlugin.strengthenTrustedFilter(fg, tool);
            }
        }).apply(g, providers);
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, false);

        Assert.assertEquals(0, g.getNodes().filter(FixedGuardNode.class).count());
        Assert.assertEquals("the diamond If folds", 0, g.getNodes().filter(IfNode.class).count());
        Assert.assertEquals("no run-time check left", 0, g.getNodes().filter(InstanceOfNode.class).count());
        Assert.assertEquals(0, g.getNodes().filter(MergeNode.class).count());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.CSF_IFS_PRE.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.CSF_IFS_LEFT.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.PART_B_IFS_PRE.get());
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.trustedFilterSummary().endsWith("attributed=ok"));
    }

    /** A diamond whose marked guard folded to a deopt before strengthen: the strengthen hook folds the If to its false arm. */
    @Test
    public void deadArmDiamondFolds() throws NoSuchMethodException {
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(CsfinalRepExclusionTest.class.getDeclaredMethod("holder", Object.class))).build();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
        LogicNode isStr = g.addOrUniqueWithInputs(InstanceOfNode.create(TypeReference.createTrustedWithoutAssumptions(META.lookupJavaType(String.class)), p));
        BeginNode strBegin = g.add(new BeginNode());
        BeginNode otherBegin = g.add(new BeginNode());
        IfNode ifNode = g.add(new IfNode(isStr, strBegin, otherBegin, BranchProbabilityNode.NOT_FREQUENT_PROFILE));
        g.start().setNext(ifNode);
        strBegin.setNext(g.add(new jdk.graal.compiler.nodes.DeoptimizeNode(DeoptimizationAction.None, DeoptimizationReason.ClassCastException,
                        InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER_CSFINAL)));
        otherBegin.setNext(g.add(new ReturnNode(p)));
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.isCsfinalDeadArm(ifNode));
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, true);
        var backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
        Providers providers = new Providers(META, backend.getCodeCache(), backend.getConstantReflection(), null, null, null, null, null, null, null, null, null, null, null);
        CanonicalizerPhase.create().copyWithCustomSimplification((Node n, jdk.graal.compiler.nodes.spi.SimplifierTool tool) -> {
            if (n instanceof IfNode i) {
                InlineCacheTrivialMethodNodePlugin.strengthenCsfinalDeadArm(i, tool);
            }
        }).apply(g, providers);
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, false);
        Assert.assertEquals(0, g.getNodes().filter(IfNode.class).count());
        Assert.assertEquals(0, g.getNodes().filter(jdk.graal.compiler.nodes.DeoptimizeNode.class).count());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.CSF_DEAD_ARMS_PRE.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.CSF_DEAD_ARMS_FOLDED.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.CSF_IFS_LEFT.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.MARKED_DEOPTS_POST.get());
    }

    /** Builds {@code If(p instanceof String) {guard} else {} merge; return p} with the given guard condition and marker. */
    private static IfNode shape(StructuredGraph g, ParameterNode p, LogicNode guardCond, jdk.vm.ci.meta.SpeculationLog.Speculation marker, boolean[] matched) {
        LogicNode isStr = g.addOrUniqueWithInputs(InstanceOfNode.create(TypeReference.createTrustedWithoutAssumptions(META.lookupJavaType(String.class)), p));
        BeginNode strBegin = g.add(new BeginNode());
        BeginNode otherBegin = g.add(new BeginNode());
        IfNode ifNode = g.add(new IfNode(isStr, strBegin, otherBegin, BranchProbabilityNode.NOT_FREQUENT_PROFILE));
        g.start().setNext(ifNode);
        FixedGuardNode guard = g.add(new FixedGuardNode(guardCond, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, marker, false));
        strBegin.setNext(guard);
        EndNode e1 = g.add(new EndNode());
        guard.setNext(e1);
        EndNode e2 = g.add(new EndNode());
        otherBegin.setNext(e2);
        MergeNode merge = g.add(new MergeNode());
        merge.addForwardEnd(e1);
        merge.addForwardEnd(e2);
        merge.setNext(g.add(new ReturnNode(p)));
        matched[0] = InlineCacheTrivialMethodNodePlugin.isCsfinalIf(guard);
        return ifNode;
    }

    /** A user {@code instanceof String} If whose true arm starts with a Part-A guard (see InlineCacheTrivialMethodNodePlugin) is not a csfinal diamond. */
    @Test
    public void censusIgnoresUserInstanceofWithPartAGuard() throws NoSuchMethodException {
        TypeReference exactString = TypeReference.createExactTrusted(META.lookupJavaType(String.class));
        boolean[] m = new boolean[1];
        for (int variant = 0; variant < 3; variant++) {
            DebugContext debug = new DebugContext.Builder(OPTIONS).build();
            StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(CsfinalRepExclusionTest.class.getDeclaredMethod("holder", Object.class))).build();
            ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
            switch (variant) {
                case 0 -> { // Part A: allow-null exact guard with the generic marker
                    shape(g, p, g.addOrUniqueWithInputs(InstanceOfNode.createAllowNull(exactString, p, null, null)), InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER, m);
                    Assert.assertFalse("Part-A guard after a user instanceof", m[0]);
                }
                case 1 -> { // the csfinal condition but the generic marker
                    shape(g, p, g.addOrUniqueWithInputs(InstanceOfNode.create(exactString, p)), InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER, m);
                    Assert.assertFalse("generic marker", m[0]);
                }
                default -> { // the emitted shape
                    shape(g, p, g.addOrUniqueWithInputs(InstanceOfNode.create(exactString, p)), InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER_CSFINAL, m);
                    Assert.assertTrue("the emitted csfinal shape", m[0]);
                }
            }
        }
    }

    /**
     * Points-to: the diamond's merged receiver state, computed with the rules of
     * {@code MethodTypeFlowBuilder.handleCondition} + {@code FilterTypeFlow.processInputState} (true arm: intersect with the
     * String hierarchy without null, then with exact String without null; false arm: subtract the String hierarchy, null
     * kept). A model of the filters on real JVMCI types (no analysis run): reps out, String/StringBuilder/null kept.
     */
    @Test
    public void mergedStateDropsOnlyReps() {
        jdk.vm.ci.meta.ResolvedJavaType str = META.lookupJavaType(String.class);
        java.util.List<jdk.vm.ci.meta.ResolvedJavaType> in = java.util.List.of(str, META.lookupJavaType(com.oracle.svm.core.stringrep.StringView.class),
                        META.lookupJavaType(com.oracle.svm.core.stringrep.SingleByteString.class), META.lookupJavaType(StringBuilder.class), META.lookupJavaType(java.nio.CharBuffer.class));
        java.util.Set<String> merged = new java.util.TreeSet<>();
        for (jdk.vm.ci.meta.ResolvedJavaType t : in) {
            boolean trueArm = str.isAssignableFrom(t) && t.equals(str); // non-exact filter, then the exact guard
            boolean falseArm = !str.isAssignableFrom(t); // negated non-exact filter
            if (trueArm || falseArm) {
                merged.add(t.toJavaName());
            }
        }
        merged.add("null"); // false arm: includeNull = !isTrue ^ allowsNull = true
        Assert.assertEquals(new java.util.TreeSet<>(java.util.List.of("java.lang.String", "java.lang.StringBuilder", "java.nio.CharBuffer", "null")), merged);
    }

    /** The child's variant for a truncated walk is UNPROVEN (pure). */
    @Test
    public void receiverVariantMarksTruncatedWalks() {
        java.util.Set<String> none = java.util.Set.of();
        java.util.Set<String> exact = java.util.Set.of("EXACT");
        java.util.Set<String> sv = new java.util.LinkedHashSet<>(java.util.List.of("SV"));
        Assert.assertEquals("UNKNOWN", InlineCacheProfilingHeuristic.receiverVariant(false, false, none, none));
        Assert.assertEquals("EXACT_STRING", InlineCacheProfilingHeuristic.receiverVariant(true, false, exact, none));
        Assert.assertEquals("EXACT,SV", InlineCacheProfilingHeuristic.receiverVariant(true, false, exact, sv));
        Assert.assertEquals("UNPROVEN", InlineCacheProfilingHeuristic.receiverVariant(true, true, exact, none));
        Assert.assertEquals("UNPROVEN", InlineCacheProfilingHeuristic.receiverVariant(true, true, exact, sv));
        Assert.assertFalse("UNPROVEN is no csfinal proof", InlineCacheTrivialMethodNodePlugin.csfinalApplies(1, IFACE, true, true, false, "UNPROVEN"));
    }

    /**
     * Child premise: a CharSequence-declared site (the builder's String-labelled vertex) whose receiver
     * chain reaches an admitted rep gets the rep list; the same chain beyond the walk's depth limit gets UNPROVEN, never
     * EXACT_STRING/UNKNOWN.
     */
    @Test
    public void childPremiseRepListAndUnproven() throws NoSuchMethodException {
        Assert.assertEquals("SBS", childVariant(2));
        Assert.assertEquals("UNPROVEN", childVariant(9));
    }

    private static String childVariant(int chain) throws NoSuchMethodException {
        StringUtilizationGraph sug = new StringUtilizationGraph();
        java.util.List<SourceTag> tags = new java.util.ArrayList<>();
        SugVertex rep = sug.newVertex();
        rep.setNodeType(SugNodeType.STRING_METHOD_CALL);
        SugVertex prev = rep;
        for (int i = 0; i < chain; i++) { // intermediate String calls: the receiver of each is the previous result
            SugVertex mid = sug.newVertex();
            mid.setNodeType(SugNodeType.STRING_METHOD_CALL);
            mid.setDeclaringClass("java.lang.String");
            mid.setMethodName("trim");
            tags.add(new SourceTag(prev, UsageRole.RECEIVER, 0));
            mid.getSourceTags().set(tags.size() - 1);
            prev = mid;
        }
        SugVertex site = sug.newVertex();
        site.setNodeType(SugNodeType.STRING_METHOD_CALL);
        site.setDeclaringClass("java.lang.String");
        site.setMethodName("length");
        site.setMethodSignature(TerminalBodyKinds.usageSignature(String.class.getMethod("length")));
        site.setLabel("CharSequence.length");
        tags.add(new SourceTag(prev, UsageRole.RECEIVER, 0));
        site.getSourceTags().set(tags.size() - 1);
        sug.setSourceTags(tags);
        java.util.List<InstrumentationDecision> validated = java.util.List.of(new InstrumentationDecision(rep, OptimizationType.SINGLE_BYTE, null));
        for (InstrumentationDecision d : new InlineCacheProfilingHeuristic().apply(sug, validated)) {
            if (d.getType() == OptimizationType.INLINE_CACHE && d.getCandidate() == site) {
                return d.getVariant();
            }
        }
        return "no entry";
    }
}
