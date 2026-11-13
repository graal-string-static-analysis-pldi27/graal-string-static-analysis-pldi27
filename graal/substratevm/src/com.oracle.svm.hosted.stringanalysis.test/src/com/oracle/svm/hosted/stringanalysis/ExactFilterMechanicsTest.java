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

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.DeoptimizeNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.FixedGuardNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.phases.util.Providers;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.DeoptimizationAction;
import jdk.vm.ci.meta.DeoptimizationReason;
import jdk.vm.ci.meta.MetaAccessProvider;

/**
 * The mechanics of the zero-cost exact filters without an image build. Hand-built graphs in the shapes the plugin
 * emits ({@code InlineCacheTrivialMethodNodePlugin}; Part A: a marked exact-String guard anchoring a Pi; Part B: an
 * analysis-only {@code If(instanceof exact SBS)} arm holding a marked guard on the same condition, then the marked
 * exact-String guard,
 * merged) go through the census hooks and a canonicalizer whose custom simplification is the strengthen hook
 * ({@code SubstrateStrengthenGraphs.simplifyDelegate}'s call). Mode 1 (the default): every marked guard is removed, the
 * Part-B If folds away, and the census attributes every guard (folded-to-throw and killed-as-dead included).
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
public class ExactFilterMechanicsTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    private static StructuredGraph newGraph() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        return new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(ExactFilterMechanicsTest.class.getDeclaredMethod("holder", Object.class))).build();
    }

    private static Providers providers() {
        var backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
        return new Providers(META, backend.getCodeCache(), backend.getConstantReflection(), null, null, null, null, null, null, null, null, null, null, null);
    }

    private static FixedGuardNode marked(StructuredGraph g, LogicNode cond) {
        return g.add(new FixedGuardNode(cond, DeoptimizationReason.ClassCastException, DeoptimizationAction.None, InlineCacheTrivialMethodNodePlugin.TRUSTED_FILTER, false));
    }

    private static TypeReference exact(Class<?> c) {
        return TypeReference.createExactTrusted(META.lookupJavaType(c));
    }

    private static ParameterNode param(StructuredGraph g) {
        return g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
    }

    /** Runs the strengthen sequence: pre census, canonicalize with the strengthen hook, post census. */
    private static void strengthen(StructuredGraph g) {
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, true);
        CanonicalizerPhase.create().copyWithCustomSimplification((Node n, jdk.graal.compiler.nodes.spi.SimplifierTool tool) -> {
            if (n instanceof FixedGuardNode guard && InlineCacheTrivialMethodNodePlugin.isTrustedFilter(guard)) {
                InlineCacheTrivialMethodNodePlugin.strengthenTrustedFilter(guard, tool);
            }
        }).apply(g, providers());
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, false);
    }

    private static long count(StructuredGraph g, Class<? extends Node> c) {
        return g.getNodes().filter(c).count();
    }

    @Test
    public void partAGuardIsRemovedAndThePiStays() throws NoSuchMethodException {
        Assert.assertEquals("default mode", 1, InlineCacheTrivialMethodNodePlugin.EXACT_PI_MODE);
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        StructuredGraph g = newGraph();
        ParameterNode p = param(g);
        LogicNode isString = g.addOrUniqueWithInputs(InstanceOfNode.createAllowNull(exact(String.class), p, null, null));
        FixedGuardNode guard = marked(g, isString);
        g.start().setNext(guard);
        ValueNode pi = g.addOrUnique(new PiNode(p, StampFactory.object(exact(String.class)), guard));
        guard.setNext(g.add(new ReturnNode(pi)));
        strengthen(g);
        Assert.assertEquals(0, count(g, FixedGuardNode.class));
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.PRESENT_PRE.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.REMOVED.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.SURVIVING.get());
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.trustedFilterSummary(), InlineCacheTrivialMethodNodePlugin.trustedFilterSummary().endsWith("attributed=ok"));
    }

    /** Part B with two flat arms: both arm Ifs fold, one return of the original receiver is left, no compare. */
    @Test
    public void partBArmsCollapse() throws NoSuchMethodException {
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        StructuredGraph g = newGraph();
        ParameterNode p = param(g);
        MergeNode merge = g.add(new MergeNode());
        BeginNode current = null;
        for (Class<?> flat : new Class<?>[]{SingleByteString.class, com.oracle.svm.core.stringrep.TrivialString.class}) {
            LogicNode isFlat = g.addOrUniqueWithInputs(InstanceOfNode.create(exact(flat), p));
            BeginNode flatBegin = g.add(new BeginNode());
            BeginNode otherBegin = g.add(new BeginNode());
            IfNode ifNode = g.add(new IfNode(isFlat, flatBegin, otherBegin, BranchProbabilityNode.SLOW_PATH_PROFILE));
            if (current == null) {
                g.start().setNext(ifNode);
            } else {
                current.setNext(ifNode);
            }
            FixedGuardNode flatGuard = marked(g, isFlat);
            flatBegin.setNext(flatGuard);
            EndNode e = g.add(new EndNode());
            flatGuard.setNext(e);
            merge.addForwardEnd(e);
            BeginNode resume = g.add(new BeginNode());
            otherBegin.setNext(resume);
            current = resume;
        }
        FixedGuardNode strGuard = marked(g, g.addOrUniqueWithInputs(InstanceOfNode.createAllowNull(exact(String.class), p, null, null)));
        current.setNext(strGuard);
        EndNode last = g.add(new EndNode());
        strGuard.setNext(last);
        merge.addForwardEnd(last);
        merge.setNext(g.add(new ReturnNode(p)));
        strengthen(g);
        Assert.assertEquals(0, count(g, FixedGuardNode.class));
        Assert.assertEquals("the arm Ifs fold", 0, count(g, IfNode.class));
        Assert.assertEquals("no compare left", 0, count(g, InstanceOfNode.class));
        Assert.assertEquals(0, count(g, MergeNode.class));
        Assert.assertEquals(3, InlineCacheTrivialMethodNodePlugin.PRESENT_PRE.get());
        Assert.assertEquals(3, InlineCacheTrivialMethodNodePlugin.REMOVED.get());
        Assert.assertEquals(2, InlineCacheTrivialMethodNodePlugin.PART_B_IFS_PRE.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.PART_B_IFS_LEFT.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.SURVIVING.get());
    }

    /** A marked guard on a failing constant is attributed folded-to-throw (an unconditional marked deopt is left). */
    @Test
    public void constantFailureIsFoldedToThrow() throws NoSuchMethodException {
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        StructuredGraph g = newGraph();
        ParameterNode p = param(g);
        FixedGuardNode guard = marked(g, LogicConstantNode.contradiction(g));
        g.start().setNext(guard);
        guard.setNext(g.add(new ReturnNode(p)));
        strengthen(g);
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.FOLDED_TO_THROW.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.MARKED_DEOPTS_POST.get());
        Assert.assertEquals(1, count(g, DeoptimizeNode.class));
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.REMOVED.get());
        Assert.assertEquals(0, InlineCacheTrivialMethodNodePlugin.SURVIVING.get());
    }

    /** A marked guard deleted with its dead branch (no strengthen visit) is attributed killed-as-dead; a live one survives. */
    @Test
    public void deadKillAndSurvivorAreAttributed() throws NoSuchMethodException {
        InlineCacheTrivialMethodNodePlugin.resetCensus();
        StructuredGraph g = newGraph();
        ParameterNode p = param(g);
        LogicNode isFlat = g.addOrUniqueWithInputs(InstanceOfNode.create(exact(SingleByteString.class), p));
        BeginNode deadBegin = g.add(new BeginNode());
        BeginNode liveBegin = g.add(new BeginNode());
        IfNode ifNode = g.add(new IfNode(isFlat, deadBegin, liveBegin, BranchProbabilityNode.SLOW_PATH_PROFILE));
        g.start().setNext(ifNode);
        FixedGuardNode deadGuard = marked(g, isFlat);
        deadBegin.setNext(deadGuard);
        deadGuard.setNext(g.add(new ReturnNode(p)));
        FixedGuardNode liveGuard = marked(g, g.addOrUniqueWithInputs(InstanceOfNode.createAllowNull(exact(String.class), p, null, null)));
        liveBegin.setNext(liveGuard);
        liveGuard.setNext(g.add(new ReturnNode(p)));
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, true);
        // the strengthen-time kill of a dead branch, then no simplification at all (mode 2's survivor)
        ifNode.setTrueSuccessor(null);
        GraphUtil.killCFG(deadBegin);
        InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, false);
        Assert.assertEquals(2, InlineCacheTrivialMethodNodePlugin.PRESENT_PRE.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.KILLED_DEAD.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.SURVIVING.get());
        Assert.assertEquals(1, InlineCacheTrivialMethodNodePlugin.PART_B_IFS_LEFT.get());
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.trustedFilterSummary().endsWith("attributed=ok"));
    }
}
