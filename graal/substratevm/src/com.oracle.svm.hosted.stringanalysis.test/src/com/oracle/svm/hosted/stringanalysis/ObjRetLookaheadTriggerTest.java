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

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.LoopExitNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.ValueProxyNode;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.code.BytecodeFrame;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The pure parts of the print-only lookahead trigger (the pure-forwarder test on
 * hand-built graphs, the certain-refusal truth table), the unframed-cause classifier and its teachable candidates, and
 * the nest-navigation link/API tables.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.core.common"})
public class ObjRetLookaheadTriggerTest {
    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    static Object sink;

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    private static StructuredGraph newGraph() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        return new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(ObjRetLookaheadTriggerTest.class.getDeclaredMethod("holder", Object.class))).build();
    }

    private static ParameterNode param(StructuredGraph g) {
        return g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
    }

    /** An invoke {@code x.toString()} (its result is the value under test). */
    private static InvokeNode toStringCall(StructuredGraph g, ValueNode x) throws NoSuchMethodException {
        ResolvedJavaMethod ts = META.lookupJavaMethod(Object.class.getDeclaredMethod("toString"));
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(InvokeKind.Virtual, ts, new ValueNode[]{x}, StampPair.createSingle(StampFactory.object()), null));
        InvokeNode inv = g.add(new InvokeNode(ct, 0));
        g.start().setNext(inv);
        return inv;
    }

    @Test
    public void directReturnIsAForwarder() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        InvokeNode inv = toStringCall(g, param(g));
        Assert.assertFalse("no use at all: no Return reached", ObjRetRules.pureForwarder(inv));
        inv.setNext(g.add(new ReturnNode(inv)));
        Assert.assertTrue(ObjRetRules.pureForwarder(inv));
        g.add(new FrameState(BytecodeFrame.AFTER_BCI, inv));
        Assert.assertTrue("frame states are ignored", ObjRetRules.pureForwarder(inv));
    }

    @Test
    public void phiProxyAndConditionalToReturnAreForwarders() throws NoSuchMethodException {
        // String.valueOf(Object): (obj == null) ? "null" : obj.toString() -- the result merges with a constant, then returns
        StructuredGraph g = newGraph();
        ParameterNode p = param(g);
        InvokeNode inv = toStringCall(g, p);
        MergeNode merge = g.add(new MergeNode());
        ValuePhiNode phi = g.addWithoutUnique(new ValuePhiNode(StampFactory.object(), merge, inv, p));
        g.add(new ReturnNode(phi));
        Assert.assertTrue(ObjRetRules.pureForwarder(inv));

        StructuredGraph g2 = newGraph();
        InvokeNode inv2 = toStringCall(g2, param(g2));
        LoopBeginNode loop = g2.add(new LoopBeginNode());
        LoopExitNode exit = g2.add(new LoopExitNode(loop));
        ValueProxyNode proxy = g2.addWithoutUnique(new ValueProxyNode(inv2, exit));
        g2.add(new ReturnNode(proxy));
        Assert.assertTrue("a loop-exit proxy carries the value on", ObjRetRules.pureForwarder(inv2));

        StructuredGraph g3 = newGraph();
        ParameterNode p3 = param(g3);
        InvokeNode inv3 = toStringCall(g3, p3);
        LogicNode isNull = g3.addOrUniqueWithInputs(IsNullNode.create(p3));
        ConditionalNode cond = g3.addWithoutUnique(new ConditionalNode(isNull, p3, inv3));
        g3.add(new ReturnNode(cond));
        Assert.assertTrue("a conditional's value arm carries the value on", ObjRetRules.pureForwarder(inv3));
    }

    @Test
    public void anyOtherUseIsNotAForwarder() throws NoSuchMethodException, NoSuchFieldException {
        // a store (StringBuilder.append(Object)'s shape: the value goes into the builder) next to the return
        StructuredGraph g = newGraph();
        InvokeNode inv = toStringCall(g, param(g));
        g.add(new ReturnNode(inv));
        g.add(new StoreFieldNode(null, META.lookupJavaField(ObjRetLookaheadTriggerTest.class.getDeclaredField("sink")), inv));
        Assert.assertFalse(ObjRetRules.pureForwarder(inv));

        // a Pi (its arm test depends on the atom: piArmDead) is not followed
        StructuredGraph g2 = newGraph();
        InvokeNode inv2 = toStringCall(g2, param(g2));
        PiNode pi = g2.addWithoutUnique(new PiNode(inv2, StampFactory.objectNonNull()));
        g2.add(new ReturnNode(pi));
        Assert.assertFalse(ObjRetRules.pureForwarder(inv2));

        // the value as an argument of another call (consumed), then the call's result returned
        StructuredGraph g3 = newGraph();
        InvokeNode inv3 = toStringCall(g3, param(g3));
        ResolvedJavaMethod h = META.lookupJavaMethod(ObjRetLookaheadTriggerTest.class.getDeclaredMethod("holder", Object.class));
        MethodCallTargetNode ct = g3.add(new MethodCallTargetNode(InvokeKind.Static, h, new ValueNode[]{inv3}, StampPair.createSingle(StampFactory.object()), null));
        InvokeNode outer = g3.add(new InvokeNode(ct, 1));
        g3.add(new ReturnNode(outer));
        Assert.assertFalse(ObjRetRules.pureForwarder(inv3));

        // a phi that also feeds a store
        StructuredGraph g4 = newGraph();
        ParameterNode p4 = param(g4);
        InvokeNode inv4 = toStringCall(g4, p4);
        MergeNode merge = g4.add(new MergeNode());
        ValuePhiNode phi = g4.addWithoutUnique(new ValuePhiNode(StampFactory.object(), merge, inv4, p4));
        g4.add(new ReturnNode(phi));
        g4.add(new StoreFieldNode(null, META.lookupJavaField(ObjRetLookaheadTriggerTest.class.getDeclaredField("sink")), phi));
        Assert.assertFalse(ObjRetRules.pureForwarder(inv4));
    }

    @Test
    public void certainRefusalTruthTable() {
        int cap = RecursiveTracking.RETURN_FAN_CAP;
        for (int bits = 0; bits < 32; bits++) {
            boolean hidden = (bits & 1) != 0;
            boolean incomplete = (bits & 2) != 0;
            boolean over = (bits & 4) != 0;
            boolean outside = (bits & 8) != 0;
            boolean below = (bits & 16) != 0;
            boolean expect = !hidden && (incomplete || over || outside || below);
            Assert.assertEquals("bits=" + bits, expect, ObjRetRules.certainRefusal(hidden, incomplete, over ? cap + 1 : cap, cap, outside, below));
        }
        // the fan cap is exclusive (callers.size() > RETURN_FAN_CAP refuses)
        Assert.assertFalse(ObjRetRules.certainRefusal(false, false, cap, cap, false, false));
        Assert.assertTrue(ObjRetRules.certainRefusal(false, false, 87, cap, false, false));
        Assert.assertTrue(ObjRetRules.LOOKAHEAD_DEPTH >= 1);
    }

    @Test
    public void unframedCauseOrder() {
        // a class initializer first, split by its build-time state
        Assert.assertEquals(ObjRetRules.UnframedCause.CLINIT_BUILD_TIME, ObjRetRules.unframedCause(true, true, true, true, true, true, true, true, true, true, true));
        Assert.assertEquals(ObjRetRules.UnframedCause.CLINIT_SIMULATED, ObjRetRules.unframedCause(true, false, true, false, false, true, false, true, false, false, false));
        Assert.assertEquals(ObjRetRules.UnframedCause.CLINIT_RUNTIME, ObjRetRules.unframedCause(true, false, false, false, false, true, false, true, false, false, false));
        Assert.assertEquals(ObjRetRules.UnframedCause.NATIVE, ObjRetRules.unframedCause(false, true, true, true, true, true, true, true, true, true, true));
        Assert.assertEquals(ObjRetRules.UnframedCause.INTRINSIC, ObjRetRules.unframedCause(false, false, false, false, true, true, true, true, true, true, true));
        Assert.assertEquals(ObjRetRules.UnframedCause.INLINED_ONLY, ObjRetRules.unframedCause(false, false, false, false, false, false, true, true, true, true, true));
        // inlined but also implementation-invoked: the body runs without a frame somewhere
        Assert.assertEquals(ObjRetRules.UnframedCause.NO_FLOWS, ObjRetRules.unframedCause(false, false, false, false, false, true, true, true, false, false, false));
        Assert.assertEquals(ObjRetRules.UnframedCause.NOT_POINTSTO, ObjRetRules.unframedCause(false, false, false, false, false, true, false, false, false, false, false));
        Assert.assertEquals(ObjRetRules.UnframedCause.STUB, ObjRetRules.unframedCause(false, false, false, false, false, true, false, true, true, true, false));
        Assert.assertEquals(ObjRetRules.UnframedCause.NO_IR, ObjRetRules.unframedCause(false, false, false, false, false, true, false, true, true, false, true));
        Assert.assertEquals(ObjRetRules.UnframedCause.OTHER, ObjRetRules.unframedCause(false, false, false, false, false, true, false, true, true, false, false));
    }

    @Test
    public void teachableCandidatesAreOnlyBuildTimeInitAndInlinedBodies() {
        Set<ObjRetRules.UnframedCause> yes = EnumSet.of(ObjRetRules.UnframedCause.CLINIT_BUILD_TIME, ObjRetRules.UnframedCause.CLINIT_SIMULATED, ObjRetRules.UnframedCause.INLINED_ONLY);
        for (ObjRetRules.UnframedCause c : ObjRetRules.UnframedCause.values()) {
            Assert.assertEquals(c.name(), yes.contains(c), ObjRetRules.teachableCandidate(c));
        }
    }

    @Test
    public void navigationTables() {
        Set<String> union = new HashSet<>();
        for (ObjRetRules.NavLink l : ObjRetRules.NavLink.values()) {
            Set<String> apis = ObjRetRules.navApis(l);
            Assert.assertFalse(l.name(), apis.isEmpty());
            union.addAll(apis);
            for (String a : apis) {
                // every API is a real Class method returning a Class, a Class[] or an executable
                boolean found = false;
                for (java.lang.reflect.Method m : Class.class.getMethods()) {
                    found |= m.getName().equals(a) && m.getParameterCount() == 0;
                }
                Assert.assertTrue(a, found);
            }
        }
        Assert.assertEquals(ObjRetRules.NAV_APIS, union);
        Assert.assertEquals(Set.of("getNestHost"), ObjRetRules.navApis(ObjRetRules.NavLink.NEST_HOST));
        Assert.assertTrue(ObjRetRules.navApis(ObjRetRules.NavLink.DECLARING).contains("getEnclosingClass"));
        Assert.assertTrue(ObjRetRules.navApis(ObjRetRules.NavLink.COMPONENT).contains("componentType"));
        // the hub-internal holder slots a use-based rule may discount, and nothing else
        Assert.assertTrue(ObjRetRules.navHolderSlot("com.oracle.svm.core.hub.DynamicHubCompanion", "nestHost"));
        Assert.assertTrue(ObjRetRules.navHolderSlot("com.oracle.svm.core.hub.DynamicHubCompanion", "declaringClass"));
        Assert.assertTrue(ObjRetRules.navHolderSlot("com.oracle.svm.core.hub.DynamicHub", "componentType"));
        Assert.assertFalse(ObjRetRules.navHolderSlot("com.oracle.svm.core.hub.DynamicHubCompanion", "superHub"));
        Assert.assertFalse(ObjRetRules.navHolderSlot("com.oracle.svm.core.hub.DynamicHubCompanion", "arrayHub"));
        Assert.assertFalse(ObjRetRules.navHolderSlot("java.lang.invoke.MethodType", "rtype"));
        // the scan's own name list never takes a receiver method the harmless-use walk accepts (they answer no Class)
        for (String a : ObjRetRules.NAV_APIS) {
            Assert.assertFalse(a, ObjRetRules.RECEIVER_OK.contains(a));
        }
    }
}
