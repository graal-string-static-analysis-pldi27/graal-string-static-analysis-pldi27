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

import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.hosted.code.InliningUtilities;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.NodeBitMap;
import jdk.graal.compiler.nodes.AbstractBeginNode;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.UnwindNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.extended.LoadHubNode;
import jdk.graal.compiler.nodes.extended.ValueAnchorNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.ConstantReflectionProvider;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Inlining parity: the trivial-method count skips the IC chain's rep-arm
 * dispatch nodes. A hand-built wrapper in the chain shape ({@code If(instanceof exact StringView)}, an arm calling
 * {@code StringView.length} on the arm's rep Pi with its exception edge, else the flat {@code String.length}, merged
 * with a phi) is not trivial under the stock count (2 invokes) and is trivial with the discount. The target is checked
 * directly: the discounted count of a chain graph equals the stock count of its flat twin (the same
 * method without the chain), also with a floating else value, an exception merge with two non-dispatch ends (the
 * hosted toRootLowerCase shape) and the class-compare forms. An arm with a non-dispatch node, a call not on the arm's
 * rep Pi, a non-rep test or constant, or a graph owned by a rep method: no discount. Inactive (OFF images, knob 0) =
 * the stock count.
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
                "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common",
                "jdk.graal.compiler/jdk.graal.compiler.phases.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.graal.compiler/jdk.graal.compiler.api.replacements",
                "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.spi"})
public class RepDispatchAccountingTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final ConstantReflectionProvider CR = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    @SuppressWarnings("unused")
    static int holder(String s) {
        return s.length();
    }

    private static ResolvedJavaMethod m(Class<?> c, String name) throws NoSuchMethodException {
        return META.lookupJavaMethod(c.getDeclaredMethod(name));
    }

    /** The rep test of the chain's If. */
    enum Form {
        INSTANCEOF,
        GETCLASS_EQ,
        LOADHUB_EQ
    }

    /** One graph shape; the defaults are the chain wrapper of the IC emitter (one arm, instanceof exact StringView). */
    static final class Shape {
        boolean chain = true; // false: the flat twin (the same method without the chain)
        boolean extraArmCall;
        Class<?> testType = StringView.class;
        Form test = Form.INSTANCEOF;
        boolean armReceiverIsParameter; // the arm's call is not on the arm's rep Pi
        boolean mergedExceptions; // a preceding flat call; every exception edge goes into one exception merge
        boolean floatingElse; // the else value feeding the phi is a floating node (flat + 1)
        boolean repOwner; // the graph belongs to a rep method
        boolean exactFirst; // an If(instanceof exact String) in front of the arm, its true end merged with the chain's fall-through before the flat call

        Shape with(java.util.function.Consumer<Shape> c) {
            c.accept(this);
            return this;
        }
    }

    /** Appends {@code invoke target(recv)} with an exception edge after {@code begin}; returns the invoke. */
    private static InvokeWithExceptionNode call(StructuredGraph g, AbstractBeginNode begin, ResolvedJavaMethod target, ValueNode recv, MergeNode excMerge) {
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(InvokeKind.Special, target, new ValueNode[]{recv}, StampPair.createSingle(StampFactory.forKind(target.getSignature().getReturnKind())),
                        null));
        ExceptionObjectNode eo = g.add(new ExceptionObjectNode(META));
        if (excMerge == null) {
            eo.setNext(g.add(new UnwindNode(eo)));
        } else {
            EndNode e = g.add(new EndNode());
            eo.setNext(e);
            excMerge.addForwardEnd(e);
        }
        InvokeWithExceptionNode inv = g.add(new InvokeWithExceptionNode(ct, eo, 0));
        begin.setNext(inv);
        inv.setNext(g.add(new BeginNode()));
        return inv;
    }

    private static LogicNode repTest(StructuredGraph g, Shape s, ValueNode p) {
        ResolvedJavaType t = META.lookupJavaType(s.testType);
        return switch (s.test) {
            case INSTANCEOF -> g.addOrUnique(InstanceOfNode.create(TypeReference.createExactTrusted(t), p));
            case GETCLASS_EQ -> g.addOrUnique(new ObjectEqualsNode(g.addOrUnique(new GetClassNode(StampFactory.objectNonNull(TypeReference.createTrusted(null, META.lookupJavaType(Class.class))), p)),
                            ConstantNode.forConstant(CR.asJavaClass(t), META, g)));
            case LOADHUB_EQ -> g.addOrUnique(new ObjectEqualsNode(ConstantNode.forConstant(CR.asJavaClass(t), META, g), g.addOrUnique(new LoadHubNode(StampFactory.objectNonNull(), p))));
        };
    }

    private static StructuredGraph build(Shape s) throws NoSuchMethodException {
        ResolvedJavaMethod own = s.repOwner ? m(StringView.class, "length") : META.lookupJavaMethod(RepDispatchAccountingTest.class.getDeclaredMethod("holder", String.class));
        StructuredGraph g = new StructuredGraph.Builder(OPTIONS, new DebugContext.Builder(OPTIONS).build()).method(own).build();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        MergeNode excMerge = null;
        AbstractBeginNode cur = g.start();
        if (s.mergedExceptions) {
            excMerge = g.add(new MergeNode());
            cur = call(g, cur, m(String.class, "hashCode"), p, excMerge).next();
        }
        ValueNode result;
        if (!s.chain) {
            InvokeWithExceptionNode flat = call(g, cur, m(String.class, "length"), p, excMerge);
            result = s.floatingElse ? g.addOrUnique(new AddNode(flat.asNode(), ConstantNode.forInt(1, g))) : flat.asNode();
            flat.next().setNext(g.add(new ReturnNode(result)));
        } else {
            EndNode strEnd = null;
            if (s.exactFirst) {
                BeginNode strBegin = g.add(new BeginNode());
                BeginNode chainBegin = g.add(new BeginNode());
                cur.setNext(g.add(new IfNode(g.addOrUnique(InstanceOfNode.create(TypeReference.createExactTrusted(META.lookupJavaType(String.class)), p)), strBegin, chainBegin,
                                BranchProbabilityNode.FAST_PATH_PROFILE)));
                strEnd = g.add(new EndNode());
                strBegin.setNext(strEnd);
                cur = chainBegin;
            }
            BeginNode armBegin = g.add(new BeginNode());
            BeginNode elseBegin = g.add(new BeginNode());
            cur.setNext(g.add(new IfNode(repTest(g, s, p), armBegin, elseBegin, BranchProbabilityNode.FAST_PATH_PROFILE)));
            Class<?> piType = StringView.class.isAssignableFrom(s.testType) || s.testType.getSuperclass() == String.class ? s.testType : StringView.class;
            ValueNode pi = g.addOrUnique(new PiNode(p, StampFactory.objectNonNull(TypeReference.createExactTrusted(META.lookupJavaType(piType))), armBegin));
            ValueNode armRecv = s.armReceiverIsParameter ? p : pi;
            InvokeWithExceptionNode armCall = call(g, armBegin, m(StringView.class, "length"), armRecv, excMerge);
            AbstractBeginNode armTail = armCall.next();
            if (s.extraArmCall) {
                armTail = call(g, armTail, m(StringView.class, "length"), armRecv, excMerge).next();
            }
            EndNode armEnd = g.add(new EndNode());
            ValueAnchorNode anchor = g.add(new ValueAnchorNode()); // the parser's anchor after a begin, as in the hosted graphs
            armTail.setNext(anchor);
            anchor.setNext(armEnd);
            AbstractBeginNode elseStart = elseBegin;
            if (s.exactFirst) {
                EndNode fallThrough = g.add(new EndNode());
                elseBegin.setNext(fallThrough);
                MergeNode m1 = g.add(new MergeNode());
                m1.addForwardEnd(strEnd);
                m1.addForwardEnd(fallThrough);
                elseStart = m1;
            }
            InvokeWithExceptionNode flat = call(g, elseStart, m(String.class, "length"), p, excMerge);
            ValueNode elseValue = s.floatingElse ? g.addOrUnique(new AddNode(flat.asNode(), ConstantNode.forInt(1, g))) : flat.asNode();
            EndNode elseEnd = g.add(new EndNode());
            flat.next().setNext(elseEnd);
            MergeNode merge = g.add(new MergeNode());
            merge.addForwardEnd(armEnd);
            merge.addForwardEnd(elseEnd);
            result = g.addOrUnique(new ValuePhiNode(StampFactory.forKind(JavaKind.Int), merge, armCall.asNode(), elseValue));
            merge.setNext(g.add(new ReturnNode(result)));
        }
        if (excMerge != null) {
            ValueNode[] eos = new ValueNode[excMerge.forwardEndCount()];
            for (int i = 0; i < eos.length; i++) {
                eos[i] = (ValueNode) excMerge.forwardEndAt(i).predecessor();
            }
            ValuePhiNode ephi = g.addOrUnique(new ValuePhiNode(StampFactory.objectNonNull(), excMerge, eos));
            excMerge.setNext(g.add(new UnwindNode(ephi)));
        }
        return g;
    }

    private static StructuredGraph wrapper(boolean extraArmCall, Class<?> testType) throws NoSuchMethodException {
        return build(new Shape().with(s -> {
            s.extraArmCall = extraArmCall;
            s.testType = testType;
        }));
    }

    /** The stock limits on a {invokes, others} count (mirrors InliningUtilities.shouldBeTrivial). */
    private static boolean underStockLimits(int[] c) {
        if (c[0] == 0) {
            return c[1] <= SubstrateOptions.MaxNodesInTrivialLeafMethod.getValue(OPTIONS);
        }
        return c[0] <= SubstrateOptions.MaxInvokesInTrivialMethod.getValue(OPTIONS) && c[1] <= SubstrateOptions.MaxNodesInTrivialMethod.getValue(OPTIONS);
    }

    /**
     * The target: the discounted count of the chain graph equals the stock count of its flat twin; and the count
     * helper agrees with the hook's stock loop on both graphs.
     */
    private static void assertParity(Shape s) throws NoSuchMethodException {
        StructuredGraph chain = build(s);
        StructuredGraph twin = build(s.with(x -> x.chain = false));
        NodeBitMap skip = RepDispatchAccounting.dispatchNodesOf(chain);
        Assert.assertNotNull("arm recognised", skip);
        Assert.assertNull("the flat twin has no arm", RepDispatchAccounting.dispatchNodesOf(twin));
        int[] disc = RepDispatchAccounting.count(chain, skip);
        int[] flat = RepDispatchAccounting.count(twin, null);
        Assert.assertArrayEquals("discounted chain count == stock count of the flat twin, got " + java.util.Arrays.toString(disc) + " vs " + java.util.Arrays.toString(flat), flat, disc);
        Assert.assertEquals(underStockLimits(disc), InliningUtilities.isTrivialMethod(chain, skip));
        Assert.assertEquals(underStockLimits(flat), InliningUtilities.isTrivialMethod(twin, null));
        Assert.assertEquals(underStockLimits(RepDispatchAccounting.count(chain, null)), InliningUtilities.isTrivialMethod(chain, null));
    }

    @Test
    public void armNodesDoNotCountTheRestDoes() throws NoSuchMethodException {
        StructuredGraph g = wrapper(false, StringView.class);
        Assert.assertFalse("stock count: 2 invokes, not trivial", InliningUtilities.isTrivialMethod(g, null));
        NodeBitMap skip = RepDispatchAccounting.dispatchNodesOf(g);
        Assert.assertNotNull(skip);
        Assert.assertTrue("with the discount: the flat call alone, trivial", InliningUtilities.isTrivialMethod(g, skip));
        for (InvokeWithExceptionNode inv : g.getNodes().filter(InvokeWithExceptionNode.class)) {
            boolean rep = ((MethodCallTargetNode) inv.callTarget()).targetMethod().getDeclaringClass().toJavaName().endsWith("StringView");
            Assert.assertEquals(inv.toString(), rep, skip.isMarked(inv));
            Assert.assertEquals(rep, skip.isMarked(inv.callTarget()));
            Assert.assertEquals(rep, skip.isMarked(inv.exceptionEdge()));
        }
        for (var n : g.getNodes()) {
            /* the chain merge has one non-dispatch end: merge, phi and both ends are arm artefacts */
            if (n instanceof IfNode || n instanceof PiNode || n instanceof InstanceOfNode || n instanceof MergeNode || n instanceof ValuePhiNode || n instanceof EndNode ||
                            n instanceof ValueAnchorNode) {
                Assert.assertTrue("dispatch: " + n, skip.isMarked(n));
            }
            if (n instanceof ReturnNode || n instanceof ParameterNode) {
                Assert.assertFalse("not dispatch: " + n, skip.isMarked(n));
            }
        }
    }

    @Test
    public void discountedCountEqualsTheFlatTwin() throws NoSuchMethodException {
        assertParity(new Shape());
    }

    /** Exact-first: the leading exact-String If, its two lines and the merge before the flat call are dispatch. */
    @Test
    public void exactFirstIfIsDispatch() throws NoSuchMethodException {
        StructuredGraph g = build(new Shape().with(s -> s.exactFirst = true));
        NodeBitMap skip = RepDispatchAccounting.dispatchNodesOf(g);
        Assert.assertNotNull(skip);
        int stringTests = 0;
        for (IfNode ifNode : g.getNodes(IfNode.TYPE)) {
            Assert.assertTrue("dispatch: " + ifNode, skip.isMarked(ifNode));
            if (ifNode.condition() instanceof InstanceOfNode io && io.type().getType().toJavaName().equals("java.lang.String")) {
                stringTests++;
                Assert.assertTrue("its condition: " + io, skip.isMarked(io));
            }
        }
        Assert.assertEquals(1, stringTests);
        for (InvokeWithExceptionNode inv : g.getNodes().filter(InvokeWithExceptionNode.class)) {
            boolean rep = ((MethodCallTargetNode) inv.callTarget()).targetMethod().getDeclaringClass().toJavaName().endsWith("StringView");
            Assert.assertEquals("only the rep call is dispatch: " + inv, rep, skip.isMarked(inv));
        }
        assertParity(new Shape().with(s -> s.exactFirst = true));
        assertParity(new Shape().with(s -> {
            s.exactFirst = true;
            s.mergedExceptions = true;
        }));
        Assert.assertNull("an exact-String If alone (no rep arm) is no dispatch", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> {
            s.exactFirst = true;
            s.extraArmCall = true;
        }))));
    }

    /** The else value is a floating node feeding the chain phi; it survives in the flat twin. */
    @Test
    public void floatingElseValueStaysCounted() throws NoSuchMethodException {
        StructuredGraph g = build(new Shape().with(s -> s.floatingElse = true));
        NodeBitMap skip = RepDispatchAccounting.dispatchNodesOf(g);
        for (AddNode add : g.getNodes().filter(AddNode.class)) {
            Assert.assertFalse("the flat value is no dispatch node: " + add, skip.isMarked(add));
        }
        assertParity(new Shape().with(s -> s.floatingElse = true));
    }

    /** The hosted toRootLowerCase shape: an exception merge with 2 non-dispatch ends (+ the arm's) stays counted. */
    @Test
    public void mergeWithTwoNonDispatchEndsStays() throws NoSuchMethodException {
        StructuredGraph g = build(new Shape().with(s -> s.mergedExceptions = true));
        NodeBitMap skip = RepDispatchAccounting.dispatchNodesOf(g);
        Assert.assertNotNull(skip);
        int excMerges = 0;
        for (MergeNode m : g.getNodes().filter(MergeNode.class)) {
            if (m.next() instanceof UnwindNode) {
                excMerges++;
                Assert.assertEquals(3, m.forwardEndCount());
                Assert.assertFalse("the exception merge stays", skip.isMarked(m));
                int markedEnds = 0;
                for (EndNode e : m.forwardEnds()) {
                    markedEnds += skip.isMarked(e) ? 1 : 0;
                }
                Assert.assertEquals("only the arm's end is dispatch", 1, markedEnds);
                for (var phi : m.phis()) {
                    Assert.assertFalse("its phi stays", skip.isMarked(phi));
                }
            }
        }
        Assert.assertEquals(1, excMerges);
        assertParity(new Shape().with(s -> s.mergedExceptions = true));
        assertParity(new Shape().with(s -> {
            s.mergedExceptions = true;
            s.floatingElse = true;
        }));
    }

    /** The class-compare form of the chain test: rep constant + the arm's rep Pi of the tested value. */
    @Test
    public void classCompareForm() throws NoSuchMethodException {
        ConstantReflectionProvider saved = RepDispatchAccounting.constantReflection;
        try {
            RepDispatchAccounting.constantReflection = CR;
            assertParity(new Shape().with(s -> s.test = Form.GETCLASS_EQ));
            assertParity(new Shape().with(s -> s.test = Form.LOADHUB_EQ));
            Assert.assertNull("a non-rep constant is no rep test", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> {
                s.test = Form.GETCLASS_EQ;
                s.testType = String.class;
            }))));
            Assert.assertNull("a call not on the arm's rep Pi is no arm", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> {
                s.test = Form.GETCLASS_EQ;
                s.armReceiverIsParameter = true;
            }))));
            RepDispatchAccounting.constantReflection = null;
            Assert.assertNull("without constant reflection the class compare is not recognised", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> s.test = Form.GETCLASS_EQ))));
        } finally {
            RepDispatchAccounting.constantReflection = saved;
        }
    }

    @Test
    public void notAnArmIsCountedAsInStock() throws NoSuchMethodException {
        Assert.assertNull("a second call in the arm: not an arm", RepDispatchAccounting.dispatchNodesOf(wrapper(true, StringView.class)));
        Assert.assertNull("an exact String test is no rep test", RepDispatchAccounting.dispatchNodesOf(wrapper(false, String.class)));
        Assert.assertNull("instanceof form: a call not on the arm's rep Pi is no arm", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> s.armReceiverIsParameter = true))));
        Assert.assertNull("a tested rep that the callee's class does not cover is no arm", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> s.testType = SingleByteString.class))));
        Assert.assertNull("a graph owned by a rep method: no discount", RepDispatchAccounting.dispatchNodesOf(build(new Shape().with(s -> s.repOwner = true))));
    }

    @Test
    public void inactiveIsStockAndTheHookConsultsThePredicate() throws NoSuchMethodException {
        boolean saved = RepDispatchAccounting.active;
        try {
            RepDispatchAccounting.active = false;
            Assert.assertNull(RepDispatchAccounting.dispatchNodes(wrapper(false, StringView.class)));
            Assert.assertFalse("inactive (OFF image): the stock count", InliningUtilities.isTrivialMethod(wrapper(false, StringView.class)));
            RepDispatchAccounting.active = true;
            Assert.assertTrue("active: the hook skips the arm", InliningUtilities.isTrivialMethod(wrapper(false, StringView.class)));
            Assert.assertTrue(RepDispatchAccounting.censusLine(), RepDispatchAccounting.censusLine().contains("made trivial by the discount="));
        } finally {
            RepDispatchAccounting.active = saved;
        }
    }
}
