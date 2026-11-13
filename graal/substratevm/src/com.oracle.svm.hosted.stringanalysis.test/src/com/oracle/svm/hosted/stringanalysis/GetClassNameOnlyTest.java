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

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.InvokeNode;
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
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.code.BytecodeFrame;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The local use check of {@code StringAtoms.isClassNameOnlyGetClass}. A {@code getClass()} of a
 * walked value is not a usage only when its {@code Class} result is used, in the same graph, only as the receiver of
 * {@code Class.getName/getSimpleName/getTypeName()} (through Pi nodes; frame states ignored). Every other use is an
 * escape that keeps the class-check usage: a store, an argument, a reflective call, a compare, a return, an exact
 * instanceof, a non-name {@code Class} call. Hand-built graphs, both getClass shapes (the intrinsified
 * {@code GetClassNode} and the unintrinsified {@code Object.getClass()} invoke).
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
public class GetClassNameOnlyTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    static Class<?> sink;

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    @SuppressWarnings("unused")
    static String describe(Class<?> c) {
        return "";
    }

    private static StructuredGraph newGraph() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        return new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(GetClassNameOnlyTest.class.getDeclaredMethod("holder", Object.class))).build();
    }

    private static ResolvedJavaMethod method(Class<?> c, String name, Class<?>... params) throws NoSuchMethodException {
        return META.lookupJavaMethod(c.getDeclaredMethod(name, params));
    }

    /** A call {@code target(args)} appended to the graph's control flow; returns its invoke. */
    private static InvokeNode call(StructuredGraph g, InvokeKind kind, ResolvedJavaMethod target, ValueNode... args) {
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(kind, target, args, StampPair.createSingle(StampFactory.object()), null));
        InvokeNode inv = g.add(new InvokeNode(ct, 0));
        g.start().setNext(inv);
        return inv;
    }

    private static GetClassNode getClassOf(StructuredGraph g) {
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        return g.addWithoutUnique(new GetClassNode(StampFactory.objectNonNull(), p));
    }

    private static void classCall(StructuredGraph g, ValueNode cls, String name) throws NoSuchMethodException {
        call(g, InvokeKind.Virtual, method(Class.class, name), cls);
    }

    @Test
    public void eachNameMethodIsAllowed() throws NoSuchMethodException {
        for (String name : new String[]{"getName", "getSimpleName", "getTypeName"}) {
            StructuredGraph g = newGraph();
            GetClassNode gc = getClassOf(g);
            classCall(g, gc, name);
            Assert.assertTrue(name, StringAtoms.isClassNameOnlyGetClass(gc));
        }
    }

    @Test
    public void allThreeAndAPiAreAllowed() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        classCall(g, gc, "getName");
        PiNode pi = g.addWithoutUnique(new PiNode(gc, StampFactory.objectNonNull()));
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(InvokeKind.Virtual, method(Class.class, "getSimpleName"), new ValueNode[]{pi},
                        StampPair.createSingle(StampFactory.object()), null));
        g.add(new InvokeNode(ct, 1));
        Assert.assertTrue(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void noUseIsNotNameOnly() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        Assert.assertFalse("a getClass with no name use stays a usage", StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void invokeFormIsAllowed() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
        InvokeNode getClass = call(g, InvokeKind.Virtual, method(Object.class, "getClass"), p);
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(InvokeKind.Virtual, method(Class.class, "getTypeName"), new ValueNode[]{getClass},
                        StampPair.createSingle(StampFactory.object()), null));
        InvokeNode name = g.add(new InvokeNode(ct, 1));
        getClass.setNext(name);
        Assert.assertTrue(StringAtoms.isClassNameOnlyGetClass(getClass));
        Assert.assertFalse("the name call itself is no getClass", StringAtoms.isClassNameOnlyGetClass(name));
    }

    @Test
    public void storedClassEscapes() throws NoSuchMethodException, NoSuchFieldException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        classCall(g, gc, "getName");
        g.add(new StoreFieldNode(null, META.lookupJavaField(GetClassNameOnlyTest.class.getDeclaredField("sink")), gc));
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void passedClassEscapes() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        call(g, InvokeKind.Static, method(GetClassNameOnlyTest.class, "describe", Class.class), gc);
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void reflectionEscapes() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        ValueNode fieldName = ConstantNode.forConstant(HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection().forString("value"), META, g);
        call(g, InvokeKind.Virtual, method(Class.class, "getDeclaredField", String.class), gc, fieldName);
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void otherClassCallEscapes() throws NoSuchMethodException {
        // Class.toString() is a name observation (TypeSwitchModelTest)
        for (String name : new String[]{"getSuperclass", "getCanonicalName", "getPackageName"}) {
            StructuredGraph g = newGraph();
            GetClassNode gc = getClassOf(g);
            classCall(g, gc, name);
            Assert.assertFalse(name, StringAtoms.isClassNameOnlyGetClass(gc));
        }
    }

    @Test
    public void compareEscapes() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        classCall(g, gc, "getName");
        ValueNode stringClass = ConstantNode.forConstant(HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection().asJavaClass(META.lookupJavaType(String.class)), META, g);
        g.addWithoutUnique(new ObjectEqualsNode(gc, stringClass));
        Assert.assertFalse("== String.class is not a name use", StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void returnedClassEscapes() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        g.start().setNext(g.add(new ReturnNode(gc)));
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void classAsNameArgumentEscapes() throws NoSuchMethodException {
        // the Class in an argument slot of a name-shaped call is not the receiver role (String.valueOf(Class) is
        // a name observation; Objects.toString(Class) stays an escape)
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        call(g, InvokeKind.Static, method(java.util.Objects.class, "toString", Object.class), gc);
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void otherAnchorsAreNotGetClass() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
        jdk.graal.compiler.nodes.LogicNode ion = g.addOrUniqueWithInputs(InstanceOfNode.create(jdk.graal.compiler.core.common.type.TypeReference.createExactTrusted(META.lookupJavaType(String.class)),
                        p));
        Assert.assertFalse("an exact instanceof stays a class check", StringAtoms.isClassNameOnlyGetClass(ion));
        InvokeNode len = call(g, InvokeKind.Virtual, method(String.class, "length"), p);
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(len));
    }

    @Test
    public void nameMethodTable() {
        Assert.assertTrue(StringAtoms.isClassNameMethod("java.lang.Class", "getName", "()Ljava/lang/String;"));
        Assert.assertTrue(StringAtoms.isClassNameMethod("com.oracle.svm.core.hub.DynamicHub", "getSimpleName", "()Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassNameMethod("java.lang.Object", "getName", "()Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassNameMethod("java.lang.Class", "getName", "(I)Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassNameMethod("java.lang.Class", "getCanonicalName", "()Ljava/lang/String;"));
    }

    // the phi, proxy, frame-state-only and interface-declared getTypeName cases (all not name-only)

    @Test
    public void phiMergeEscapes() throws NoSuchMethodException {
        // the Class merged with another Class: the name call's receiver is the phi, not the getClass result
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        ValueNode stringClass = ConstantNode.forConstant(HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection().asJavaClass(META.lookupJavaType(String.class)), META, g);
        MergeNode merge = g.add(new MergeNode());
        ValuePhiNode phi = g.addWithoutUnique(new ValuePhiNode(StampFactory.objectNonNull(), merge, gc, stringClass));
        classCall(g, phi, "getName");
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void proxyEscapes() throws NoSuchMethodException {
        // a loop-exit ValueProxyNode is not followed (only Pi nodes are)
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        LoopBeginNode loop = g.add(new LoopBeginNode());
        LoopExitNode exit = g.add(new LoopExitNode(loop));
        ValueProxyNode proxy = g.addWithoutUnique(new ValueProxyNode(gc, exit));
        classCall(g, proxy, "getName");
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void frameStateOnlyIsNotNameOnly() throws NoSuchMethodException {
        // a frame-state use alone is ignored, and at least one name use is required
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        g.add(new FrameState(BytecodeFrame.AFTER_BCI, gc));
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
        classCall(g, gc, "getSimpleName");
        Assert.assertTrue("frame state + a name use", StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void interfaceTypeGetTypeNameEscapes() throws NoSuchMethodException {
        // java.lang.reflect.Type.getTypeName (declared on the interface) is not a Class name method
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        call(g, InvokeKind.Interface, method(java.lang.reflect.Type.class, "getTypeName"), gc);
        Assert.assertFalse(StringAtoms.isClassNameOnlyGetClass(gc));
        Assert.assertFalse(StringAtoms.isClassNameMethod("java.lang.reflect.Type", "getTypeName", "()Ljava/lang/String;"));
    }
}
