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

import java.lang.constant.ClassDesc;
import java.lang.invoke.CallSite;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.runtime.SwitchBootstraps;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.hotspot.HotSpotObjectConstant;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The {@code SwitchBootstraps.typeSwitch} model and the class-name-only getClass
 * extension. The model's decision is pure ({@code StringAtoms.isTypeSwitchBootstrap},
 * {@code repInvariantClassLabel}, {@code typeSwitchRefusal}): every label kind, the invocation type, the {@code F1} shape. The
 * premises: javac's real typeSwitch sites read through JVMCI as production reads them ({@code typeSwitchLabels}), and the
 * JDK bootstrap's semantics the model relies on (null = -1, first matching label from the restart index, no match =
 * labels.length).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.core.common"})
public class TypeSwitchModelTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());
    private static final List<Class<?>> REPS = StringAtoms.TYPESWITCH_REPS;
    private static final Class<?>[] SEL_OBJECT = {Object.class, int.class};

    /** A rep stand-in that declares an interface of its own (a String does not implement Runnable). */
    static final class ExtraInterfaceRep implements Runnable {
        @Override
        public void run() {
        }
    }

    /** javac fixtures: one typeSwitch indy each. */
    static final class Sites {
        static int classOnly(Object o) {
            return switch (o) {
                case null -> -1;
                case Integer i -> i;
                case String s when s.length() > 3 -> 1;
                case String s -> 2;
                case CharSequence cs -> 3;
                default -> throw new IllegalStateException("unexpected " + o.getClass());
            };
        }

        static int mixedConstant(String s) {
            return switch (s) {
                case "abc" -> 1;
                case String t when t.length() > 3 -> 2;
                case String t -> 3;
            };
        }

        static int integerConstant(Integer x) {
            return switch (x) {
                case 7 -> 1;
                case Integer i when i > 3 -> 2;
                case Integer i -> 3;
            };
        }
    }

    private static String refusal(List<Object> labels) {
        return StringAtoms.typeSwitchRefusal(SEL_OBJECT, int.class, "linkToTargetMethod", 3, true, labels, REPS);
    }

    @Test
    public void exactBootstrapIdentity() throws NoSuchMethodException {
        java.lang.reflect.Method ts = SwitchBootstraps.class.getMethod("typeSwitch", MethodHandles.Lookup.class, String.class, MethodType.class, Object[].class);
        ResolvedJavaMethod m = META.lookupJavaMethod(ts);
        Assert.assertTrue(StringAtoms.isTypeSwitchBootstrap(m.getDeclaringClass().toJavaName(true), m.getName(), m.getSignature().toMethodDescriptor()));
        java.lang.reflect.Method es = SwitchBootstraps.class.getMethod("enumSwitch", MethodHandles.Lookup.class, String.class, MethodType.class, Object[].class);
        ResolvedJavaMethod e = META.lookupJavaMethod(es);
        Assert.assertFalse("enumSwitch", StringAtoms.isTypeSwitchBootstrap(e.getDeclaringClass().toJavaName(true), e.getName(), e.getSignature().toMethodDescriptor()));
        Assert.assertFalse("another owner", StringAtoms.isTypeSwitchBootstrap("my.SwitchBootstraps", "typeSwitch", StringAtoms.TYPESWITCH_DESCRIPTOR));
        Assert.assertFalse("another descriptor", StringAtoms.isTypeSwitchBootstrap(StringAtoms.TYPESWITCH_OWNER, "typeSwitch", "()V"));
    }

    @Test
    public void classLabelsOutsideTheConeAndStringAreRepInvariant() {
        for (Class<?> c : new Class<?>[]{Integer.class, Long.class, Object.class, CharSequence.class, Comparable.class, java.io.Serializable.class, String.class, StringBuilder.class,
                        int[].class, String[].class, Thread.State.class}) {
            Assert.assertTrue(c.getName(), StringAtoms.repInvariantClassLabel(c, REPS));
        }
    }

    @Test
    public void repPrimitiveHiddenAndNonClassLabelsAreNot() {
        Runnable lambda = () -> {
        };
        Assert.assertTrue("fixture precondition: a lambda class is hidden", lambda.getClass().isHidden());
        Object hiddenArray = java.lang.reflect.Array.newInstance(lambda.getClass(), 0);
        for (Object l : new Object[]{StringView.class, SingleByteString.class, int.class, lambda.getClass(), hiddenArray.getClass(), "abc", 1, null}) {
            Assert.assertFalse(String.valueOf(l), StringAtoms.repInvariantClassLabel(l, REPS));
        }
    }

    @Test
    public void aRepWithAnExtraInterfaceRefusesThatLabel() {
        List<Class<?>> reps = new ArrayList<>(REPS);
        reps.add(ExtraInterfaceRep.class);
        Assert.assertTrue(StringAtoms.repInvariantClassLabel(Runnable.class, REPS));
        Assert.assertFalse(StringAtoms.repInvariantClassLabel(Runnable.class, reps));
        Assert.assertTrue("a label no rep answers differently", StringAtoms.repInvariantClassLabel(Integer.class, reps));
    }

    @Test
    public void classOnlySitesAreModelled() {
        Assert.assertNull(refusal(List.of(Integer.class, String.class, String.class, CharSequence.class)));
        Assert.assertNull("no label: null -> -1, else 0", refusal(List.of()));
    }

    @Test
    public void everyValueLabelKindRefuses() {
        Object enumDesc = Enum.EnumDesc.of(ClassDesc.of("java.lang.Thread$State"), "NEW");
        Assert.assertEquals("label-String", refusal(List.of("abc")));
        Assert.assertEquals("label-Integer", refusal(List.of(7)));
        Assert.assertEquals("label-Long", refusal(List.of(7L)));
        Assert.assertEquals("label-Float", refusal(List.of(1f)));
        Assert.assertEquals("label-Double", refusal(List.of(1d)));
        Assert.assertEquals("label-Boolean", refusal(List.of(true)));
        Assert.assertEquals("label-EnumDesc", refusal(List.of(enumDesc)));
        Assert.assertEquals("label-unreadable", refusal(Arrays.asList(Integer.class, null)));
    }

    @Test
    public void mixedConstantAndClassLabelsRefuse() {
        Assert.assertEquals("label-String", refusal(List.of(String.class, "abc", String.class)));
        Assert.assertEquals("label-Integer", refusal(List.of(Integer.class, 7, Integer.class)));
        Assert.assertEquals("label-class-not-rep-invariant", refusal(List.of(Integer.class, StringView.class)));
    }

    @Test
    public void invocationTypeAndShapeRefuse() {
        Assert.assertEquals("labels-unreadable", refusal(null));
        List<Object> ok = List.of(Integer.class);
        Assert.assertEquals("invocation-type", StringAtoms.typeSwitchRefusal(new Class<?>[]{int.class, int.class}, int.class, "linkToTargetMethod", 3, true, ok, REPS));
        Assert.assertEquals("invocation-type", StringAtoms.typeSwitchRefusal(new Class<?>[]{Object.class, long.class}, int.class, "linkToTargetMethod", 3, true, ok, REPS));
        Assert.assertEquals("invocation-type", StringAtoms.typeSwitchRefusal(SEL_OBJECT, Object.class, "linkToTargetMethod", 3, true, ok, REPS));
        Assert.assertEquals("invocation-type", StringAtoms.typeSwitchRefusal(new Class<?>[]{Object.class}, int.class, "linkToTargetMethod", 2, true, ok, REPS));
        Assert.assertEquals("invocation-type", StringAtoms.typeSwitchRefusal(null, int.class, "linkToTargetMethod", 3, true, ok, REPS));
        Assert.assertEquals("not-f1", StringAtoms.typeSwitchRefusal(SEL_OBJECT, int.class, "invokeBasic", 3, true, ok, REPS));
        Assert.assertEquals("not-f1", StringAtoms.typeSwitchRefusal(SEL_OBJECT, int.class, "linkToTargetMethod", 2, true, ok, REPS));
        Assert.assertEquals("not-f1", StringAtoms.typeSwitchRefusal(SEL_OBJECT, int.class, "linkToTargetMethod", 3, false, ok, REPS));
        Assert.assertNull(StringAtoms.typeSwitchRefusal(new Class<?>[]{CharSequence.class, int.class}, int.class, "linkToTargetMethod", 3, true, ok, REPS));
    }

    /** The one typeSwitch indy of {@code m}, read as production reads it: the bootstrap and its labels. */
    private static ConstantPool.BootstrapMethodInvocation indy(ResolvedJavaMethod m) {
        BytecodeStream s = new BytecodeStream(m.getCode());
        while (s.currentBC() != Bytecodes.END) {
            if (s.currentBC() == Bytecodes.INVOKEDYNAMIC) {
                ConstantPool.BootstrapMethodInvocation bmi = m.getConstantPool().lookupBootstrapMethodInvocation(s.readCPI4(), Bytecodes.INVOKEDYNAMIC);
                if (bmi != null && bmi.getMethod().getName().equals("typeSwitch")) {
                    return bmi;
                }
            }
            s.next();
        }
        throw new AssertionError("no typeSwitch indy in " + m.format("%H.%n"));
    }

    private static String javacSite(String name, Class<?> param) throws NoSuchMethodException {
        ConstantPool.BootstrapMethodInvocation bmi = indy(META.lookupJavaMethod(Sites.class.getDeclaredMethod(name, param)));
        ResolvedJavaMethod boot = bmi.getMethod();
        Assert.assertTrue(name, StringAtoms.isTypeSwitchBootstrap(boot.getDeclaringClass().toJavaName(true), boot.getName(), boot.getSignature().toMethodDescriptor()));
        MethodType mt = ((HotSpotObjectConstant) bmi.getType()).asObject(MethodType.class);
        List<Object> labels = StringAtoms.typeSwitchLabels(bmi.getStaticArguments(), c -> c instanceof HotSpotObjectConstant hs ? hs.asObject(Object.class) : null);
        return StringAtoms.typeSwitchRefusal(mt.parameterArray(), mt.returnType(), "linkToTargetMethod", 3, true, labels, REPS);
    }

    @Test
    public void javacSitesReadAsProductionReadsThem() throws NoSuchMethodException {
        Assert.assertNull("Class labels only", javacSite("classOnly", Object.class));
        Assert.assertEquals("a String constant mixed with String patterns", "label-String", javacSite("mixedConstant", String.class));
        Assert.assertEquals("an int constant label", "label-Integer", javacSite("integerConstant", Integer.class));
    }

    /** The JDK semantics the model relies on: only the label tests decide the index; null = -1; no match = labels.length. */
    @Test
    public void bootstrapSemanticsPremise() throws Throwable {
        Object[] labels = {Integer.class, String.class, CharSequence.class};
        CallSite cs = SwitchBootstraps.typeSwitch(MethodHandles.lookup(), "typeSwitch", MethodType.methodType(int.class, Object.class, int.class), labels);
        MethodHandle h = cs.dynamicInvoker();
        Assert.assertEquals(-1, (int) h.invokeExact((Object) null, 0));
        Assert.assertEquals(0, (int) h.invokeExact((Object) Integer.valueOf(3), 0));
        Assert.assertEquals(1, (int) h.invokeExact((Object) "abc", 0));
        Assert.assertEquals("the restart index skips earlier labels", 2, (int) h.invokeExact((Object) "abc", 2));
        Assert.assertEquals(2, (int) h.invokeExact((Object) new StringBuilder("x"), 0));
        Assert.assertEquals("no match", 3, (int) h.invokeExact(new Object(), 0));
        Assert.assertEquals("restart past every label", 3, (int) h.invokeExact((Object) "abc", 3));
    }

    // ------------------------------------------------------------------ the class-name-only getClass extension

    private static StructuredGraph newGraph() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        return new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(TypeSwitchModelTest.class.getDeclaredMethod("holder", Object.class))).build();
    }

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    private static ResolvedJavaMethod method(Class<?> c, String name, Class<?>... params) throws NoSuchMethodException {
        return META.lookupJavaMethod(c.getDeclaredMethod(name, params));
    }

    private static GetClassNode getClassOf(StructuredGraph g) {
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull())));
        return g.addWithoutUnique(new GetClassNode(StampFactory.objectNonNull(), p));
    }

    private static void call(StructuredGraph g, InvokeKind kind, ResolvedJavaMethod target, ValueNode... args) {
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(kind, target, args, StampPair.createSingle(StampFactory.object()), null));
        InvokeNode inv = g.add(new InvokeNode(ct, 0));
        g.start().setNext(inv);
    }

    @Test
    public void classToStringAndValueOfAreNameObservations() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        call(g, InvokeKind.Virtual, method(Class.class, "toString"), gc);
        Assert.assertTrue("Class.toString()", StringAtoms.isClassNameOnlyGetClass(gc));
        g = newGraph();
        gc = getClassOf(g);
        call(g, InvokeKind.Static, method(String.class, "valueOf", Object.class), gc);
        Assert.assertTrue("String.valueOf(Class)", StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void otherRenderingsStayUsages() throws NoSuchMethodException {
        StructuredGraph g = newGraph();
        GetClassNode gc = getClassOf(g);
        call(g, InvokeKind.Virtual, method(Class.class, "toGenericString"), gc);
        Assert.assertFalse("Class.toGenericString()", StringAtoms.isClassNameOnlyGetClass(gc));
        g = newGraph();
        gc = getClassOf(g);
        call(g, InvokeKind.Static, method(java.util.Objects.class, "toString", Object.class), gc);
        Assert.assertFalse("Objects.toString(Class)", StringAtoms.isClassNameOnlyGetClass(gc));
        g = newGraph();
        gc = getClassOf(g);
        call(g, InvokeKind.Static, method(String.class, "valueOf", char[].class), gc);
        Assert.assertFalse("String.valueOf(char[])", StringAtoms.isClassNameOnlyGetClass(gc));
    }

    @Test
    public void classToStringPureTable() {
        Assert.assertTrue(StringAtoms.isClassToStringMethod(false, "java.lang.Class", "toString", "()Ljava/lang/String;"));
        Assert.assertTrue(StringAtoms.isClassToStringMethod(false, "com.oracle.svm.core.hub.DynamicHub", "toString", "()Ljava/lang/String;"));
        Assert.assertTrue(StringAtoms.isClassToStringMethod(true, "java.lang.String", "valueOf", "(Ljava/lang/Object;)Ljava/lang/String;"));
        Assert.assertFalse("Object.toString (not provably the Class's)", StringAtoms.isClassToStringMethod(false, "java.lang.Object", "toString", "()Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassToStringMethod(false, "java.lang.String", "valueOf", "(Ljava/lang/Object;)Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassToStringMethod(true, "java.lang.String", "valueOf", "(C)Ljava/lang/String;"));
        Assert.assertFalse(StringAtoms.isClassToStringMethod(true, "java.lang.Class", "toString", "()Ljava/lang/String;"));
    }
}
