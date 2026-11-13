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
import java.util.Arrays;

import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.AbstractBeginNode;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.IntegerEqualsNode;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.extended.GuardingNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import com.oracle.svm.core.nodes.SubstrateMethodCallTargetNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData;
import jdk.graal.compiler.replacements.InvocationPluginHelper;
import jdk.graal.compiler.replacements.StandardGraphBuilderPlugins;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Common graph code of the five lazy-rep {@code equals} intrinsics.
 *
 * <p><b>Premise of the exact-String fast path:</b> after the "argument is an exact {@code java.lang.String}" test, the
 * intrinsics compare the receiver's computed coder with the argument's ({@code false} on a mismatch) and then read every
 * child's {@code value} array directly. That is exact only when every child is a flat compact String and the argument
 * is compact. Under the nested operand rule a child may be a lazy rep (value null): {@link #emitFallbackIfAnyChildValueNull}
 * routes such a call to the total fallback. The coder-mismatch {@code false} before that routing stays exact with
 * nested children: a lazy rep's coder is the OR of its leaves' coders and every leaf is compact (recursively), so the
 * receiver's coder is the compact coder of its content, like the exact argument's. A StringView leaf, whose coder need
 * not be compact, never becomes a part: {@code runNestedConcatConflictPass} disables an LC site whose direct operand is
 * an admitted SB/SV site, and an LC site an admitted SV operand reaches through any flow. Non-compact plain children
 * are an open coder case (the JDK's own {@code equals} shares it). The other paths need no premise: a same-class
 * argument goes to {@code equalsSameType}, whose {@code childEquals} is total, and every other argument to the total
 * {@code equalsFallback}.
 */
abstract class LazyRepEqualsGraphBuilderBase {

    static final byte LATIN1_CODER = 0;

    static final Method STRING_LATIN1_EQUALS;
    static final Method STRING_UTF16_EQUALS;
    static final Method ARRAYS_EQUALS_OBJECT_ARRAY;

    static {
        try {
            STRING_LATIN1_EQUALS = String.class.getDeclaredMethod("latin1Equals", byte[].class, int.class, byte[].class, int.class, int.class);
            STRING_UTF16_EQUALS = String.class.getDeclaredMethod("utf16Equals", byte[].class, int.class, byte[].class, int.class, int.class);
            ARRAYS_EQUALS_OBJECT_ARRAY = Arrays.class.getDeclaredMethod("equals", Object[].class, Object[].class);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException("Failed to reflect String/Arrays helpers for lazy rep equals intrinsic", e);
        }
    }

    protected final GraphBuilderContext b;
    protected final Helper helper;
    protected final ValueNode thisRep;
    protected final ValueNode other;
    protected ValueNode otherString;
    protected final ConstantNode trueValue;
    protected final ConstantNode falseValue;
    protected final ResolvedJavaField coderField;
    protected final ResolvedJavaField valueField;

    LazyRepEqualsGraphBuilderBase(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        this.b = b;
        this.helper = new Helper(b, targetMethod);
        this.thisRep = receiver.get(true);
        this.other = other;
        this.trueValue = ConstantNode.forBoolean(true);
        this.falseValue = ConstantNode.forBoolean(false);
        this.coderField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_CODER_FIELD);
        this.valueField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_VALUE_FIELD);
    }

    abstract boolean build();

    protected final ValueNode loadField(ValueNode obj, ResolvedJavaField field) {
        return helper.loadField(obj, field);
    }

    protected final ValueNode loadStringCoder(ValueNode str) {
        return loadField(str, coderField);
    }

    protected final ValueNode loadStringValue(ValueNode str) {
        return b.nullCheckedValue(loadField(str, valueField));
    }

    /**
     * A value-null child (a lazy rep under the nested-operand rule) routes the
     * call to the total {@code fallbackMethod(thisRep, otherString)}. Call before any {@link #loadStringValue} of a child.
     */
    protected final void emitFallbackIfAnyChildValueNull(Method fallbackMethod, ValueNode... children) {
        for (ValueNode child : children) {
            LogicNode valueIsNull = b.add(IsNullNode.create(loadField(child, valueField)));
            emitReturnIfWithInvoke(valueIsNull, fallbackMethod, new ValueNode[]{thisRep, otherString}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);
        }
    }

    protected final ValueNode stringByteLength(ValueNode str) {
        return helper.arraylength(loadStringValue(str));
    }

    protected final AbstractBeginNode emitReturnIf(LogicNode condition, ValueNode returnValue, double prob) {
        return helper.emitReturnIf(condition, returnValue, prob);
    }

    protected final AbstractBeginNode emitReturnIfNot(LogicNode condition, ValueNode returnValue, double prob) {
        return helper.emitReturnIfNot(condition, returnValue, prob);
    }

    protected final void emitFinalReturn(ValueNode returnValue) {
        helper.emitFinalReturn(JavaKind.Boolean, returnValue);
    }

    protected final void emitIdentityReturn(double prob) {
        emitReturnIf(b.add(new ObjectEqualsNode(thisRep, other)), trueValue, prob);
    }

    protected final ValueNode repCoder() {
        return loadStringCoder(thisRep);
    }

    protected final ValueNode otherCoder() {
        return loadStringCoder(other);
    }

    protected final GuardingNode emitStringInstanceGuard() {
        TypeReference stringType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(String.class));
        GuardingNode guard = emitReturnIfNot(InstanceOfNode.create(stringType, other), b.add(ConstantNode.forBoolean(false)),
                        BranchProbabilityNode.SLOW_PATH_PROBABILITY);
        Stamp stamp = StampFactory.objectNonNull(stringType);
        otherString = b.add(new PiNode(other, stamp, guard.asNode()));
        return guard;
    }

    protected final ValueNode piCastOther(GuardingNode guard, Class<?> type) {
        TypeReference tr = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(type));
        Stamp stamp = StampFactory.objectNonNull(tr);
        return b.add(new PiNode(other, stamp, guard.asNode()));
    }

    protected final GuardingNode emitRepInstanceGuard(Class<?> repType) {
        TypeReference tr = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(repType));
        return emitReturnIfNot(InstanceOfNode.create(tr, other), b.add(ConstantNode.forBoolean(false)), BranchProbabilityNode.SLOW_PATH_PROBABILITY);
    }

    protected final LogicNode emitIsExactString(ValueNode obj) {
        ValueNode clazz = b.add(new GetClassNode(
                        StampFactory.objectNonNull(TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(Class.class))), obj));
        TypeReference stringType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(String.class));
        ConstantNode stringClassConstant = ConstantNode.forConstant(b.getConstantReflection().asJavaClass(stringType.getType()), b.getMetaAccess());
        return b.add(new ObjectEqualsNode(clazz, stringClassConstant));
    }

    protected final ValueNode emitStaticBooleanInvoke(Method reflect, ValueNode[] args) {
        ResolvedJavaMethod m = b.getMetaAccess().lookupJavaMethod(reflect);
        InvokeNode invokeNode = new InvokeNode(callTarget(InvokeKind.Static, m, args), b.bci());
        b.append(invokeNode);
        b.push(JavaKind.Boolean, invokeNode);
        b.setStateAfter(invokeNode);
        b.pop(JavaKind.Boolean);
        return invokeNode;
    }

    protected final ValueNode emitLatin1Equals(ValueNode a, ValueNode aOff, ValueNode b2, ValueNode bOff, ValueNode len) {
        return emitStaticBooleanInvoke(STRING_LATIN1_EQUALS, new ValueNode[]{a, aOff, b2, bOff, len});
    }

    protected final ValueNode emitArraysEqualsObjectArray(ValueNode a, ValueNode a2) {
        return emitStaticBooleanInvoke(ARRAYS_EQUALS_OBJECT_ARRAY, new ValueNode[]{a, a2});
    }

    protected final ValueNode emitVirtualBooleanInvoke(Method reflect, InvokeKind kind, ValueNode[] args) {
        ResolvedJavaMethod m = b.getMetaAccess().lookupJavaMethod(reflect);
        InvokeNode invokeNode = new InvokeNode(callTarget(kind, m, args), b.bci());
        b.append(invokeNode);
        JavaKind resultKind = m.getSignature().getReturnKind();
        b.push(resultKind, invokeNode);
        b.setStateAfter(invokeNode);
        b.pop(resultKind);
        return invokeNode;
    }

    protected final AbstractBeginNode emitReturnIfWithInvoke(LogicNode condition, Method reflect, ValueNode[] args, double returnProbability) {
        return emitReturnWithInvoke(condition, false, reflect, args, returnProbability);
    }

    /**
     * Returns the static {@code reflect(args)} result when {@code condition} is false, else falls through (a
     * non-exact-String argument of another class goes to the total {@code equalsFallback}).
     */
    protected final AbstractBeginNode emitReturnIfNotWithInvoke(LogicNode condition, Method reflect, ValueNode[] args, double returnProbability) {
        return emitReturnWithInvoke(condition, true, reflect, args, returnProbability);
    }

    private AbstractBeginNode emitReturnWithInvoke(LogicNode condition, boolean onFalse, Method reflect, ValueNode[] args, double returnProbability) {
        ResolvedJavaMethod m = b.getMetaAccess().lookupJavaMethod(reflect);
        InvokeNode invokeNode = b.getGraph().add(new InvokeNode(callTarget(InvokeKind.Static, m, args), b.bci()));
        b.push(JavaKind.Boolean, invokeNode);
        b.setStateAfter(invokeNode);
        b.pop(JavaKind.Boolean);
        return helper.emitReturnWithInvoke(condition, onFalse, invokeNode, returnProbability);
    }

    /** A call target of {@code m(args)}; an argument not yet in the graph is added first. */
    private MethodCallTargetNode callTarget(InvokeKind kind, ResolvedJavaMethod m, ValueNode[] args) {
        JavaType returnType = m.getSignature().getReturnType(m.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        ValueNode[] addedArgs = new ValueNode[args.length];
        for (int i = 0; i < args.length; i++) {
            ValueNode arg = args[i];
            if (arg.isUnregistered()) {
                arg = b.add(arg);
            }
            addedArgs[i] = arg;
        }
        return b.getGraph().add(new SubstrateMethodCallTargetNode(kind, m, addedArgs, returnStamp));
    }

    protected final void emitCoderBranchAndFinalReturn(Method fallbackMethod, Runnable latin1Path) {
        LogicNode coderIsLatin1 = b.add(new IntegerEqualsNode(repCoder(), constantInt(LATIN1_CODER)));

        ResolvedJavaMethod m = b.getMetaAccess().lookupJavaMethod(fallbackMethod);
        InvokeNode fallbackInvoke = b.getGraph().add(new InvokeNode(callTarget(InvokeKind.Static, m, new ValueNode[]{thisRep, other}), b.bci()));
        b.push(JavaKind.Boolean, fallbackInvoke);
        b.setStateAfter(fallbackInvoke);
        b.pop(JavaKind.Boolean);

        BeginNode fallbackBegin = b.getGraph().add(new BeginNode());
        EndNode fallbackEnd = b.getGraph().add(new EndNode());
        fallbackBegin.setNext(fallbackInvoke);
        fallbackInvoke.setNext(fallbackEnd);
        helper.addReturnValuePublic(fallbackEnd, JavaKind.Boolean, fallbackInvoke);

        BranchProbabilityData probability = BranchProbabilityData.injected(BranchProbabilityNode.FAST_PATH_PROBABILITY, false);
        IfNode coderIf = new IfNode(coderIsLatin1, null, fallbackBegin, probability);
        b.append(coderIf);
        BeginNode latin1Begin = b.append(new BeginNode());
        coderIf.setTrueSuccessor(latin1Begin);

        latin1Path.run();

        helper.emitFinalReturn(JavaKind.Boolean, b.add(ConstantNode.forBoolean(true)));
    }

    protected final ValueNode emitAdd(ValueNode x, ValueNode y) {
        return b.add(new AddNode(x, y));
    }

    protected final LogicNode emitIntegerEquals(ValueNode x, ValueNode y) {
        return b.add(new IntegerEqualsNode(x, y));
    }

    protected final ValueNode constantInt(int v) {
        return ConstantNode.forInt(v);
    }

    protected final ValueNode zeroInt() {
        return ConstantNode.forInt(0);
    }

    protected final LogicNode boolIsTrue(ValueNode boolResult) {
        return IntegerEqualsNode.create(b.getConstantReflection(), b.getMetaAccess(), b.getOptions(), null, boolResult, ConstantNode.forBoolean(true), NodeView.DEFAULT);
    }

    protected final void emitReturnIfFalse(ValueNode boolResult, double prob) {
        emitReturnIfNot(boolIsTrue(boolResult), b.add(ConstantNode.forBoolean(false)), prob);
    }

    /** The invocation-plugin helper of these intrinsics and of the String and StringView {@code equals} intrinsics. */
    protected static final class Helper extends InvocationPluginHelper {
        Helper(GraphBuilderContext b, ResolvedJavaMethod targetMethod) {
            super(b, targetMethod);
        }

        /**
         * Returns the boolean result of {@code invokeNode} (created, not yet placed in the control flow) on the
         * {@code condition}-true branch, or on the false branch if {@code onFalse}; the other branch falls through.
         */
        AbstractBeginNode emitReturnWithInvoke(LogicNode condition, boolean onFalse, InvokeNode invokeNode, double returnProbability) {
            BeginNode returnSuccessor = b.getGraph().add(new BeginNode());
            EndNode end = b.getGraph().add(new EndNode());
            returnSuccessor.setNext(invokeNode);
            invokeNode.setNext(end);
            addReturnValue(end, JavaKind.Boolean, invokeNode);
            BranchProbabilityData probability = BranchProbabilityData.injected(returnProbability, onFalse);
            IfNode ifNode = onFalse ? new IfNode(condition, null, returnSuccessor, probability) : new IfNode(condition, returnSuccessor, null, probability);
            b.append(ifNode);
            BeginNode fallThroughSuccessor = b.append(new BeginNode());
            if (onFalse) {
                ifNode.setTrueSuccessor(fallThroughSuccessor);
            } else {
                ifNode.setFalseSuccessor(fallThroughSuccessor);
            }
            return fallThroughSuccessor;
        }

        void addReturnValuePublic(EndNode end, JavaKind kind, ValueNode returnValue) {
            addReturnValue(end, kind, returnValue);
        }
    }
}