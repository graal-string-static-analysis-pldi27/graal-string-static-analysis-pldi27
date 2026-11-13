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

import java.lang.reflect.Field;
import java.lang.reflect.Method;

import com.oracle.svm.core.stringrep.StringView;

import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.IntegerEqualsNode;
import jdk.graal.compiler.nodes.calc.LeftShiftNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.calc.RightShiftNode;
import jdk.graal.compiler.nodes.calc.SignExtendNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.extended.GuardingNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import com.oracle.svm.core.nodes.SubstrateMethodCallTargetNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.replacements.StandardGraphBuilderPlugins;
import jdk.graal.compiler.replacements.nodes.ArrayEqualsNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

final class StringViewEqualsGraphBuilder {

    private static final Field STRING_VIEW_BACKING_FIELD;
    private static final Field STRING_VIEW_OFFSET_FIELD;
    private static final Field STRING_VIEW_LENGTH_FIELD;

    private static final Method SV_EQUALS_STRING_VIEW;
    private static final Method SV_EQUALS_FALLBACK;

    static {
        try {
            SV_EQUALS_STRING_VIEW = StringView.class.getDeclaredMethod("equalsStringView", StringView.class, StringView.class);
            SV_EQUALS_FALLBACK = StringView.class.getDeclaredMethod("equalsFallback", StringView.class, String.class);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException("Failed to reflect StringView methods for equals intrinsic", e);
        }
    }

    static {
        try {
            Field backing = StringView.class.getDeclaredField("backing");
            backing.setAccessible(true);
            Field offset = StringView.class.getDeclaredField("offset");
            offset.setAccessible(true);
            Field length = StringView.class.getDeclaredField("length");
            length.setAccessible(true);
            STRING_VIEW_BACKING_FIELD = backing;
            STRING_VIEW_OFFSET_FIELD = offset;
            STRING_VIEW_LENGTH_FIELD = length;
        } catch (NoSuchFieldException e) {
            throw new RuntimeException("Failed to reflect StringView fields for equals intrinsic", e);
        }
    }

    static boolean buildStringViewEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        ValueNode thisView = receiver.get(true);
        return buildStringViewEqualsGraph(b, targetMethod, thisView, other);
    }

    static boolean buildStringViewEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, ValueNode receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        ValueNode thisView = b.nullCheckedValue(receiver);
        return buildStringViewEqualsGraphImpl(b, targetMethod, thisView, other);
    }

    private static boolean buildStringViewEqualsGraphImpl(GraphBuilderContext b, ResolvedJavaMethod targetMethod, ValueNode thisView, ValueNode other) {
        try (LazyRepEqualsGraphBuilderBase.Helper helper = new LazyRepEqualsGraphBuilderBase.Helper(b, targetMethod)) {
            ConstantNode trueValue = ConstantNode.forBoolean(true);
            ConstantNode falseValue = ConstantNode.forBoolean(false);
            ConstantNode arrayBaseOffset = ConstantNode.forLong(b.getMetaAccess().getArrayBaseOffset(JavaKind.Byte), b.getGraph());

            helper.emitReturnIf(b.add(new ObjectEqualsNode(thisView, other)), trueValue, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            TypeReference stringType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(String.class));
            GuardingNode stringArgGuard = helper.emitReturnIfNot(InstanceOfNode.create(stringType, other), b.add(falseValue),
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);
            Stamp stamp = StampFactory.objectNonNull(stringType);
            ValueNode otherString = b.add(new PiNode(other, stamp, stringArgGuard.asNode()));

            ResolvedJavaField lengthField = b.getMetaAccess().lookupJavaField(STRING_VIEW_LENGTH_FIELD);
            ResolvedJavaField coderField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_CODER_FIELD);
            ResolvedJavaField valueField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_VALUE_FIELD);
            ResolvedJavaField backingField = b.getMetaAccess().lookupJavaField(STRING_VIEW_BACKING_FIELD);
            ResolvedJavaField offsetField = b.getMetaAccess().lookupJavaField(STRING_VIEW_OFFSET_FIELD);

            // The view-argument branch comes first (equalsStringView handles a coder mismatch itself: a view
            // keeps its parent's coder, so two views of equal content may differ in coder)
            TypeReference stringViewTypeRef = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(StringView.class));
            LogicNode isStringViewArg = b.add(InstanceOfNode.create(stringViewTypeRef, otherString));
            helper.emitReturnWithInvoke(isStringViewArg, false, staticBooleanInvoke(b, SV_EQUALS_STRING_VIEW, thisView, otherString), BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode otherGetClass = b.add(new GetClassNode(
                            StampFactory.objectNonNull(TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(Class.class))), otherString));
            ConstantNode stringClassConstant = ConstantNode.forConstant(b.getConstantReflection().asJavaClass(stringType.getType()), b.getMetaAccess());
            LogicNode isExactString = b.add(new ObjectEqualsNode(otherGetClass, stringClassConstant));

            // Any other rep (a flat SingleByteString/TrivialString, a value-null lazy rep) compares by content through
            // the total StringView.equalsFallback; answering false there would be wrong for equal content
            helper.emitReturnWithInvoke(isExactString, true, staticBooleanInvoke(b, SV_EQUALS_FALLBACK, thisView, otherString), BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode thisLengthChars = helper.loadField(thisView, lengthField);
            ValueNode thisCoder = helper.loadField(thisView, coderField);
            ValueNode thatCoder = helper.loadField(otherString, coderField);

            // A coder mismatch with a plain String is not "unequal" for a UTF-16 view of a Latin-1-only range
            helper.emitReturnWithInvoke(b.add(new IntegerEqualsNode(thisCoder, thatCoder)), true, staticBooleanInvoke(b, SV_EQUALS_FALLBACK, thisView, otherString),
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode thatValue = b.nullCheckedValue(helper.loadField(otherString, valueField));
            ValueNode thatValueLenBytes = helper.arraylength(thatValue);
            ValueNode thatLengthChars = b.add(new RightShiftNode(thatValueLenBytes, thisCoder));
            helper.emitReturnIfNot(IntegerEqualsNode.create(thisLengthChars, thatLengthChars, NodeView.DEFAULT), falseValue, BranchProbabilityNode.SLOW_PATH_PROBABILITY);
            helper.emitReturnIf(IntegerEqualsNode.create(thisLengthChars, ConstantNode.forInt(0), NodeView.DEFAULT), trueValue,
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode thisBacking = b.nullCheckedValue(helper.loadField(thisView, backingField));
            ValueNode thisOffsetChars = helper.loadField(thisView, offsetField);

            ValueNode thisOffsetBytes = b.add(new LeftShiftNode(thisOffsetChars, thisCoder));
            ValueNode thisOffsetBytesWord = b.add(SignExtendNode.create(thisOffsetBytes, helper.getWordKind().getBitCount(), NodeView.DEFAULT));
            ValueNode thisBackingOffset = b.add(new AddNode(arrayBaseOffset, thisOffsetBytesWord));

            ValueNode thisByteLen = b.add(new LeftShiftNode(thisLengthChars, thisCoder));

            helper.emitFinalReturn(JavaKind.Boolean, b.append(new ArrayEqualsNode(thisBacking, thisBackingOffset, thatValue, arrayBaseOffset,
                            thisByteLen, JavaKind.Byte)));
        }
        return true;
    }

    /** A static boolean invoke of {@code reflect(a, b)} at the current bci, not yet placed in the control flow. */
    private static InvokeNode staticBooleanInvoke(GraphBuilderContext b, Method reflect, ValueNode a, ValueNode o) {
        ResolvedJavaMethod m = b.getMetaAccess().lookupJavaMethod(reflect);
        JavaType returnType = m.getSignature().getReturnType(m.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        MethodCallTargetNode callTarget = b.getGraph().add(new SubstrateMethodCallTargetNode(InvokeKind.Static, m, new ValueNode[]{a, o}, returnStamp));
        InvokeNode invokeNode = b.getGraph().add(new InvokeNode(callTarget, b.bci()));
        b.push(JavaKind.Boolean, invokeNode);
        b.setStateAfter(invokeNode);
        b.pop(JavaKind.Boolean);
        return invokeNode;
    }

    private StringViewEqualsGraphBuilder() {
    }
}
