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

import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.IntegerEqualsNode;
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
import jdk.graal.compiler.replacements.nodes.ArrayEqualsNode;
import jdk.graal.compiler.replacements.StandardGraphBuilderPlugins;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

final class SafeStringEqualsGraphBuilder {

    static boolean buildSafeEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        ValueNode thisString = receiver.get(true);
        return buildSafeEqualsGraph(b, targetMethod, thisString, other);
    }

    static boolean buildSafeEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, ValueNode receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        ValueNode thisString = b.nullCheckedValue(receiver);
        return buildSafeEqualsGraphImpl(b, targetMethod, thisString, other);
    }

    private static boolean buildSafeEqualsGraphImpl(GraphBuilderContext b, ResolvedJavaMethod targetMethod, ValueNode thisString, ValueNode other) {
        try (LazyRepEqualsGraphBuilderBase.Helper helper = new LazyRepEqualsGraphBuilderBase.Helper(b, targetMethod)) {
            ConstantNode trueValue = ConstantNode.forBoolean(true);
            ConstantNode falseValue = ConstantNode.forBoolean(false);
            ConstantNode arrayBaseOffset = ConstantNode.forLong(b.getMetaAccess().getArrayBaseOffset(JavaKind.Byte), b.getGraph());

            helper.emitReturnIf(b.add(new ObjectEqualsNode(thisString, other)), trueValue, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            TypeReference stringType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(String.class));
            GuardingNode stringArgGuard = helper.emitReturnIfNot(InstanceOfNode.create(stringType, other), b.add(falseValue),
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);
            Stamp stamp = StampFactory.objectNonNull(stringType);
            ValueNode otherString = b.add(new PiNode(other, stamp, stringArgGuard.asNode()));

            ValueNode otherGetClass = b.add(new GetClassNode(
                            StampFactory.objectNonNull(TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(Class.class))), otherString));
            ConstantNode stringClassConstant = ConstantNode.forConstant(b.getConstantReflection().asJavaClass(stringType.getType()), b.getMetaAccess());
            LogicNode isExactString = b.add(new ObjectEqualsNode(otherGetClass, stringClassConstant));

            Method equalsReflect;
            try {
                equalsReflect = Object.class.getDeclaredMethod("equals", Object.class);
            } catch (NoSuchMethodException e) {
                throw new RuntimeException(e);
            }
            ResolvedJavaMethod equalsMethod = b.getMetaAccess().lookupJavaMethod(equalsReflect);
            JavaType returnType = equalsMethod.getSignature().getReturnType(equalsMethod.getDeclaringClass());
            StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
            MethodCallTargetNode callTarget = b.getGraph().add(
                            new SubstrateMethodCallTargetNode(InvokeKind.Virtual, equalsMethod, new ValueNode[]{otherString, thisString}, returnStamp));
            InvokeNode invokeNode = b.getGraph().add(new InvokeNode(callTarget, b.bci()));
            b.push(JavaKind.Boolean, invokeNode);
            b.setStateAfter(invokeNode);
            b.pop(JavaKind.Boolean);

            helper.emitReturnWithInvoke(isExactString, true, invokeNode, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ResolvedJavaField coderField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_CODER_FIELD);
            ValueNode thisCoder = helper.loadField(thisString, coderField);
            ValueNode thatCoder = helper.loadField(otherString, coderField);
            helper.emitReturnIfNot(b.add(new IntegerEqualsNode(thisCoder, thatCoder)), falseValue, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ResolvedJavaField valueField = b.getMetaAccess().lookupJavaField(StandardGraphBuilderPlugins.STRING_VALUE_FIELD);
            ValueNode thisValue = b.nullCheckedValue(helper.loadField(otherString, valueField));
            ValueNode thatValue = b.nullCheckedValue(helper.loadField(thisString, valueField));

            ValueNode thisLength = helper.arraylength(thisValue);
            ValueNode thatLength = helper.arraylength(thatValue);
            helper.emitReturnIfNot(IntegerEqualsNode.create(thisLength, thatLength, NodeView.DEFAULT), falseValue, BranchProbabilityNode.SLOW_PATH_PROBABILITY);
            helper.emitReturnIf(IntegerEqualsNode.create(thisLength, ConstantNode.forInt(0), NodeView.DEFAULT), trueValue,
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);
            helper.emitFinalReturn(JavaKind.Boolean, b.append(new ArrayEqualsNode(thisValue, arrayBaseOffset, thatValue, arrayBaseOffset,
                            thisLength.isConstant() ? thisLength : thatLength, JavaKind.Byte)));
        }
        return true;
    }

    private SafeStringEqualsGraphBuilder() {
    }
}