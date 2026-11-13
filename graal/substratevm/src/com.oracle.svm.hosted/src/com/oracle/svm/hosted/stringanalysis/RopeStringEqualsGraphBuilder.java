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

import com.oracle.svm.core.stringrep.RopeString;

import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.IntegerEqualsNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

final class RopeStringEqualsGraphBuilder extends LazyRepEqualsGraphBuilderBase {

    private static final Field LEFT_FIELD;
    private static final Field RIGHT_FIELD;
    private static final Method EQUALS_SAME_TYPE;
    private static final Method EQUALS_FALLBACK;

    static {
        try {
            Field left = RopeString.class.getDeclaredField("left");
            left.setAccessible(true);
            Field right = RopeString.class.getDeclaredField("right");
            right.setAccessible(true);
            LEFT_FIELD = left;
            RIGHT_FIELD = right;
            EQUALS_SAME_TYPE = RopeString.class.getDeclaredMethod("equalsSameType", RopeString.class, RopeString.class);
            EQUALS_FALLBACK = RopeString.class.getDeclaredMethod("equalsFallback", RopeString.class, Object.class);
        } catch (NoSuchFieldException | NoSuchMethodException e) {
            throw new RuntimeException("Failed to reflect RopeString fields/methods for equals intrinsic", e);
        }
    }

    private RopeStringEqualsGraphBuilder(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        super(b, targetMethod, receiver, other);
    }

    static boolean buildRopeStringEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        return new RopeStringEqualsGraphBuilder(b, targetMethod, receiver, other).build();
    }

    @Override
    boolean build() {
        ResolvedJavaField leftField = b.getMetaAccess().lookupJavaField(LEFT_FIELD);
        ResolvedJavaField rightField = b.getMetaAccess().lookupJavaField(RIGHT_FIELD);

        emitIdentityReturn(BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        TypeReference ropeType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(RopeString.class));
        LogicNode isRope = b.add(InstanceOfNode.create(ropeType, other));
        emitReturnIfWithInvoke(isRope, EQUALS_SAME_TYPE, new ValueNode[]{thisRep, other}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        emitStringInstanceGuard();

        // A String argument of another class (a flat rep, a view, another lazy rep) compares
        // by content through the total equalsFallback (charAt/length)
        emitReturnIfNotWithInvoke(emitIsExactString(otherString), EQUALS_FALLBACK, new ValueNode[]{thisRep, otherString}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        // the coder-mismatch false stays exact with nested lazy children: see the premise in
        // LazyRepEqualsGraphBuilderBase (a rep's coder is the OR of its compact leaves; SV leaves are excluded)
        ValueNode thisCoder = repCoder();
        ValueNode thatCoder = loadStringCoder(otherString);
        emitReturnIfNot(b.add(new IntegerEqualsNode(thisCoder, thatCoder)), b.add(ConstantNode.forBoolean(false)),
                        BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        emitCoderBranchAndFinalReturn(EQUALS_FALLBACK, () -> {
            ValueNode thisLeft = loadField(thisRep, leftField);
            ValueNode thisRight = loadField(thisRep, rightField);
            emitFallbackIfAnyChildValueNull(EQUALS_FALLBACK, thisLeft, thisRight);
            ValueNode thatValue = loadStringValue(otherString);

            ValueNode leftLen = stringByteLength(thisLeft);
            ValueNode rightLen = stringByteLength(thisRight);
            ValueNode totalLen = emitAdd(leftLen, rightLen);

            emitReturnIfNot(emitIntegerEquals(totalLen, helper.arraylength(thatValue)), b.add(ConstantNode.forBoolean(false)),
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode leftEqual = emitLatin1Equals(loadStringValue(thisLeft), zeroInt(), thatValue, zeroInt(), leftLen);
            emitReturnIfFalse(leftEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);

            ValueNode rightEqual = emitLatin1Equals(loadStringValue(thisRight), zeroInt(), thatValue, leftLen, rightLen);
            emitReturnIfFalse(rightEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);
        });

        return true;
    }
}