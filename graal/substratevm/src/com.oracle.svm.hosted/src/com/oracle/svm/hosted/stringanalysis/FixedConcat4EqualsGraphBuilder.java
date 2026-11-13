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

import com.oracle.svm.core.stringrep.FixedConcat4;

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

final class FixedConcat4EqualsGraphBuilder extends LazyRepEqualsGraphBuilderBase {

    private static final Field A_FIELD;
    private static final Field B_FIELD;
    private static final Field C_FIELD;
    private static final Field D_FIELD;
    private static final Method EQUALS_SAME_TYPE;
    private static final Method EQUALS_FALLBACK;

    static {
        try {
            Field a = FixedConcat4.class.getDeclaredField("a");
            a.setAccessible(true);
            Field bb = FixedConcat4.class.getDeclaredField("b");
            bb.setAccessible(true);
            Field c = FixedConcat4.class.getDeclaredField("c");
            c.setAccessible(true);
            Field d = FixedConcat4.class.getDeclaredField("d");
            d.setAccessible(true);
            A_FIELD = a;
            B_FIELD = bb;
            C_FIELD = c;
            D_FIELD = d;
            EQUALS_SAME_TYPE = FixedConcat4.class.getDeclaredMethod("equalsSameType", FixedConcat4.class, FixedConcat4.class);
            EQUALS_FALLBACK = FixedConcat4.class.getDeclaredMethod("equalsFallback", FixedConcat4.class, Object.class);
        } catch (NoSuchFieldException | NoSuchMethodException e) {
            throw new RuntimeException("Failed to reflect FixedConcat4 fields/methods for equals intrinsic", e);
        }
    }

    private FixedConcat4EqualsGraphBuilder(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        super(b, targetMethod, receiver, other);
    }

    static boolean buildFixedConcat4EqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        return new FixedConcat4EqualsGraphBuilder(b, targetMethod, receiver, other).build();
    }

    @Override
    boolean build() {
        ResolvedJavaField aField = b.getMetaAccess().lookupJavaField(A_FIELD);
        ResolvedJavaField bField = b.getMetaAccess().lookupJavaField(B_FIELD);
        ResolvedJavaField cField = b.getMetaAccess().lookupJavaField(C_FIELD);
        ResolvedJavaField dField = b.getMetaAccess().lookupJavaField(D_FIELD);

        emitIdentityReturn(BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        TypeReference repType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(FixedConcat4.class));
        LogicNode isRep = b.add(InstanceOfNode.create(repType, other));
        emitReturnIfWithInvoke(isRep, EQUALS_SAME_TYPE, new ValueNode[]{thisRep, other}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

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
            ValueNode thisA = loadField(thisRep, aField);
            ValueNode thisB = loadField(thisRep, bField);
            ValueNode thisC = loadField(thisRep, cField);
            ValueNode thisD = loadField(thisRep, dField);
            emitFallbackIfAnyChildValueNull(EQUALS_FALLBACK, thisA, thisB, thisC, thisD);
            ValueNode thatValue = loadStringValue(otherString);

            ValueNode lenA = stringByteLength(thisA);
            ValueNode lenAB = emitAdd(lenA, stringByteLength(thisB));
            ValueNode lenABC = emitAdd(lenAB, stringByteLength(thisC));
            ValueNode totalLen = emitAdd(lenABC, stringByteLength(thisD));

            emitReturnIfNot(emitIntegerEquals(totalLen, helper.arraylength(thatValue)), b.add(ConstantNode.forBoolean(false)),
                            BranchProbabilityNode.SLOW_PATH_PROBABILITY);

            ValueNode aEqual = emitLatin1Equals(loadStringValue(thisA), zeroInt(), thatValue, zeroInt(), lenA);
            emitReturnIfFalse(aEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);

            ValueNode bEqual = emitLatin1Equals(loadStringValue(thisB), zeroInt(), thatValue, lenA, stringByteLength(thisB));
            emitReturnIfFalse(bEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);

            ValueNode cEqual = emitLatin1Equals(loadStringValue(thisC), zeroInt(), thatValue, lenAB, stringByteLength(thisC));
            emitReturnIfFalse(cEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);

            ValueNode dEqual = emitLatin1Equals(loadStringValue(thisD), zeroInt(), thatValue, lenABC, stringByteLength(thisD));
            emitReturnIfFalse(dEqual, BranchProbabilityNode.FAST_PATH_PROBABILITY);
        });

        return true;
    }
}