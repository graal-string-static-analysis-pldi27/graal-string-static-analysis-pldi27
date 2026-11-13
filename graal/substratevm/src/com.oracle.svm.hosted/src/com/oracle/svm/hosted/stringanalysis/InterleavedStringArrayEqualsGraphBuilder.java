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

import com.oracle.svm.core.stringrep.InterleavedStringArray;

import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.IntegerEqualsNode;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.vm.ci.meta.ResolvedJavaMethod;

final class InterleavedStringArrayEqualsGraphBuilder extends LazyRepEqualsGraphBuilderBase {

    private static final Method EQUALS_SAME_TYPE;
    private static final Method EQUALS_FALLBACK;

    static {
        try {
            EQUALS_SAME_TYPE = InterleavedStringArray.class.getDeclaredMethod("equalsSameType", InterleavedStringArray.class, InterleavedStringArray.class);
            EQUALS_FALLBACK = InterleavedStringArray.class.getDeclaredMethod("equalsFallback", InterleavedStringArray.class, Object.class);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException("Failed to reflect InterleavedStringArray methods for equals intrinsic", e);
        }
    }

    private InterleavedStringArrayEqualsGraphBuilder(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        super(b, targetMethod, receiver, other);
    }

    static boolean buildInterleavedStringArrayEqualsGraph(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
        if (!b.canMergeIntrinsicReturns()) {
            return false;
        }
        return new InterleavedStringArrayEqualsGraphBuilder(b, targetMethod, receiver, other).build();
    }

    @Override
    boolean build() {
        emitIdentityReturn(BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        TypeReference repType = TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(InterleavedStringArray.class));
        LogicNode isRep = b.add(InstanceOfNode.create(repType, other));
        emitReturnIfWithInvoke(isRep, EQUALS_SAME_TYPE, new ValueNode[]{thisRep, other}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        emitStringInstanceGuard();

        // A String argument of another class (a flat rep, a view, another lazy rep) compares by content through the
        // total equalsFallback (charAt/length); answering false there would be wrong for equal content
        emitReturnIfNotWithInvoke(emitIsExactString(otherString), EQUALS_FALLBACK, new ValueNode[]{thisRep, otherString}, BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        ValueNode thisCoder = repCoder();
        ValueNode thatCoder = loadStringCoder(otherString);
        emitReturnIfNot(b.add(new IntegerEqualsNode(thisCoder, thatCoder)), b.add(ConstantNode.forBoolean(false)),
                        BranchProbabilityNode.SLOW_PATH_PROBABILITY);

        ValueNode fallbackResult = emitStaticBooleanInvoke(EQUALS_FALLBACK, new ValueNode[]{thisRep, other});
        emitFinalReturn(fallbackResult);

        return true;
    }
}