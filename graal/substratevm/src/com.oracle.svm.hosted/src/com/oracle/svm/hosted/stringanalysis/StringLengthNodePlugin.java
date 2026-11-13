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
import java.util.ArrayList;
import java.util.List;

import com.oracle.svm.core.nodes.SubstrateMethodCallTargetNode;
import com.oracle.svm.core.stringrep.StringView;

import jdk.graal.compiler.core.common.type.ObjectStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.AbstractMergeNode;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.calc.RightShiftNode;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.ArrayLengthNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The length intrinsic plugin ({@code StringLengthPluginRegistration}): folds {@code String.length()} to
 * {@code value.length >> coder} when the receiver's stamp is exact {@code String}, else (in the rep-admitting modes)
 * emits the guarded {@code instanceof} dispatch with per-rep length-field branches and a virtual fallback (rep-safe:
 * the fallback dispatches to the rep's own override).
 * <p>
 * Under the always-virt rule ({@code StringAnalysisPolicy.alwaysVirtJdkTrivialApplies}) this plugin makes no claim at a
 * site whose enclosing method is a terminal body, although its forms are guarded: that population (e.g. the length
 * sites of {@code StringConcatHelper.stringSize}) goes back to the stock pipeline.
 */
public final class StringLengthNodePlugin implements NodePlugin {

    private final boolean handleStringView;
    private final boolean handleLazyReps;
    private final Field stringValueField;
    private final Field stringCoderField;
    private final Field stringViewLengthField;

    StringLengthNodePlugin(boolean handleStringView, boolean handleLazyReps) {
        this.handleStringView = handleStringView;
        this.handleLazyReps = handleLazyReps;
        try {
            Field valueReflect = String.class.getDeclaredField("value");
            valueReflect.setAccessible(true);
            Field coderReflect = String.class.getDeclaredField("coder");
            coderReflect.setAccessible(true);
            Field svLengthReflect = StringView.class.getDeclaredField("length");
            svLengthReflect.setAccessible(true);
            this.stringValueField = valueReflect;
            this.stringCoderField = coderReflect;
            this.stringViewLengthField = svLengthReflect;
        } catch (NoSuchFieldException e) {
            throw new RuntimeException("Failed to reflect String/StringView fields for length intrinsic", e);
        }
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the IC's flat call re-parsed on the stock path
        }
        if (!method.getName().equals("length")) {
            return false;
        }
        if (ZeroAdmitStock.active()) {
            return false; // a zero-admit profile compiles String as OFF does
        }
        if (!method.getDeclaringClass().toJavaName().equals("java.lang.String")) {
            return false;
        }
        if (method.getSignature().getParameterCount(false) != 0) {
            return false;
        }
        if (args.length != 1) {
            return false;
        }

        /* Always-virt: a terminal-body enclosing method rides the stock pipeline (see the class javadoc); other sites
         * continue below untouched. */
        if (StringAnalysisPolicy.alwaysVirtJdkTrivialApplies(b)) {
            return false;
        }

        ValueNode receiver = args[0];

        if (isExactStringStamp(receiver.stamp(NodeView.DEFAULT), b.getMetaAccess())) {
            ResolvedJavaField valueField = b.getMetaAccess().lookupJavaField(stringValueField);
            ResolvedJavaField coderField = b.getMetaAccess().lookupJavaField(stringCoderField);
            ValueNode value = b.add(LoadFieldNode.create(b.getAssumptions(), receiver, valueField));
            ValueNode coder = b.add(LoadFieldNode.create(b.getAssumptions(), receiver, coderField));
            ValueNode arrayLen = b.add(new ArrayLengthNode(value));
            ValueNode result = b.add(new RightShiftNode(arrayLen, coder));
            b.addPush(JavaKind.Int, result);
            return true;
        }

        if (!handleStringView && !handleLazyReps) {
            return false;
        }

        MetaAccessProvider meta = b.getMetaAccess();
        StructuredGraph graph = b.getGraph();
        ResolvedJavaType stringType = meta.lookupJavaType(String.class);
        ResolvedJavaField valueField = meta.lookupJavaField(stringValueField);
        ResolvedJavaField coderField = meta.lookupJavaField(stringCoderField);

        TypeReference exactString = TypeReference.createExactTrusted(stringType);
        LogicNode isString = graph.addOrUniqueWithInputs(InstanceOfNode.create(exactString, receiver));

        BeginNode stringBegin = b.add(new BeginNode());
        FixedWithNextNode predecessor = (FixedWithNextNode) stringBegin.predecessor();
        predecessor.setNext(null);
        BeginNode notStringBegin = b.add(new BeginNode());
        stringBegin.setNext(null);
        IfNode outerIf = b.add(new IfNode(isString, stringBegin, notStringBegin, BranchProbabilityNode.FAST_PATH_PROFILE));
        notStringBegin.setNext(null);
        predecessor.setNext(outerIf);

        LoadFieldNode stringValue = graph.add(LoadFieldNode.create(b.getAssumptions(), receiver, valueField));
        LoadFieldNode stringCoder = graph.add(LoadFieldNode.create(b.getAssumptions(), receiver, coderField));
        ArrayLengthNode stringArrayLen = graph.add(new ArrayLengthNode(stringValue));
        ValueNode stringResult = graph.addOrUnique(new RightShiftNode(stringArrayLen, stringCoder));
        EndNode stringEnd = graph.add(new EndNode());
        stringBegin.setNext(stringValue);
        stringValue.setNext(stringCoder);
        stringCoder.setNext(stringArrayLen);
        stringArrayLen.setNext(stringEnd);

        List<ValueNode> phiInputs = new ArrayList<>();
        List<EndNode> mergeEnds = new ArrayList<>();
        phiInputs.add(stringResult);
        mergeEnds.add(stringEnd);

        BeginNode currentFalseBegin = notStringBegin;

        if (handleStringView) {
            currentFalseBegin = addLengthFieldBranch(graph, b, meta, receiver, currentFalseBegin,
                            StringView.class, stringViewLengthField, phiInputs, mergeEnds);
        }

        JavaType returnType = method.getSignature().getReturnType(method.getDeclaringClass());
        StampPair returnStamp = StampFactory.forDeclaredType(b.getAssumptions(), returnType, false);
        MethodCallTargetNode fallbackCallTarget = graph.add(
                        new SubstrateMethodCallTargetNode(InvokeKind.Virtual, method, new ValueNode[]{receiver}, returnStamp));
        /*
         * The fallback goes through the parser's own invoke path, so it gets this bci's exception edge (a plain
         * InvokeNode has none). The outer IfNode ended the parser's current block, so the fallback's BeginNode is
         * appended as the current instruction; the call target is built here, so no plugin runs again.
         */
        assert b.hasParseTerminated() : "the fallback must start after the dispatch's control split";
        BeginNode fallbackBegin = b.append(new BeginNode());
        currentFalseBegin.setNext(fallbackBegin);
        b.handleReplacedInvoke(fallbackCallTarget, JavaKind.Int);
        ValueNode fallbackResult = b.pop(JavaKind.Int);
        EndNode fallbackEnd = b.append(new EndNode());
        phiInputs.add(fallbackResult);
        mergeEnds.add(fallbackEnd);

        AbstractMergeNode merge = b.append(new MergeNode());
        for (EndNode end : mergeEnds) {
            merge.addForwardEnd(end);
        }
        ValuePhiNode phi = new ValuePhiNode(StampFactory.forKind(JavaKind.Int), merge, phiInputs.toArray(new ValueNode[0]));
        graph.addOrUnique(phi);
        b.push(JavaKind.Int, phi);
        b.setStateAfter(merge);

        return true;
    }

    private BeginNode addLengthFieldBranch(StructuredGraph graph, GraphBuilderContext b, MetaAccessProvider meta,
                    ValueNode receiver, BeginNode currentFalseBegin, Class<?> repClass, Field lengthField,
                    List<ValueNode> phiInputs, List<EndNode> mergeEnds) {
        ResolvedJavaType repType = meta.lookupJavaType(repClass);
        ResolvedJavaField resolvedLengthField = meta.lookupJavaField(lengthField);
        TypeReference exactRep = TypeReference.createExactTrusted(repType);
        LogicNode isRep = graph.addOrUniqueWithInputs(InstanceOfNode.create(exactRep, receiver));

        BeginNode repBegin = graph.add(new BeginNode());
        BeginNode notRepBegin = graph.add(new BeginNode());
        IfNode repIf = graph.add(new IfNode(isRep, repBegin, notRepBegin, BranchProbabilityNode.FAST_PATH_PROFILE));
        currentFalseBegin.setNext(repIf);

        Stamp repStamp = StampFactory.objectNonNull(exactRep);
        PiNode repReceiver = graph.addOrUnique(new PiNode(receiver, repStamp, repBegin));
        LoadFieldNode repLen = graph.add(LoadFieldNode.create(b.getAssumptions(), repReceiver, resolvedLengthField));
        EndNode repEnd = graph.add(new EndNode());
        repBegin.setNext(repLen);
        repLen.setNext(repEnd);

        phiInputs.add(repLen);
        mergeEnds.add(repEnd);
        return notRepBegin;
    }

    private static boolean isExactStringStamp(Stamp stamp, MetaAccessProvider metaAccess) {
        if (!(stamp instanceof ObjectStamp os)) {
            return false;
        }
        return os.type() != null &&
                        os.type().equals(metaAccess.lookupJavaType(String.class)) &&
                        os.isExactType();
    }
}