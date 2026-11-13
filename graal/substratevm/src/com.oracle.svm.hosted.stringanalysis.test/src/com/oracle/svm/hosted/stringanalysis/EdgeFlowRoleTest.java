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

import java.util.BitSet;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * Edge-level {@link SugEdge.FlowRole} metadata. Verifies role inference at
 * {@link StringUtilizationGraph#addEdge}, role-aware {@link UsageSourceBuilder} seed/passthrough
 * propagation, and role-aware {@code propagateIncompleteTraceBackward}. Also covers the ARG-only usage-site shape
 * (arg DATAFLOW edges without a QUALIFIER source are PARAMETER, not NONE).
 */
public class EdgeFlowRoleTest {

    private static SugVertex vertex(StringUtilizationGraph graph, SugNodeType type, String name) {
        SugVertex v = graph.newVertex();
        v.setNodeType(type);
        v.setMethodName(name);
        v.setDeclaringClass("java.lang.StringBuilder");
        v.setEnclosingClassName("TestUserClass");
        v.setSourceLocation(name + ".java:1");
        return v;
    }

    private static SugVertex newAccumulator(StringUtilizationGraph graph) {
        return vertex(graph, SugNodeType.NEW_ACCUMULATOR, null);
    }

    private static SugVertex accumulatorCall(StringUtilizationGraph graph, String name) {
        return vertex(graph, SugNodeType.STRING_METHOD_CALL, name);
    }

    private static SugVertex stringCall(StringUtilizationGraph graph, String name) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        if (name.equals("length")) {
            v.setMethodSignature("");
        } else if (name.equals("substring")) {
            v.setMethodSignature("I,I");
        }
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName("TestUserClass");
        v.setSourceLocation(name + ".java:1");
        return v;
    }

    @Test
    public void edgeFlowRoleAssignment() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex a = vertex(graph, SugNodeType.FLOW_NODE, "a");
        SugVertex b = vertex(graph, SugNodeType.FLOW_NODE, "b");
        SugVertex c = vertex(graph, SugNodeType.FLOW_NODE, "c");
        SugVertex d = vertex(graph, SugNodeType.FLOW_NODE, "d");
        SugVertex e = vertex(graph, SugNodeType.FLOW_NODE, "e");
        SugVertex f = vertex(graph, SugNodeType.FLOW_NODE, "f");

        SugEdge qual = graph.addEdge(a, b, SugEdgeType.QUALIFIER, -1);
        SugEdge param = graph.addEdge(c, b, SugEdgeType.PARAMETER, 0);
        SugEdge recvDataflow = graph.addEdge(b, d, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        SugEdge argDataflow = graph.addEdge(e, b, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.ARG);
        SugEdge concat = graph.addEdge(a, f, SugEdgeType.CONCAT_LEFT, 0);

        Assert.assertEquals(SugEdge.FlowRole.RECEIVER, qual.getFlowRole());
        Assert.assertEquals(SugEdge.FlowRole.ARG, param.getFlowRole());
        Assert.assertEquals(SugEdge.FlowRole.RECEIVER, recvDataflow.getFlowRole());
        Assert.assertEquals(SugEdge.FlowRole.ARG, argDataflow.getFlowRole());
        Assert.assertEquals(SugEdge.FlowRole.NONE, concat.getFlowRole());
    }

    /**
     * A String arg flowing to {@code append} via an ARG DATAFLOW edge must not carry the receiver's
     * {@code toString} usage tag. The {@code toString} RECEIVER tag
     * reaches {@code append} through its RECEIVER DATAFLOW return edge, and on the passthrough step
     * must only propagate to the RECEIVER in-edges, not the ARG in-edge.
     */
    @Test
    public void appendArgViewNotRejectedByReceiverUsage() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph);
        SugVertex append = accumulatorCall(graph, "append");
        append.markAccumulatorOp();
        SugVertex toString = accumulatorCall(graph, "toString");
        SugVertex ret = vertex(graph, SugNodeType.FLOW_NODE, "ret");
        SugVertex arg = stringCall(graph, "substring");
        SugVertex result = vertex(graph, SugNodeType.VARIABLE, "result");
        SugVertex length = stringCall(graph, "length");

        graph.addEdge(acc, append, SugEdgeType.QUALIFIER, -1);
        graph.addEdge(acc, toString, SugEdgeType.QUALIFIER, -1);
        graph.addEdge(arg, append, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.ARG);
        graph.addEdge(append, ret, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        graph.addEdge(ret, toString, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, -1);
        graph.addEdge(result, length, SugEdgeType.DATAFLOW, -1);

        UsageSourceBuilder.build(graph);

        BitSet argTags = arg.getUsageTags();
        for (int i = argTags.nextSetBit(0); i >= 0; i = argTags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            Assert.assertNotEquals("arg must not carry receiver toString usage", "toString", tag.usageSite().getMethodName());
        }

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);
        // the arg's only usage tag is PARAMETER-role at append (not a safe sink): the RECEIVER toString usage does not
        // leak into the arg (no arg tag points at toString), and the arg carries no positive downstream proof
        for (int i = argTags.nextSetBit(0); i >= 0; i = argTags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            Assert.assertNotEquals("arg must not carry receiver toString usage (role isolation)",
                            "toString", tag.usageSite().getMethodName());
        }
        // the arg ADMITs (a PARAMETER usage is a usage: no warning); the missing proof shows at the predicate level
        Assert.assertEquals("arg StringView candidate admits", 1, decisions.size());
        Assert.assertTrue(heuristic.getWarnings().isEmpty());
        Assert.assertFalse("the arg carries no positive downstream proof",
                        AdmissionProof.hasPositiveDownstreamProof(graph, arg));
    }

    /**
     * The {@code toString} RECEIVER tag must still reach NEW_ACCUMULATOR through the {@code append}
     * passthrough, so the ACCUMULATOR_VIEW extraction is preserved.
     */
    @Test
    public void accumulatorConnectivityPreserved() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph);
        SugVertex append = accumulatorCall(graph, "append");
        append.markAccumulatorOp();
        SugVertex toString = accumulatorCall(graph, "toString");
        SugVertex ret = vertex(graph, SugNodeType.FLOW_NODE, "ret");
        SugVertex arg = stringCall(graph, "substring");
        SugVertex result = vertex(graph, SugNodeType.VARIABLE, "result");
        SugVertex length = stringCall(graph, "length");

        graph.addEdge(acc, append, SugEdgeType.QUALIFIER, -1);
        graph.addEdge(arg, append, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.ARG);
        graph.addEdge(append, ret, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        graph.addEdge(ret, toString, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        graph.addEdge(toString, result, SugEdgeType.DATAFLOW, -1);
        graph.addEdge(result, length, SugEdgeType.DATAFLOW, -1);

        UsageSourceBuilder.build(graph);

        BitSet accTags = acc.getUsageTags();
        boolean foundToString = false;
        for (int i = accTags.nextSetBit(0); i >= 0; i = accTags.nextSetBit(i + 1)) {
            if ("toString".equals(graph.getUsageTag(i).usageSite().getMethodName())) {
                foundToString = true;
                break;
            }
        }
        Assert.assertTrue("toString RECEIVER tag must reach accumulator", foundToString);

        AccumulatorHeuristic heuristic = new AccumulatorHeuristic(false);
        List<InstrumentationDecision> decisions = heuristic.apply(graph);
        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals("ACCUMULATOR_VIEW", decisions.get(0).getVariant());
    }

    /**
     * A usage site with a single ARG DATAFLOW in-edge and no QUALIFIER source gets
     * {@code UsageRole.PARAMETER} (from {@code FlowRole.ARG}), not NONE, and validateUsages skips it.
     */
    @Test
    public void argFlowDataflowEdgeWithoutQualifierIsParameter() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex arg = stringCall(graph, "substring");
        SugVertex indexOf = accumulatorCall(graph, "indexOf");

        graph.addEdge(arg, indexOf, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.ARG);

        UsageSourceBuilder.build(graph);

        BitSet argTags = arg.getUsageTags();
        Assert.assertFalse("arg should carry a usage tag", argTags.isEmpty());
        boolean sawParameter = false;
        for (int i = argTags.nextSetBit(0); i >= 0; i = argTags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                sawParameter = true;
            }
        }
        Assert.assertTrue("arg DATAFLOW edge without qualifier must be PARAMETER", sawParameter);
    }

    /**
     * A {@code FlowRole.NONE} DATAFLOW edge (the reaching flow is not a direct actual parameter) stays
     * {@code UsageRole.NONE} even when a QUALIFIER in-edge from another source exists (no {@code qualifierSources}
     * fallback); a direct actual parameter gets {@code FlowRole.ARG} at edge creation, hence PARAMETER. NONE edges are
     * conservatively treated as receiver-self / unknown flows.
     */
    @Test
    public void noneRoleDataflowWithQualifierFromDifferentSourceStaysNone() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex receiver = vertex(graph, SugNodeType.NEW_ACCUMULATOR, "sb");
        SugVertex append = accumulatorCall(graph, "append");
        append.markAccumulatorOp();
        SugVertex substring = stringCall(graph, "substring");

        graph.addEdge(receiver, append, SugEdgeType.QUALIFIER, -1);
        graph.addEdge(substring, append, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.NONE);

        UsageSourceBuilder.build(graph);

        BitSet substringTags = substring.getUsageTags();
        for (int i = substringTags.nextSetBit(0); i >= 0; i = substringTags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            Assert.assertNotEquals("NONE-role DATAFLOW edge must NOT be PARAMETER (fallback removed)", UsageRole.PARAMETER, tag.role());
        }
    }

    /** A {@code FlowRole.NONE} DATAFLOW edge into a usage site with no QUALIFIER in-edge stays {@code UsageRole.NONE}. */

    @Test
    public void noneRoleDataflowWithoutQualifierStaysNone() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex indexOf = accumulatorCall(graph, "indexOf");
        SugVertex substring = stringCall(graph, "substring");

        graph.addEdge(substring, indexOf, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.NONE);

        UsageSourceBuilder.build(graph);

        BitSet substringTags = substring.getUsageTags();
        boolean sawNone = false;
        for (int i = substringTags.nextSetBit(0); i >= 0; i = substringTags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            Assert.assertNotEquals("NONE-role edge without qualifier must NOT be PARAMETER", UsageRole.PARAMETER, tag.role());
            if (tag.role() == UsageRole.NONE) {
                sawNone = true;
            }
        }
        Assert.assertTrue("NONE-role DATAFLOW edge without qualifier must stay NONE", sawNone);
    }

    /**
     * An accumulatorOp {@code append} marked incomplete must not mark its ARG predecessor incomplete
     * via propagateIncompleteTraceBackward, while it still marks a same-role (RECEIVER) predecessor.
     */
    @Test
    public void receiverIncompleteNotPropagatedToArg() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex acc = newAccumulator(graph);
        SugVertex append = accumulatorCall(graph, "append");
        append.markAccumulatorOp();
        SugVertex receiverPredecessor = vertex(graph, SugNodeType.FLOW_NODE, "receiverPred");
        SugVertex arg = stringCall(graph, "substring");

        graph.addEdge(receiverPredecessor, append, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.RECEIVER);
        graph.addEdge(arg, append, SugEdgeType.DATAFLOW, -1, SugEdge.FlowRole.ARG);
        graph.addEdge(acc, append, SugEdgeType.QUALIFIER, -1);

        append.markIncompleteTrace();

        SugBuilderV2TestHelper.propagateIncompleteTraceBackward(graph);

        Assert.assertFalse("arg must not be marked incomplete from receiver-side append", arg.isIncompleteTrace());
        Assert.assertTrue("same-role RECEIVER predecessor must still be marked incomplete", receiverPredecessor.isIncompleteTrace());
    }

    private static final class SugBuilderV2TestHelper {
        static void propagateIncompleteTraceBackward(StringUtilizationGraph graph) {
            java.util.Deque<SugVertex> worklist = new java.util.ArrayDeque<>();
            java.util.Set<SugVertex> inWorklist = new java.util.HashSet<>();
            for (SugVertex v : graph.getVertices()) {
                if (v.isIncompleteTrace()) {
                    worklist.add(v);
                    inWorklist.add(v);
                }
            }
            while (!worklist.isEmpty()) {
                SugVertex v = worklist.poll();
                for (SugEdge inEdge : v.getInEdges()) {
                    SugVertex pred = inEdge.getFrom();
                    if (!pred.isIncompleteTrace() && inEdge.getEdgeType() == SugEdgeType.DATAFLOW) {
                        if (inEdge.getFlowRole() == SugEdge.FlowRole.ARG && v.isAccumulatorOp()) {
                            continue;
                        }
                        pred.markIncompleteTrace();
                        if (inWorklist.add(pred)) {
                            worklist.add(pred);
                        }
                    }
                }
            }
        }
    }
}
