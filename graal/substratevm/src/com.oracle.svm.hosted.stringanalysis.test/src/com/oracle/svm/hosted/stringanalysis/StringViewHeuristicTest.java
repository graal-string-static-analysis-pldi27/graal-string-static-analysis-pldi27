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

import java.util.List;

import org.junit.Assert;
import org.junit.Test;

public class StringViewHeuristicTest {

    private static SugVertex substringCandidate(StringUtilizationGraph graph, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("substring");
        v.setMethodSignature("I,I");
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        v.setEnclosingClassName("TestUserClass");
        return v;
    }

    private static SugVertex subSequenceCandidate(StringUtilizationGraph graph, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("subSequence");
        v.setMethodSignature("I,I");
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        v.setEnclosingClassName("TestUserClass");
        return v;
    }

    private static SugVertex call(StringUtilizationGraph graph, String name, String sig, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        v.setDeclaringClass("java.lang.String");
        v.setSourceLocation(loc);
        return v;
    }

    @Test
    public void substringWithAllWhitelistedCallsAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex length = call(graph, "length", "", "S.java:2");
        SugVertex charAt = call(graph, "charAt", "I", "S.java:3");
        SugVertex equals = call(graph, "equals", "Ljava/lang/Object;", "S.java:4");
        graph.addEdge(sub, length, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, charAt, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(sub, equals, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertSame(sub, decisions.get(0).getCandidate());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void substringReachingNonWhitelistedCallRejected() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex replace = call(graph, "replace", "CC", "S.java:2");
        graph.addEdge(sub, replace, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("replace"));
    }

    @Test
    public void nestedSubstringBothAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex outer = substringCandidate(graph, "S.java:1");
        SugVertex inner = substringCandidate(graph, "S.java:2");
        SugVertex length = call(graph, "length", "", "S.java:3");
        graph.addEdge(outer, inner, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(inner, length, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(2, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void toUpperCaseLengthPreservingWhitelistedAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex upper = call(graph, "toUpperCase", "", "S.java:2");
        SugVertex length = call(graph, "length", "", "S.java:3");
        graph.addEdge(sub, upper, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(upper, length, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertSame(sub, decisions.get(0).getCandidate());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void subSequenceCandidateWithWhitelistedCallsAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex subSeq = subSequenceCandidate(graph, "S.java:1");
        SugVertex length = call(graph, "length", "", "S.java:2");
        SugVertex charAt = call(graph, "charAt", "I", "S.java:3");
        graph.addEdge(subSeq, length, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(subSeq, charAt, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertSame(subSeq, decisions.get(0).getCandidate());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void internCallRejectsStringView() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex receiver = graph.newVertex();
        receiver.setNodeType(SugNodeType.FLOW_NODE);
        receiver.setDeclaringClass("java.lang.String");
        receiver.setSourceLocation("S.java:2");
        SugVertex intern = graph.newVertex();
        intern.setNodeType(SugNodeType.STRING_METHOD_CALL);
        intern.setMethodName("intern");
        intern.setDeclaringClass("java.lang.String");
        intern.setMethodSignature("Ljava/lang/String;");
        intern.setLabel("String.intern");
        intern.setSourceLocation("S.java:3");
        graph.addEdge(sub, receiver, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(receiver, intern, SugEdgeType.QUALIFIER, -1);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("intern"));
    }

    @Test
    public void internalClassCandidateSkipped() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = graph.newVertex();
        sub.setNodeType(SugNodeType.STRING_METHOD_CALL);
        sub.setMethodName("substring");
        sub.setDeclaringClass("java.lang.String");
        sub.setSourceLocation("S.java:1");
        sub.setEnclosingClassName("java.lang.String");

        List<InstrumentationDecision> decisions = new StringViewHeuristic().apply(graph);

        Assert.assertTrue(decisions.isEmpty());
    }

    @Test
    public void jdkLibraryCallWhitelistedSkipsTraversal() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex jdkCall = graph.newVertex();
        jdkCall.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        jdkCall.setMethodName("length");
        jdkCall.setDeclaringClass("java.lang.String");
        jdkCall.setMethodSignature("");
        jdkCall.setSourceLocation("String.java:5");
        SugVertex downstream = graph.newVertex();
        downstream.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(sub, jdkCall, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(jdkCall, downstream, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    @Test
    public void jdkLibraryCallNonWhitelistedRejects() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex jdkCall = graph.newVertex();
        jdkCall.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        jdkCall.setMethodName("replace");
        jdkCall.setDeclaringClass("java.lang.String");
        jdkCall.setMethodSignature("CC");
        jdkCall.setSourceLocation("String.java:5");
        graph.addEdge(sub, jdkCall, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertTrue(decisions.isEmpty());
        Assert.assertEquals(1, heuristic.getRejections().size());
        Assert.assertTrue(heuristic.getRejections().get(0).contains("replace"));
    }

    @Test
    public void isolatedCandidateWithNoOutEdgesAdmittedWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // no usage is not a rejection reason: the candidate ADMITs with the dev-time warning.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertTrue(AdmissionProof.hasNoUsage(sub));
        Assert.assertFalse(AdmissionProof.hasPositiveDownstreamProof(graph, sub));
    }

    @Test
    public void isolatedSubSequenceCandidateWithNoOutEdgesAdmittedWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex subSeq = subSequenceCandidate(graph, "S.java:1");

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // ADMIT with the warning.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
    }

    /**
     * A candidate with out-edges to non-call vertices, a complete trace and no usage facts: out-edges exist but
     * nothing is proven downstream. It is ADMITted with the no-usage warning (it is neither
     * isolated nor incomplete, just empty of proof).
     */
    @Test
    public void completeTraceNoUsagesNoProofAdmittedWithWarningUnderDecision6() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        SugVertex variable = graph.newVertex();
        variable.setNodeType(SugNodeType.VARIABLE);
        graph.addEdge(sub, passthrough, SugEdgeType.DATAFLOW, 0);
        graph.addEdge(passthrough, variable, SugEdgeType.DATAFLOW, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // a complete trace with no usages and no proof ADMITs with the warning. The no-proof
        // predicate is pinned.
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertTrue(AdmissionProof.hasNoUsage(sub));
        Assert.assertFalse("out-edges to non-call vertices prove nothing", AdmissionProof.hasPositiveDownstreamProof(graph, sub));
        // the no-usage detector: a warning line, never a REJECT line
        Assert.assertEquals(1, heuristic.getWarnings().size());
        Assert.assertTrue(heuristic.getWarnings().get(0).startsWith("WARNING V" + sub.getId() + " (substring @ S.java:1): "));
        Assert.assertTrue(heuristic.getWarnings().get(0).contains(AdmissionProof.NO_USAGE_WARNING));
        Assert.assertFalse(heuristic.getWarnings().get(0).contains("REJECT"));
    }

    /**
     * A candidate whose only usage fact is a PARAMETER-role tag at a designated safe sink
     * (PrintStream.println(String)) carries safe-sink evidence: ADMIT (the JMH-Blackhole-style terminal shape).
     */
    @Test
    public void safeSinkEvidenceCandidateAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex sink = graph.newVertex();
        sink.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        sink.setDeclaringClass("java.io.PrintStream");
        sink.setMethodName("println");
        sink.setMethodSignature("Ljava/lang/String;");
        sink.setSourceLocation("PrintStream.java:5");
        graph.addEdge(sub, sink, SugEdgeType.PARAMETER, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    /**
     * A candidate with no usage facts whose {@code wiredAnyLoad} bit is set (a STORE endpoint of one of its origins
     * wired a non-empty load set, emitted by MethodSummaryTransfer.emit) carries the wired-heap-path proof: ADMIT.
     * Without the bit this shape has no positive downstream proof (see
     * {@link #completeTraceNoUsagesNoProofAdmittedWithWarningUnderDecision6}).
     */
    @Test
    public void wiredHeapPathCandidateAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex passthrough = graph.newVertex();
        passthrough.setNodeType(SugNodeType.FLOW_NODE);
        graph.addEdge(sub, passthrough, SugEdgeType.DATAFLOW, 0);
        sub.markWiredAnyLoad();

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    /**
     * A candidate with a RECEIVER-role whitelisted usage fact (equals) is the usage-validated admit: the traced usage
     * fact is the proof (pins the PDP(a) arm against regressing into an absence signal).
     */
    @Test
    public void usageValidatedCandidateAccepted() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex equals = call(graph, "equals", "Ljava/lang/Object;", "S.java:2");
        graph.addEdge(sub, equals, SugEdgeType.QUALIFIER, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertEquals(1, decisions.size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, decisions.get(0).getType());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
    }

    /**
     * A PARAMETER-role tag at a call that is not a safe sink (not in SAFE_SINKS) is an argument pass-through, not
     * terminal evidence: no PDP. The candidate is still ADMITted (a PARAMETER usage is a usage, so no no-usage warning).
     */
    @Test
    public void parameterTagAtNonSafeSinkIsNotProof() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex append = call(graph, "append", "Ljava/lang/String;", "S.java:2");
        append.setDeclaringClass("java.lang.StringBuilder");
        graph.addEdge(sub, append, SugEdgeType.PARAMETER, 0);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        // the candidate ADMITs (a PARAMETER usage is a usage: no no-usage warning), but the non-safe-sink PARAMETER
        // is not positive downstream proof; the distinction holds at the predicate level
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertTrue("a PARAMETER usage is a usage: no no-usage warning", heuristic.getWarnings().isEmpty());
        Assert.assertFalse("a PARAMETER tag at a non-safe-sink site is not proof", AdmissionProof.hasPositiveDownstreamProof(graph, sub));
    }

    /**
     * The terminal equals argument is an ordinary usage. A candidate whose
     * only use is {@code plain.equals(sv)} (a PARAMETER tag at slot 1 of an {@code equals(Object)} vertex) is terminal
     * evidence like a safe-sink argument: ADMIT, and no no-usage warning.
     */
    @Test
    public void equalsArgumentIsAUsageNoWarning() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex sub = substringCandidate(graph, "S.java:1");
        SugVertex equals = call(graph, "equals", "Ljava/lang/Object;", "S.java:2");
        graph.addEdge(sub, equals, SugEdgeType.PARAMETER, 1);

        StringViewHeuristic heuristic = new StringViewHeuristic();
        List<InstrumentationDecision> decisions = heuristic.apply(graph);

        Assert.assertFalse("the equals argument is a recorded usage", sub.getUsageTags().isEmpty());
        Assert.assertEquals(1, decisions.size());
        Assert.assertTrue(heuristic.getRejections().isEmpty());
        Assert.assertTrue("no no-usage warning for an equals-argument usage", heuristic.getWarnings().isEmpty());
    }

    /** Slot 0 (not the argument) and a non-{@code equals(Object)} vertex are not the equals-argument terminal. */
    @Test
    public void onlySlot1OfEqualsObjectIsTheTerminalArgument() {
        for (String[] c : new String[][]{{"equals", "Ljava/lang/Object;", "0"}, {"equals", "(Ljava/lang/Object;)", "1"}, {"equalsIgnoreCase", "Ljava/lang/String;", "1"}}) {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex sub = substringCandidate(graph, "S.java:1");
            SugVertex site = call(graph, c[0], c[1], "S.java:2");
            graph.addEdge(sub, site, SugEdgeType.PARAMETER, Integer.parseInt(c[2]));
            StringViewHeuristic heuristic = new StringViewHeuristic();
            // a non-terminal PARAMETER usage still ADMITs (a usage, no warning) but carries no positive downstream
            // proof; the terminal-argument distinction holds at the predicate level

            Assert.assertEquals(String.join(" ", c), 1, heuristic.apply(graph).size());
            Assert.assertTrue(String.join(" ", c), heuristic.getWarnings().isEmpty());
            Assert.assertFalse(String.join(" ", c), AdmissionProof.hasPositiveDownstreamProof(graph, sub));
        }
    }
}
