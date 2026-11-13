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

/**
 * The positive downstream proof (PDP) shared by the heuristics' admission gates: ADMIT requires positive proof that the
 * candidate's downstream was traced and found engaged; the absence of unsafe findings alone does not admit. PDP holds
 * when the analysis derived at least one of: (a) usage facts: a RECEIVER/NONE-role usage tag (each then validated
 * whitelisted-or-internal by the consuming heuristic); (b) safe-sink evidence: a PARAMETER-role tag at a terminal
 * argument site ({@code TransferFacts.isSafeSinkMethod}, the equals/compareTo argument, a mirrored builder entry point);
 * (c) wired heap path: the {@code wiredAnyLoad} bit (a STORE/ARRAY_STORE endpoint of one of the candidate's origins
 * wired a non-empty load set at some composeHeap seam, or, for skip shapes, the callee PARAM_ENTRY's own composeHeap
 * carried over the receiver bridge). PDP(c) never bypasses incompleteness: a wired load's incomplete path still rejects
 * via {@code isIncompleteTrace()}.
 * <p>
 * Verdict: ADMIT iff {@code validateUsages} passes, PDP holds and {@code !isIncompleteTrace()}. A candidate whose trace
 * is lost or empty rejects with {@link #LOST_TRACE_REASON}.
 */
public final class AdmissionProof {

    /** Rejection reason for a lost or empty downstream trace (distinct from "untraceable" and "incomplete downstream trace"). */
    public static final String LOST_TRACE_REASON = "lost downstream trace — no positive proof";

    /**
     * The no-usage policy: a candidate with no usage is admitted, since its value was traced to the end and nothing
     * reads it. Admitting is sound only because silent walk stops are closed: a walk that ends with no usage, no refusal
     * and no terminal would otherwise admit a value that is in fact read (e.g. {@code throw new AssertionError(concat)}: an NPE at run time). The engine refuses such an unmodelled exception flow
     * ({@code EXCEPTION_FLOW_UNMODELLED}), and the {@code fwd.rtrack.silentcensus} detector reports every walk that ends
     * silently ({@code [sug-fwd-silent-end]}; each must be a genuine drop). A no-usage candidate gets a WARNING line (a
     * detector, never a verdict). The warning text is kept verbatim (child logs are compared across builds).
     */
    public static final String NO_USAGE_WARNING = "no usage found — admitted (dev-time warning, not a verdict)";

    /** The candidate has no usage of any kind (no usage tag in any role). */
    static boolean hasNoUsage(SugVertex candidate) {
        return candidate.getUsageTags().isEmpty();
    }

    /** The per-candidate no-usage warning line ({@code kind} as in the heuristic's REJECT lines). */
    static String noUsageWarning(SugVertex candidate, String kind) {
        return "WARNING V" + candidate.getId() + " (" + kind + " @ " + candidate.getSourceLocation() + "): " + NO_USAGE_WARNING;
    }

    private AdmissionProof() {
    }

    /** PDP(a)+(b): any RECEIVER/NONE-role usage tag, or a PARAMETER-role tag at a terminal argument site. */
    private static boolean hasUsageFactProof(StringUtilizationGraph graph, SugVertex candidate) {
        BitSet tags = candidate.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            UsageTag tag = graph.getUsageTag(i);
            if (tag.role() == UsageRole.PARAMETER) {
                // PDP(b): a PARAMETER tag at a terminal argument site (a safe sink; the equals or compareTo argument,
                // whose String body is never entered; the string slot of a mirrored builder entry point). Any other
                // PARAMETER tag is a pass-through (the callee is entered and records its own usages).
                if (tag.usageSite() != null && (TransferFacts.isSafeSinkMethod(tag.usageSite()) || isTerminalEqualsArgument(tag) || isTerminalCompareToArgument(tag) ||
                                AppendMirror.isTerminalMirrorArgument(tag))) {
                    return true;
                }
                continue;
            }
            // PDP(a): RECEIVER/NONE-role usage facts (validated by the caller's validateUsages)
            return true;
        }
        return false;
    }

    /**
     * A PARAMETER tag at slot 1 of an {@code equals(Object)} call vertex (the equals-argument terminal; the engine never
     * enters {@code String.equals} for it): terminal evidence, as a safe-sink argument.
     */
    static boolean isTerminalEqualsArgument(UsageTag tag) {
        return tag.paramIndex() == 1 && EqualsMatrixHeuristic.isEqualsObjectCall(tag.usageSite());
    }

    /**
     * A PARAMETER tag at slot 1 of a {@code String.compareTo(String|Object)} site (the rep-aware compareTo
     * terminal; the String body is never entered): terminal evidence, as the equals argument.
     */
    static boolean isTerminalCompareToArgument(UsageTag tag) {
        SugVertex v = tag.usageSite();
        return tag.paramIndex() == 1 && v != null && "compareTo".equals(v.getMethodName()) && "java.lang.String".equals(v.getDeclaringClass()) &&
                        ("Ljava/lang/String;".equals(v.getMethodSignature()) || "Ljava/lang/Object;".equals(v.getMethodSignature()));
    }

    /** Whether the candidate carries PDP — (a) usage facts, (b) safe-sink, or (c) wired-heap. */
    public static boolean hasPositiveDownstreamProof(StringUtilizationGraph graph, SugVertex candidate) {
        // PDP(c): the wired-heap-path bit (composed by emit; independent of the usage tags).
        if (candidate.isWiredAnyLoad()) {
            return true;
        }
        return hasUsageFactProof(graph, candidate);
    }
}