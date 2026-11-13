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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.oracle.graal.pointsto.flow.ConstantPrimitiveSourceTypeFlow;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;

public final class SingleByteHeuristic implements Heuristic {

    private final List<String> rejections = new ArrayList<>();
    private final List<String> warnings = new ArrayList<>();
    private Set<String> doNotSingleByteKeys;

    @Override
    public List<InstrumentationDecision> apply(StringUtilizationGraph graph) {
        UsageSourceBuilder.ensureBuilt(graph);
        rejections.clear();
        warnings.clear();
        doNotSingleByteKeys = ConstantStringDependencyScanner.computeDoNotSingleByteKeys(graph);
        List<SugVertex> literalCandidates = new ArrayList<>();
        List<SugVertex> substringCandidates = new ArrayList<>();
        for (SugVertex v : graph.getVertices()) {
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc == null || !StringAnalysisPolicy.isUserCodeClass(enc)) {
                continue;
            }
            if (isCandidate(v)) {
                if (isLiteralCandidate(v)) {
                    literalCandidates.add(v);
                } else {
                    substringCandidates.add(v);
                }
            }
        }

        List<InstrumentationDecision> decisions = new ArrayList<>();
        for (SugVertex sub : substringCandidates) {
            // The substring admit requires positive downstream proof, as in the other heuristics: a length-1
            // substring whose trace is lost or empty is not admitted on absence alone. Incomplete candidates were
            // already filtered by isCandidate. A no-usage candidate is admitted with a warning (see AdmissionProof).
            if (reachesIntern(graph, sub)) {
                rejections.add("REJECT V" + sub.getId() + " (candidate @ " + sub.getSourceLocation() + "): " + INTERN_REASON);
                continue;
            }
            if (hasStrictClassCheck(graph, sub)) {
                rejections.add("REJECT V" + sub.getId() + " (candidate @ " + sub.getSourceLocation() + "): " + CLASS_CHECK_REASON);
                continue;
            }
            if (AdmissionProof.hasNoUsage(sub)) {
                warnings.add(AdmissionProof.noUsageWarning(sub, "candidate"));
            }
            decisions.add(new InstrumentationDecision(sub, OptimizationType.SINGLE_BYTE, null));
        }
        for (SugVertex lit : literalCandidates) {
            if (substringCandidates.isEmpty()) {
                rejections.add("REJECT V" + lit.getId() + " (literal @ " + lit.getSourceLocation() +
                                "): no runtime-created SingleByteString (substring) to interact with");
                continue;
            }
            if (StringAtoms.isSeedableLiteral(lit)) {
                // A seeded literal also needs positive downstream proof and no strict
                // class check (the replaced literal's class is SingleByteString; StringAnalysisChildNoFold keeps
                // lit.getClass() in the child IR); identity observations were refused by the walk (LITERAL_IDENTITY)
                String why = !AdmissionProof.hasPositiveDownstreamProof(graph, lit) ? AdmissionProof.LOST_TRACE_REASON
                                : hasStrictClassCheck(graph, lit) ? CLASS_CHECK_REASON : null;
                if (why != null) {
                    rejections.add("REJECT V" + lit.getId() + " (literal @ " + lit.getSourceLocation() + "): " + why);
                    continue;
                }
            }
            boolean interacts = hasUsageIntersecting(graph, lit, substringCandidates) ||
                            anySubstringUsageMatchesLiteral(graph, lit, substringCandidates);
            if (interacts && reachesIntern(graph, lit)) {
                rejections.add("REJECT V" + lit.getId() + " (literal @ " + lit.getSourceLocation() + "): " + INTERN_REASON);
            } else if (interacts) {
                decisions.add(new InstrumentationDecision(lit, OptimizationType.SINGLE_BYTE, null));
            } else {
                rejections.add("REJECT V" + lit.getId() + " (literal @ " + lit.getSourceLocation() +
                                "): no interaction with any runtime-created SingleByteString (substring)");
            }
        }
        return decisions;
    }

    /**
     * {@code intern()} rejects a SINGLE_BYTE candidate: the runtime intern table would publish the
     * {@code SingleByteString} to every later {@code intern()} caller, outside the candidate's tracked flow.
     */
    static final String INTERN_REASON = "intern() is a non-whitelisted use for SINGLE_BYTE (the runtime intern table would publish the rep)";

    /**
     * Whether an {@code intern} call (the user's {@code String.intern()} or SVM's {@code StringInternSupport.intern},
     * both SUG vertices named {@code intern}) is among the usage sites reachable from {@code v}, following each usage
     * site's own usages (the value it produces), without a depth limit. Over-approximate on purpose: an intern of a
     * value derived from the candidate also rejects.
     */
    static boolean reachesIntern(StringUtilizationGraph graph, SugVertex v) {
        Set<SugVertex> seen = new HashSet<>();
        java.util.ArrayDeque<SugVertex> work = new java.util.ArrayDeque<>();
        work.add(v);
        seen.add(v);
        while (!work.isEmpty()) {
            SugVertex x = work.poll();
            BitSet tags = x.getUsageTags();
            if (tags == null) {
                continue;
            }
            for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
                SugVertex u = graph.getUsageTag(i).usageSite();
                if (u == null || !seen.add(u)) {
                    continue;
                }
                if (isInternCall(u)) {
                    return true;
                }
                work.add(u);
            }
        }
        return false;
    }

    /**
     * A strict class check ({@code getClass()}, {@code Class.isInstance/cast}, an exact {@code instanceof}) of a SINGLE_BYTE candidate
     * rejects, as for String View and Lazy Concat: the replaced value's class is {@code SingleByteString}, so
     * {@code s.substring(i, i + 1).getClass().getName()} would print {@code com.oracle.svm.core.stringrep.SingleByteString}
     * where the JVM prints {@code java.lang.String}.
     */
    static final String CLASS_CHECK_REASON = "strict class check on a SINGLE_BYTE candidate (its class becomes SingleByteString)";

    /** A usage tag of {@code v} at a strict class-check site ({@code getClass}, {@code Class.cast/isInstance}). */
    static boolean hasStrictClassCheck(StringUtilizationGraph graph, SugVertex v) {
        BitSet tags = v.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            SugVertex u = graph.getUsageTag(i).usageSite();
            if (u != null && SugNameTables.isStrictClassCheckName(u.getMethodName(), u.getDeclaringClass())) {
                return true;
            }
        }
        return false;
    }

    static boolean isInternCall(SugVertex u) {
        return (u.getNodeType() == SugNodeType.STRING_METHOD_CALL || u.getNodeType() == SugNodeType.JDK_LIBRARY_CALL) && "intern".equals(u.getMethodName());
    }

    public List<String> getRejections() {
        return rejections;
    }

    /** The no-usage warnings of admitted candidates. */
    public List<String> getWarnings() {
        return warnings;
    }

    private boolean isCandidate(SugVertex v) {
        if (v.getLength() != 1) {
            return false;
        }
        boolean literal = v.getNodeType() == SugNodeType.STRING_LITERAL;
        boolean substring = v.getNodeType() == SugNodeType.STRING_METHOD_CALL && "substring".equals(v.getMethodName());
        boolean valueOfChar = v.getNodeType() == SugNodeType.STRING_METHOD_CALL && "valueOf".equals(v.getMethodName()) &&
                        ("char".equals(v.getMethodSignature()) || "C".equals(v.getMethodSignature()));
        if (!literal && !substring && !valueOfChar) {
            return false;
        }
        if (v.isIncompleteTrace()) {
            String reason = v.isResourceLimitedTrace() ? "method-summary resource limit" : "incomplete downstream trace";
            rejections.add("REJECT V" + v.getId() + " (candidate @ " + v.getSourceLocation() + "): " + reason);
            return false;
        }
        if (literal) {
            if (doNotSingleByteKeys != null && v.getSourceKey() != null && doNotSingleByteKeys.contains(v.getSourceKey())) {
                rejections.add("REJECT V" + v.getId() + " (literal @ " + v.getSourceLocation() +
                                "): constant-String consumer dependency (excluded by profile layer)");
                return false;
            }
            return true;
        }
        return substring || valueOfChar;
    }

    private boolean isLiteralCandidate(SugVertex v) {
        if (v.getNodeType() == SugNodeType.STRING_LITERAL) {
            return true;
        }
        if (v.getNodeType() == SugNodeType.STRING_METHOD_CALL && "valueOf".equals(v.getMethodName()) &&
                        ("char".equals(v.getMethodSignature()) || "C".equals(v.getMethodSignature()))) {
            TypeFlow<?> sourceFlow = v.getSourceFlow();
            if (sourceFlow instanceof InvokeTypeFlow inv) {
                TypeFlow<?>[] actuals = inv.getActualParameters();
                if (actuals != null && actuals.length > 0 && actuals[0] instanceof ConstantPrimitiveSourceTypeFlow) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean hasUsageIntersecting(StringUtilizationGraph graph, SugVertex lit, List<SugVertex> substringCandidates) {
        Set<SugVertex> subSet = new HashSet<>(substringCandidates);
        BitSet tags = lit.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            if (subSet.contains(graph.getUsageTag(i).usageSite())) {
                return true;
            }
        }
        return false;
    }

    private static boolean anySubstringUsageMatchesLiteral(StringUtilizationGraph graph, SugVertex lit, List<SugVertex> substringCandidates) {
        Set<SugVertex> litUsageSites = new HashSet<>();
        BitSet litTags = lit.getUsageTags();
        for (int i = litTags.nextSetBit(0); i >= 0; i = litTags.nextSetBit(i + 1)) {
            litUsageSites.add(graph.getUsageTag(i).usageSite());
        }
        for (SugVertex sub : substringCandidates) {
            BitSet subTags = sub.getUsageTags();
            for (int i = subTags.nextSetBit(0); i >= 0; i = subTags.nextSetBit(i + 1)) {
                SugVertex usage = graph.getUsageTag(i).usageSite();
                if (litUsageSites.contains(usage) && isEqualsCall(usage)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean isEqualsCall(SugVertex v) {
        if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL && v.getNodeType() != SugNodeType.JDK_LIBRARY_CALL) {
            return false;
        }
        return "equals".equals(v.getMethodName());
    }

    public Set<SugVertex> reachableMarkedVertices(StringUtilizationGraph graph, List<InstrumentationDecision> decisions) {
        UsageSourceBuilder.ensureBuilt(graph);
        Set<SugVertex> marked = new HashSet<>();
        for (InstrumentationDecision d : decisions) {
            marked.add(d.getCandidate());
            collectUsageTransitive(graph, d.getCandidate(), marked, new HashSet<>());
        }
        return marked;
    }

    private static void collectUsageTransitive(StringUtilizationGraph graph, SugVertex creationSite, Set<SugVertex> out, Set<SugVertex> visited) {
        if (!visited.add(creationSite)) {
            return;
        }
        BitSet tags = creationSite.getUsageTags();
        for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
            SugVertex usage = graph.getUsageTag(i).usageSite();
            if (out.add(usage)) {
                collectUsageTransitive(graph, usage, out, visited);
            }
        }
    }
}
