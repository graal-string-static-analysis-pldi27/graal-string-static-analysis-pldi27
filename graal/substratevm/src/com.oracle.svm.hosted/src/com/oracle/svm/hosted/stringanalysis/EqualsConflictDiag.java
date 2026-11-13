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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Print-only, default off (knob {@code -Dsvm.stringanalysis.eq.diag=1}): the inputs of the equals matrix
 * and the cross-rep conflict pass. Per call vertex of a String-argument method with any source tag: its source tags
 * (candidate, role, index, the candidate's decision or its conflict revert) and its EQUALS_MATRIX decision. Per
 * candidate: each usage tag at such a method, with whether the usage site is a SUG vertex (attached, seen by the
 * per-vertex passes) or a detached target site. Then the conflict lines. Lines are sorted (verdict-neutral).
 */
final class EqualsConflictDiag {

    static final boolean ON = Integer.getInteger("svm.stringanalysis.eq.diag", 0) != 0;

    static final Set<String> STRING_ARG_METHODS = Set.of("equals", "compareTo", "compareToIgnoreCase", "contentEquals", "equalsIgnoreCase",
                    "startsWith", "endsWith", "indexOf", "lastIndexOf", "regionMatches", "contains", "replace", "split", "matches", "concat");

    private EqualsConflictDiag() {
    }

    private static String dec(InstrumentationDecision d) {
        if (d == null) {
            return "none";
        }
        return d.getType() + (d.getVariant() != null ? "[" + d.getVariant() + "]" : "");
    }

    static void print(StringUtilizationGraph sug, List<InstrumentationDecision> validated, HeuristicOrchestrator orch) {
        if (!ON) {
            return;
        }
        Map<SugVertex, InstrumentationDecision> byCand = new IdentityHashMap<>();
        Map<SugVertex, InstrumentationDecision> emByVertex = new IdentityHashMap<>();
        for (InstrumentationDecision d : validated) {
            if (d.getType() == OptimizationType.EQUALS_MATRIX) {
                emByVertex.put(d.getCandidate(), d);
            } else if (d.getType() != OptimizationType.INLINE_CACHE) {
                byCand.put(d.getCandidate(), d);
            }
        }
        Map<SugVertex, InstrumentationDecision> suppressed = new IdentityHashMap<>();
        for (InstrumentationDecision d : orch.getConflictSuppressed()) {
            suppressed.put(d.getCandidate(), d);
        }
        Map<SugVertex, Boolean> attached = new IdentityHashMap<>();
        for (SugVertex v : sug.getVertices()) {
            attached.put(v, Boolean.TRUE);
        }
        TreeSet<String> lines = new TreeSet<>();
        for (SugVertex v : sug.getCallSiteVertices()) {
            if (!STRING_ARG_METHODS.contains(v.getMethodName())) {
                continue;
            }
            BitSet tags = v.getSourceTags();
            if (tags.isEmpty()) {
                continue;
            }
            List<String> ts = new ArrayList<>();
            for (int i = tags.nextSetBit(0); i >= 0; i = tags.nextSetBit(i + 1)) {
                SourceTag t = sug.getSourceTag(i);
                InstrumentationDecision d = byCand.get(t.creationSite());
                String sd = d != null ? dec(d) : suppressed.containsKey(t.creationSite()) ? "suppressed:" + dec(suppressed.get(t.creationSite())) : "none";
                ts.add(t.creationSite().getSourceLocation() + ":" + t.role() + ":" + t.paramIndex() + ":" + sd);
            }
            ts.sort(null);
            lines.add("[eq-diag] site " + v.getSourceLocation() + " " + v.getNodeType() + " " + v.getDeclaringClass() + "." + v.getMethodName() + "(" +
                            v.getMethodSignature() + ") tags=" + ts + " em=" + (emByVertex.containsKey(v) ? "REDIRECT" : "-"));
        }
        for (SugVertex c : sug.getVertices()) {
            BitSet ut = c.getUsageTags();
            if (ut.isEmpty()) {
                continue;
            }
            InstrumentationDecision d = byCand.get(c);
            for (int i = ut.nextSetBit(0); i >= 0; i = ut.nextSetBit(i + 1)) {
                UsageTag u = sug.getUsageTag(i);
                SugVertex s = u.usageSite();
                if (s == null || !STRING_ARG_METHODS.contains(s.getMethodName())) {
                    continue;
                }
                lines.add("[eq-diag] use cand=" + c.getSourceLocation() + " dec=" + (d != null ? dec(d) : suppressed.containsKey(c) ? "suppressed:" + dec(suppressed.get(c)) : "none") +
                                " site=" + s.getSourceLocation() + " " + s.getDeclaringClass() + "." + s.getMethodName() + "(" + s.getMethodSignature() + ") " + u.role() + ":" +
                                u.paramIndex() + (attached.containsKey(s) ? " attached" : " DETACHED"));
            }
        }
        for (String c : orch.getConflicts()) {
            lines.add("[eq-diag] conflict " + c.replaceAll("V[0-9]+", "V"));
        }
        for (String l : lines) {
            System.out.println(l);
        }
        System.out.println("[eq-diag] done lines=" + lines.size());
    }
}
