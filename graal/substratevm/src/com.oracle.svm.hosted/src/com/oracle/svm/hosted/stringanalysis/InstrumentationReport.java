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
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class InstrumentationReport {

    private final StringAnalysisResults results;
    private final List<String> conflicts;

    public InstrumentationReport(StringAnalysisResults results, List<String> conflicts) {
        this.results = results;
        this.conflicts = conflicts;
    }

    public String dumpText() {
        StringBuilder sb = new StringBuilder();
        sb.append("===== String Analysis Instrumentation Report =====\n");
        sb.append("\n");
        sb.append("--- Summary ---\n");
        sb.append("  raw candidates      = ").append(results.getRawCandidateCount()).append("\n");
        sb.append("  precedence suppressed = ").append(results.getPrecedenceSuppressedCount()).append("\n");
        sb.append("  conflicts rejected  = ").append(results.getConflictCount()).append("\n");
        sb.append("  final validated     = ").append(results.getValidatedCount()).append("\n");
        sb.append("\n");

        Map<OptimizationType, Long> counts = countByType(results.getDecisions());
        sb.append("  --- validated by type ---\n");
        for (OptimizationType t : OptimizationType.values()) {
            if (t == OptimizationType.NONE) {
                continue;
            }
            long c = counts.getOrDefault(t, 0L);
            sb.append("    ").append(t).append(" = ").append(c).append("\n");
        }
        sb.append("\n");

        sb.append("--- Validated Decisions ---\n");
        List<InstrumentationDecision> sorted = new ArrayList<>(results.getDecisions());
        sorted.sort(Comparator.comparingInt(d -> d.getCandidate().getId()));
        for (InstrumentationDecision d : sorted) {
            sb.append(formatDecision(d)).append("\n");
        }
        sb.append("\n");

        if (!conflicts.isEmpty()) {
            sb.append("--- Conflicts (").append(conflicts.size()).append(") ---\n");
            for (String c : conflicts) {
                sb.append("  ").append(c).append("\n");
            }
            sb.append("\n");
        }

        sb.append("===== String Analysis Instrumentation Report (end) =====");
        return sb.toString();
    }

    public String dumpMachineReadable() {
        StringBuilder sb = new StringBuilder();
        sb.append("# String Analysis Instrumentation Report\n");
        sb.append("# format: vertex_id | source_location | enclosing_method | optimization_type | variant | label\n");
        sb.append("# raw_candidates=").append(results.getRawCandidateCount())
                        .append(" validated=").append(results.getValidatedCount())
                        .append(" conflicts=").append(results.getConflictCount())
                        .append(" precedence_suppressed=").append(results.getPrecedenceSuppressedCount()).append("\n");
        sb.append("---\n");
        List<InstrumentationDecision> sorted = new ArrayList<>(results.getDecisions());
        sorted.sort(Comparator.comparingInt(d -> d.getCandidate().getId()));
        for (InstrumentationDecision d : sorted) {
            SugVertex v = d.getCandidate();
            String enclosing = "null";
            if (v.getEnclosingMethod() != null) {
                enclosing = v.getEnclosingMethod().getDeclaringClass().toJavaName(true) + "#" + v.getEnclosingMethod().getName();
            }
            String label = v.getLiteralText();
            if (label == null) {
                label = v.getMethodName() != null ? v.getMethodName() : v.getLabel();
            }
            if (label == null) {
                label = "";
            }
            sb.append(v.getId()).append(" | ");
            sb.append(d.getSourceLocation()).append(" | ");
            sb.append(enclosing).append(" | ");
            sb.append(d.getType()).append(" | ");
            sb.append(d.getVariant() != null ? d.getVariant() : "").append(" | ");
            sb.append(escape(label));
            sb.append("\n");
        }
        return sb.toString();
    }

    private static String formatDecision(InstrumentationDecision d) {
        SugVertex v = d.getCandidate();
        StringBuilder sb = new StringBuilder();
        sb.append("  [V").append(v.getId()).append("] ");
        sb.append(d.getType());
        if (d.getVariant() != null) {
            sb.append("[").append(d.getVariant()).append("]");
        }
        sb.append("  @ ").append(d.getSourceLocation());
        if (v.getEnclosingMethod() != null) {
            sb.append("  in ").append(v.getEnclosingMethod().getDeclaringClass().toJavaName(true))
                            .append("#").append(v.getEnclosingMethod().getName());
        }
        if (v.getLiteralText() != null) {
            sb.append("  text=\"").append(escape(v.getLiteralText())).append("\"");
        }
        if (v.getMethodName() != null) {
            sb.append("  method=").append(v.getDeclaringClass()).append(".").append(v.getMethodName());
        }
        if (v.getLength() != SugVertex.UNKNOWN_LENGTH) {
            sb.append("  len=").append(v.getLength());
        }
        return sb.toString();
    }

    private static Map<OptimizationType, Long> countByType(List<InstrumentationDecision> decisions) {
        Map<OptimizationType, Long> counts = new LinkedHashMap<>();
        for (InstrumentationDecision d : decisions) {
            counts.merge(d.getType(), 1L, Long::sum);
        }
        return counts;
    }

    private static String escape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                case '|' -> sb.append("\\|");
                default -> sb.append(c);
            }
        }
        return sb.toString();
    }
}
