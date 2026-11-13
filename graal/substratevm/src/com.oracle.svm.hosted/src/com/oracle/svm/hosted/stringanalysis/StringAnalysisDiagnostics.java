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
import java.util.Set;
import java.util.TreeSet;

import com.oracle.svm.core.SubstrateOptions;

/**
 * Diagnostic print helpers of the string analysis feature (verdict-inert): the captured-site summary, the
 * per-heuristic diagnostics report and the filtered report formatter.
 */
final class StringAnalysisDiagnostics {

    static void printCapturedSites() {
        int concat = 0, append = 0, substring = 0, concatMethod = 0;
        for (List<CapturedSite> sites : StringAnalysisFeature.CAPTURED.values()) {
            for (CapturedSite s : sites) {
                if (s instanceof ConcatSite) {
                    concat++;
                } else if (s instanceof ConcatMethodSite) {
                    concatMethod++;
                } else if (s instanceof AccumulatorOpSite) {
                    append++;
                } else if (s instanceof SubstringArithSite) {
                    substring++;
                }
            }
        }
        System.out.println("[string-analysis-capture] concat sites = " + concat +
                        ", concat-method sites = " + concatMethod +
                        ", accumulator-op sites = " + append +
                        ", substring sites = " + substring);
        StringAnalysisFeature.CAPTURED.forEach((m, sites) -> {
            String cls = m.getDeclaringClass().toJavaName(true);
            if (!cls.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                return;
            }
            for (CapturedSite s : sites) {
                System.out.println("  " + cls + " :: " + describe(s));
            }
        });
    }

    private static String describe(CapturedSite s) {
        if (s instanceof ConcatSite c) {
            StringBuilder sb = new StringBuilder("CONCAT_SITE @ ").append(c.sourceLocation())
                            .append(" bci=").append(c.bci()).append(" ").append(c.bootstrapName())
                            .append(" operands=").append(c.totalOperandCount())
                            .append(" (dyn=").append(c.dynamicOperandCount()).append(")");
            List<OperandRef> ops = c.operands();
            for (int i = 0; i < ops.size(); i++) {
                OperandRef op = ops.get(i);
                sb.append(" [").append(i).append("@").append(op.sourceLocation() == null ? "?" : op.sourceLocation())
                                .append(":").append(op.operandBci()).append("]");
            }
            return sb.toString();
        } else if (s instanceof ConcatMethodSite cm) {
            List<OperandRef> ops = cm.operands();
            String recv = (ops.size() > 0 && ops.get(0) != null) ? (ops.get(0).sourceLocation() == null ? "?" : ops.get(0).sourceLocation()) : "?";
            String arg = (ops.size() > 1 && ops.get(1) != null) ? (ops.get(1).sourceLocation() == null ? "?" : ops.get(1).sourceLocation()) : "?";
            return "CONCAT_METHOD_SITE @ " + cm.sourceLocation() + " bci=" + cm.bci() +
                            " operands=" + ops.size() + " recv@" + recv + " arg@" + arg;
        } else if (s instanceof AccumulatorOpSite a) {
            return "APPEND_SITE @ " + a.sourceLocation() + " bci=" + a.bci() + " " + a.targetQualified() + " argc=" + a.argCount() +
                            " recv@" + (a.receiverLocation() == null ? "?" : a.receiverLocation());
        } else if (s instanceof SubstringArithSite sub) {
            return "SUBSTRING_SITE @ " + sub.sourceLocation() + " bci=" + sub.bci() + " " + sub.name() +
                            " unitRange=" + sub.unitRange();
        }
        return String.valueOf(s);
    }

    static String buildDiagnostics(StringUtilizationGraph sug, LengthPropagator propagator,
                    SingleByteHeuristic singleByte, List<InstrumentationDecision> singleByteDecisions,
                    StringViewHeuristic stringView, List<InstrumentationDecision> stringViewDecisions,
                    LazyConcatHeuristic lazyConcat, List<InstrumentationDecision> lazyConcatDecisions,
                    AccumulatorHeuristic accumulator, List<InstrumentationDecision> accumulatorDecisions,
                    EqualsMatrixHeuristic equalsMatrix, List<InstrumentationDecision> equalsMatrixDecisions,
                    HeuristicOrchestrator orchestrator, List<InstrumentationDecision> validated,
                    InstrumentationReport report) {
        // The accepted counters and decision lines exclude the cross-rep equals conflict reverts (the 3-source protocol:
        // a reverted candidate has its REJECT line and no profile entry)
        Set<InstrumentationDecision> reverted = orchestrator.getCrossRepEqualsReverted();
        singleByteDecisions = withoutReverted(singleByteDecisions, reverted);
        stringViewDecisions = withoutReverted(stringViewDecisions, reverted);
        lazyConcatDecisions = withoutReverted(lazyConcatDecisions, reverted);
        accumulatorDecisions = withoutReverted(accumulatorDecisions, reverted);
        StringBuilder sb = new StringBuilder();
        sb.append("===== String Utilization Graph (full) =====\n");
        sb.append("  total vertices = ").append(sug.getVertices().size()).append("\n");
        sb.append("  total edges    = ").append(sug.getEdges().size()).append("\n");
        sug.vertexTypeCounts().forEach((t, c) -> sb.append("  ").append(t).append(" = ").append(c).append("\n"));
        sb.append("  --- length propagation ---\n");
        sb.append("  E1 (literal)    = ").append(propagator.getE1Count()).append("\n");
        sb.append("  E2 (substring)  = ").append(propagator.getE2Count()).append("\n");
        sb.append("  E3 (unit-range) = ").append(propagator.getE3Count()).append("\n");
        sb.append("  E4 (forward)    = ").append(propagator.getE4Count()).append("\n");
        sb.append("  conflicts (E5)  = ").append(propagator.getConflictCount()).append("\n");
        sb.append("  assigned total  = ").append(propagator.getAssignedCount()).append("\n");
        sb.append("  --- non-internal enclosing classes (prefix-list validation) ---\n");
        TreeSet<String> nonInternalClasses = new TreeSet<>();
        for (SugVertex v : sug.getVertices()) {
            String enc = StringAnalysisPolicy.enclosingClassName(v);
            if (enc != null && !StringAnalysisPolicy.isInternalClass(enc)) {
                nonInternalClasses.add(enc);
            }
        }
        for (String cls : nonInternalClasses) {
            sb.append("    ").append(cls).append("\n");
        }
        sb.append("\n");

        sb.append("===== Single-Byte Heuristic =====\n");
        sb.append("  candidates = ").append(singleByteDecisions.size()).append("\n");
        sb.append("  rejections = ").append(singleByte.getRejections().size()).append("\n");
        for (InstrumentationDecision d : singleByteDecisions) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(d.describe()).append("\n");
            }
        }
        for (String r : singleByte.getRejections()) {
            if (r.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(r).append("\n");
            }
        }
        appendNoUsageWarnings(sb, singleByte.getWarnings());
        sb.append("===== Single-Byte Heuristic (end) =====\n\n");

        sb.append("===== String View Heuristic =====\n");
        sb.append("  candidates (accepted) = ").append(stringViewDecisions.size()).append("\n");
        sb.append("  rejections = ").append(stringView.getRejections().size()).append("\n");
        for (InstrumentationDecision d : stringViewDecisions) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(d.describe()).append("\n");
            }
        }
        for (String r : stringView.getRejections()) {
            if (r.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(r).append("\n");
            }
        }
        appendNoUsageWarnings(sb, stringView.getWarnings());
        sb.append("===== String View Heuristic (end) =====\n\n");

        sb.append("===== Lazy Concat Heuristic =====\n");
        sb.append("  CONCAT_EXPRESSION vertices = ").append(lazyConcat.getConcatExpressionTotal()).append("\n");
        sb.append("  outermost candidates = ").append(lazyConcat.getCandidateCount()).append("\n");
        sb.append("  accepted = ").append(lazyConcatDecisions.size()).append("\n");
        sb.append("  rejections = ").append(lazyConcat.getRejections().size()).append("\n");
        for (InstrumentationDecision d : lazyConcatDecisions) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(d.describe()).append("\n");
            }
        }
        for (String r : lazyConcat.getRejections()) {
            if (r.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(r).append("\n");
            }
        }
        appendNoUsageWarnings(sb, lazyConcat.getWarnings());
        if (lazyConcat.getConcatExpressionTotal() == 0) {
            sb.append("  NOTE: no CONCAT_EXPRESSION vertices found.\n");
        }
        sb.append("===== Lazy Concat Heuristic (end) =====\n\n");

        sb.append("===== Accumulator Heuristic =====\n");
        sb.append("  NEW_ACCUMULATOR candidates = ").append(accumulator.getCandidateCount()).append("\n");
        sb.append("  accepted = ").append(accumulatorDecisions.size()).append("\n");
        sb.append("  rejections = ").append(accumulator.getRejections().size()).append("\n");
        for (InstrumentationDecision d : accumulatorDecisions) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(d.describe()).append("\n");
            }
        }
        for (String r : accumulator.getRejections()) {
            if (r.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(r).append("\n");
            }
        }
        appendNoUsageWarnings(sb, accumulator.getWarnings());
        sb.append("===== Accumulator Heuristic (end) =====\n\n");

        sb.append("===== Equals Matrix Heuristic =====\n");
        int totalEquals = equalsMatrix.getRedirectCount() + equalsMatrix.getFastPathCount();
        sb.append("  total equals vertices = ").append(totalEquals).append("\n");
        sb.append("  REDIRECT  = ").append(equalsMatrix.getRedirectCount()).append("\n");
        sb.append("  FAST_PATH = ").append(equalsMatrix.getFastPathCount()).append("\n");
        for (InstrumentationDecision d : equalsMatrixDecisions) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(d.describe()).append("\n");
            }
        }
        sb.append("===== Equals Matrix Heuristic (end) =====\n\n");

        sb.append("===== Prioritization + Validation Pass =====\n");
        sb.append("  raw candidates = ").append(orchestrator.getRawCount()).append("\n");
        sb.append("  precedence suppressed = ").append(orchestrator.getPrecedenceSuppressed().size()).append("\n");
        sb.append("  conflicts = ").append(orchestrator.getConflicts().size()).append("\n");
        sb.append("  final validated = ").append(validated.size()).append("\n");
        orchestrator.validatedCountsByType().forEach((t, c) -> sb.append("    ").append(t).append(" = ").append(c).append("\n"));
        for (InstrumentationDecision d : orchestrator.getPrecedenceSuppressed()) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  SUPPRESSED ").append(d.describe()).append("\n");
            }
        }
        for (String c : orchestrator.getConflicts()) {
            if (c.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(c).append("\n");
            }
        }
        sb.append("===== Prioritization + Validation Pass (end) =====\n\n");

        sb.append(report.dumpText()).append("\n\n");
        sb.append(sug.dumpTextFiltered(SubstrateOptions.StringAnalysisDumpFilter.getValue())).append("\n\n");
        sb.append(sug.dumpLengthSummary(SubstrateOptions.StringAnalysisDumpFilter.getValue()));
        return sb.toString();
    }

    static String reportFiltered(InstrumentationReport report, List<InstrumentationDecision> validated, String filter) {
        StringBuilder sb = new StringBuilder();
        sb.append("# String Analysis Instrumentation Report (filtered: ").append(filter).append(")\n");
        sb.append("# format: vertex_id | source_location | enclosing_method | optimization_type | variant | label\n");
        sb.append("---\n");
        for (InstrumentationDecision d : validated) {
            String enc = enclosingClassName(d.getCandidate());
            if (enc != null && enc.contains(filter)) {
                sb.append(d.getCandidate().getId()).append(" | ")
                                .append(d.getSourceLocation()).append(" | ")
                                .append(enc).append(" | ")
                                .append(d.getType()).append(" | ")
                                .append(d.getVariant() != null ? d.getVariant() : "").append(" | ")
                                .append(d.getCandidate().getLiteralText() != null ? d.getCandidate().getLiteralText() : "")
                                .append("\n");
            }
        }
        return sb.toString();
    }

    private static List<InstrumentationDecision> withoutReverted(List<InstrumentationDecision> decisions, Set<InstrumentationDecision> reverted) {
        if (reverted.isEmpty()) {
            return decisions;
        }
        List<InstrumentationDecision> kept = new java.util.ArrayList<>();
        for (InstrumentationDecision d : decisions) {
            if (!reverted.contains(d)) {
                kept.add(d);
            }
        }
        return kept;
    }

    /** The section's no-usage warning count and its filtered warning lines (never a REJECT line). */
    private static void appendNoUsageWarnings(StringBuilder sb, List<String> warnings) {
        sb.append("  no-usage warnings = ").append(warnings.size()).append("\n");
        for (String w : warnings) {
            if (w.contains(SubstrateOptions.StringAnalysisDumpFilter.getValue())) {
                sb.append("  ").append(w).append("\n");
            }
        }
    }

    private static String enclosingClassName(SugVertex v) {
        if (v.getEnclosingMethod() == null) {
            return null;
        }
        return v.getEnclosingMethod().getDeclaringClass().toJavaName(true);
    }
}