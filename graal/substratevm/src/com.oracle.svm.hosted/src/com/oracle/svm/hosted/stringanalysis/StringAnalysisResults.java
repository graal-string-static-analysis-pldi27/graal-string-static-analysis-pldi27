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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Build-time singleton holding the validated string utilization decisions produced by the
 * {@code HeuristicOrchestrator}, indexed by vertex id and source location for downstream
 * (compiler-integration) queries. Set by {@code StringAnalysisFeature} after analysis and
 * accessible at run time via {@link #getInstance()}.
 */
public final class StringAnalysisResults {

    private static volatile StringAnalysisResults instance;

    private final List<InstrumentationDecision> decisions;
    private final Map<Integer, InstrumentationDecision> byVertexId;
    private final Map<String, List<InstrumentationDecision>> bySourceLocation;

    private final int rawCandidateCount;
    private final int validatedCount;
    private final int conflictCount;
    private final int precedenceSuppressedCount;

    public StringAnalysisResults(List<InstrumentationDecision> decisions,
                    int rawCandidateCount,
                    int validatedCount,
                    int conflictCount,
                    int precedenceSuppressedCount) {
        this.decisions = Collections.unmodifiableList(new ArrayList<>(decisions));
        this.byVertexId = new LinkedHashMap<>();
        this.bySourceLocation = new LinkedHashMap<>();
        for (InstrumentationDecision d : decisions) {
            byVertexId.put(d.getCandidate().getId(), d);
            bySourceLocation.computeIfAbsent(d.getSourceLocation(), k -> new ArrayList<>()).add(d);
        }
        this.rawCandidateCount = rawCandidateCount;
        this.validatedCount = validatedCount;
        this.conflictCount = conflictCount;
        this.precedenceSuppressedCount = precedenceSuppressedCount;
    }

    public List<InstrumentationDecision> getDecisions() {
        return decisions;
    }

    public InstrumentationDecision getDecision(int vertexId) {
        return byVertexId.get(vertexId);
    }

    public List<InstrumentationDecision> getDecisionsBySource(String sourceLocation) {
        return bySourceLocation.getOrDefault(sourceLocation, Collections.emptyList());
    }

    public InstrumentationDecision getFirstDecisionBySource(String sourceLocation) {
        List<InstrumentationDecision> list = bySourceLocation.get(sourceLocation);
        return (list != null && !list.isEmpty()) ? list.get(0) : null;
    }

    public boolean hasDecisions() {
        return !decisions.isEmpty();
    }

    public int getValidatedCount() {
        return validatedCount;
    }

    public int getRawCandidateCount() {
        return rawCandidateCount;
    }

    /**
     * The number of lines in the orchestrator's conflicts list ("conflicts rejected" in the report): one per reverted or
     * suppressed decision, never one per site.
     */
    public int getConflictCount() {
        return conflictCount;
    }

    public int getPrecedenceSuppressedCount() {
        return precedenceSuppressedCount;
    }

    public static void setInstance(StringAnalysisResults results) {
        instance = results;
    }

    public static void clearInstance() {
        instance = null;
    }

    public static StringAnalysisResults getInstance() {
        return instance;
    }
}
