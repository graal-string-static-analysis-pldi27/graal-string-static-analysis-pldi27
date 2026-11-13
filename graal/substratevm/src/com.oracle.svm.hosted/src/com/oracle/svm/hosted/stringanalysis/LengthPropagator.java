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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.oracle.graal.pointsto.meta.AnalysisMethod;

public final class LengthPropagator {

    private static final Set<String> LENGTH_PRESERVING_METHODS = Set.of("toUpperCase", "toLowerCase");

    private final StringUtilizationGraph sug;
    private final Map<AnalysisMethod, List<CapturedSite>> captured;
    private final Map<SugVertex, Integer> lengthOf = new HashMap<>();
    private final Set<SugVertex> conflicted = new HashSet<>();

    private int e1Count;
    private int e2Count;
    private int e3Count;
    private int e4Count;
    private int conflictCount;

    public LengthPropagator(StringUtilizationGraph sug) {
        this(sug, Collections.emptyMap());
    }

    public LengthPropagator(StringUtilizationGraph sug, Map<AnalysisMethod, List<CapturedSite>> captured) {
        this.sug = sug;
        this.captured = captured != null ? captured : Collections.emptyMap();
    }

    public void propagate() {
        applyE1();
        applyE2();
        applyE3();
        applyE4();
        writeBack();
        applyConstRange();
    }

    public int getE1Count() {
        return e1Count;
    }

    public int getE2Count() {
        return e2Count;
    }

    public int getE3Count() {
        return e3Count;
    }

    public int getE4Count() {
        return e4Count;
    }

    public int getConflictCount() {
        return conflictCount;
    }

    public int getAssignedCount() {
        return lengthOf.size();
    }

    private void applyE1() {
        for (SugVertex v : sug.getVertices()) {
            if (v.getNodeType() == SugNodeType.STRING_LITERAL && v.getLiteralText() != null) {
                int len = v.getLiteralText().length();
                v.setLength(len);
                lengthOf.put(v, len);
                e1Count++;
            }
        }
    }

    private void applyE2() {
        for (SugVertex v : sug.getVertices()) {
            if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL) {
                continue;
            }
            if ("substring".equals(v.getMethodName())) {
                Long i = getConstantParam(v, 0);
                Long j = getConstantParam(v, 1);
                if (i == null || j == null) {
                    continue;
                }
                int len = (int) (j - i);
                if (len < 0) {
                    continue;
                }
                if (assign(v, len)) {
                    e2Count++;
                }
            } else if ("valueOf".equals(v.getMethodName()) &&
                            ("char".equals(v.getMethodSignature()) || "C".equals(v.getMethodSignature()))) {
                if (assign(v, 1)) {
                    e2Count++;
                }
            }
        }
    }

    private void applyE3() {
        for (Map.Entry<AnalysisMethod, List<CapturedSite>> entry : captured.entrySet()) {
            AnalysisMethod enclosing = entry.getKey();
            String keyPrefix = enclosing.getDeclaringClass().toJavaName(true) + "#" + enclosing.getName() +
                            enclosing.getSignature().toMethodDescriptor() + "@";
            for (CapturedSite site : entry.getValue()) {
                if (!(site instanceof SubstringArithSite sas) || !sas.unitRange()) {
                    continue;
                }
                String siteKey = keyPrefix + sas.bci();
                assignUnitRange(siteKey, sas.sourceLocation());
            }
        }
    }

    /**
     * Marks each substring/subSequence vertex whose captured range length is a constant
     * ({@link SubstringArithSite#constRange}): a fact for the String View rule only; it assigns no length.
     */
    private void applyConstRange() {
        for (Map.Entry<AnalysisMethod, List<CapturedSite>> entry : captured.entrySet()) {
            AnalysisMethod enclosing = entry.getKey();
            String keyPrefix = enclosing.getDeclaringClass().toJavaName(true) + "#" + enclosing.getName() +
                            enclosing.getSignature().toMethodDescriptor() + "@";
            for (CapturedSite site : entry.getValue()) {
                if (!(site instanceof SubstringArithSite sas) || sas.constRange() < 0) {
                    continue;
                }
                SugVertex match = matchSubstringVertex(keyPrefix + sas.bci(), sas.sourceLocation(), sas.name());
                if (match != null) {
                    match.setConstRangeLength(sas.constRange());
                }
            }
        }
    }

    boolean assignUnitRange(String sourceKey, String sourceLocation) {
        SugVertex match = matchSubstringVertex(sourceKey, sourceLocation, "substring");
        if (match != null && assign(match, 1)) {
            e3Count++;
            return true;
        }
        return false;
    }

    private SugVertex matchSubstringVertex(String sourceKey, String sourceLocation, String methodName) {
        if (sourceKey != null) {
            SugVertex match = null;
            int count = 0;
            for (SugVertex v : sug.getVertices()) {
                if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL) {
                    continue;
                }
                if (!methodName.equals(v.getMethodName())) {
                    continue;
                }
                if (sourceKey.equals(v.getSourceKey())) {
                    match = v;
                    count++;
                }
            }
            if (count == 1) {
                return match;
            }
        }
        if (sourceLocation != null) {
            SugVertex match = null;
            int count = 0;
            for (SugVertex v : sug.getVertices()) {
                if (v.getNodeType() != SugNodeType.STRING_METHOD_CALL) {
                    continue;
                }
                if (!methodName.equals(v.getMethodName())) {
                    continue;
                }
                if (sourceLocation.equals(v.getSourceLocation())) {
                    match = v;
                    count++;
                }
            }
            if (count == 1) {
                return match;
            }
        }
        return null;
    }

    private void applyE4() {
        Deque<SugVertex> worklist = new ArrayDeque<>(lengthOf.keySet());
        Set<SugVertex> inWorklist = new HashSet<>(lengthOf.keySet());
        while (!worklist.isEmpty()) {
            SugVertex v = worklist.removeFirst();
            inWorklist.remove(v);
            Integer lenObj = lengthOf.get(v);
            if (lenObj == null) {
                continue;
            }
            int n = lenObj;
            for (SugEdge e : v.getOutEdges()) {
                if (e.getEdgeType() == SugEdgeType.PARAMETER) {
                    continue;
                }
                SugVertex to = e.getTo();
                if (conflicted.contains(to)) {
                    continue;
                }
                if (!canPropagateTo(to)) {
                    continue;
                }
                if (!lengthOf.containsKey(to)) {
                    lengthOf.put(to, n);
                    e4Count++;
                    if (!inWorklist.contains(to)) {
                        worklist.add(to);
                        inWorklist.add(to);
                    }
                } else if (lengthOf.get(to) != n) {
                    conflicted.add(to);
                    lengthOf.remove(to);
                    conflictCount++;
                    cascadeConflict(to);
                }
            }
        }
    }

    private void cascadeConflict(SugVertex conflictedVertex) {
        Deque<SugVertex> work = new ArrayDeque<>();
        work.add(conflictedVertex);
        while (!work.isEmpty()) {
            SugVertex cur = work.removeFirst();
            for (SugEdge e : cur.getOutEdges()) {
                if (e.getEdgeType() == SugEdgeType.PARAMETER) {
                    continue;
                }
                if (e.getEdgeType() == SugEdgeType.QUALIFIER &&
                                (e.getTo().getNodeType() == SugNodeType.STRING_METHOD_CALL ||
                                                e.getTo().getNodeType() == SugNodeType.JDK_LIBRARY_CALL)) {
                    continue;
                }
                if (e.getEdgeType() == SugEdgeType.DATAFLOW &&
                                (e.getTo().getNodeType() == SugNodeType.STRING_METHOD_CALL ||
                                                e.getTo().getNodeType() == SugNodeType.JDK_LIBRARY_CALL)) {
                    continue;
                }
                SugVertex downstream = e.getTo();
                if (conflicted.add(downstream)) {
                    lengthOf.remove(downstream);
                    work.add(downstream);
                }
            }
        }
    }

    private boolean canPropagateTo(SugVertex target) {
        if (target.getNodeType() == SugNodeType.CONCAT_EXPRESSION) {
            return false;
        }
        if (target.getNodeType() == SugNodeType.STRING_METHOD_CALL) {
            return LENGTH_PRESERVING_METHODS.contains(target.getMethodName());
        }
        if (target.getNodeType() == SugNodeType.CONSTANT_ARG) {
            return false;
        }
        return true;
    }

    private boolean assign(SugVertex v, int n) {
        if (conflicted.contains(v)) {
            return false;
        }
        Integer existing = lengthOf.get(v);
        if (existing == null) {
            lengthOf.put(v, n);
            return true;
        } else if (existing != n) {
            conflicted.add(v);
            lengthOf.remove(v);
            conflictCount++;
            return false;
        }
        return false;
    }

    private void writeBack() {
        for (SugVertex v : sug.getVertices()) {
            if (conflicted.contains(v)) {
                v.setLength(SugVertex.UNKNOWN_LENGTH);
            } else if (lengthOf.containsKey(v)) {
                v.setLength(lengthOf.get(v));
            }
        }
    }

    private Long getConstantParam(SugVertex callVertex, int paramIndex) {
        for (SugEdge e : callVertex.getInEdges()) {
            if (e.getEdgeType() != SugEdgeType.PARAMETER) {
                continue;
            }
            if (e.getParamIndex() != paramIndex) {
                continue;
            }
            SugVertex from = e.getFrom();
            if (from.getNodeType() == SugNodeType.CONSTANT_ARG) {
                return from.getConstantValue();
            }
        }
        return null;
    }
}
