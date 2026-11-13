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
import java.util.Map;

import com.oracle.graal.pointsto.meta.AnalysisMethod;

final class ReceiverCorrelation {

    private ReceiverCorrelation() {
    }

    static SugVertex correlateReceiverByKey(StringUtilizationGraph graph, String receiverSourceKey,
                    String receiverLocation, AnalysisMethod enclosing) {
        if (receiverSourceKey != null) {
            SugVertex accumulatorMatch = null;
            int accumulatorMatches = 0;
            SugVertex flowMatch = null;
            int flowMatches = 0;
            for (SugVertex v : graph.getVertices()) {
                if (v == null) {
                    continue;
                }
                if (!receiverSourceKey.equals(v.getSourceKey())) {
                    continue;
                }
                SugNodeType t = v.getNodeType();
                if (t == SugNodeType.NEW_ACCUMULATOR) {
                    accumulatorMatch = v;
                    accumulatorMatches++;
                } else if ((t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE) && isAccumulatorJavaType(v)) {
                    flowMatch = v;
                    flowMatches++;
                }
            }
            if (accumulatorMatches == 1) {
                return accumulatorMatch;
            }
            if (flowMatches == 1) {
                return flowMatch;
            }
        }
        if (receiverLocation == null) {
            return null;
        }
        SugVertex accumulatorMatch = null;
        int accumulatorMatches = 0;
        SugVertex flowMatch = null;
        int flowMatches = 0;
        for (SugVertex v : graph.getVertices()) {
            if (v == null || v.getEnclosingMethod() != enclosing) {
                continue;
            }
            if (!receiverLocation.equals(v.getSourceLocation())) {
                continue;
            }
            SugNodeType t = v.getNodeType();
            if (t == SugNodeType.NEW_ACCUMULATOR) {
                accumulatorMatch = v;
                accumulatorMatches++;
            } else if ((t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE) && isAccumulatorJavaType(v)) {
                flowMatch = v;
                flowMatches++;
            }
        }
        if (accumulatorMatches == 1) {
            return accumulatorMatch;
        }
        if (flowMatches == 1) {
            return flowMatch;
        }
        return null;
    }

    static SugVertex correlateReceiverByKey(String receiverSourceKey,
                    String receiverLocation, AnalysisMethod enclosing,
                    Map<String, List<SugVertex>> verticesBySourceKey,
                    Map<AnalysisMethod, Map<String, List<SugVertex>>> verticesByEnclosingAndSource) {
        if (receiverSourceKey != null) {
            SugVertex accumulatorMatch = null;
            int accumulatorMatches = 0;
            SugVertex flowMatch = null;
            int flowMatches = 0;
            List<SugVertex> candidates = verticesBySourceKey.get(receiverSourceKey);
            if (candidates != null) {
                for (SugVertex v : candidates) {
                    SugNodeType t = v.getNodeType();
                    if (t == SugNodeType.NEW_ACCUMULATOR) {
                        accumulatorMatch = v;
                        accumulatorMatches++;
                    } else if ((t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE) && isAccumulatorJavaType(v)) {
                        flowMatch = v;
                        flowMatches++;
                    }
                }
            }
            if (accumulatorMatches == 1) {
                return accumulatorMatch;
            }
            if (flowMatches == 1) {
                return flowMatch;
            }
        }
        if (receiverLocation == null) {
            return null;
        }
        SugVertex accumulatorMatch = null;
        int accumulatorMatches = 0;
        SugVertex flowMatch = null;
        int flowMatches = 0;
        Map<String, List<SugVertex>> bySource = verticesByEnclosingAndSource.get(enclosing);
        if (bySource != null) {
            List<SugVertex> candidates = bySource.get(receiverLocation);
            if (candidates != null) {
                for (SugVertex v : candidates) {
                    SugNodeType t = v.getNodeType();
                    if (t == SugNodeType.NEW_ACCUMULATOR) {
                        accumulatorMatch = v;
                        accumulatorMatches++;
                    } else if ((t == SugNodeType.FLOW_NODE || t == SugNodeType.VARIABLE) && isAccumulatorJavaType(v)) {
                        flowMatch = v;
                        flowMatches++;
                    }
                }
            }
        }
        if (accumulatorMatches == 1) {
            return accumulatorMatch;
        }
        if (flowMatches == 1) {
            return flowMatch;
        }
        return null;
    }

    private static boolean isAccumulatorJavaType(SugVertex v) {
        if (v.getJavaType() == null) {
            return false;
        }
        return AccumulatorWhitelist.isAccumulatorType(v.getJavaType().toJavaName(true));
    }
}
