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

public final class InstrumentationDecision {

    private final SugVertex candidate;
    private final OptimizationType type;
    private final String variant;
    private final String sourceLocation;
    /** Unified accumulator lowering: the exact accumulator class of an ACCUMULATOR_VIEW extraction (see ProfileEntry). */
    private final String accumulatorClass;

    public InstrumentationDecision(SugVertex candidate, OptimizationType type, String variant) {
        this(candidate, type, variant, null);
    }

    public InstrumentationDecision(SugVertex candidate, OptimizationType type, String variant, String accumulatorClass) {
        this.candidate = candidate;
        this.type = type;
        this.variant = variant;
        this.sourceLocation = candidate.getSourceLocation();
        this.accumulatorClass = accumulatorClass;
    }

    public SugVertex getCandidate() {
        return candidate;
    }

    public OptimizationType getType() {
        return type;
    }

    public String getVariant() {
        return variant;
    }

    public String getSourceLocation() {
        return sourceLocation;
    }

    public String getAccumulatorClass() {
        return accumulatorClass;
    }

    public String describe() {
        StringBuilder sb = new StringBuilder();
        sb.append(type);
        if (variant != null) {
            sb.append("[").append(variant).append("]");
        }
        sb.append("  V").append(candidate.getId()).append("  @ ").append(sourceLocation);
        if (candidate.getLiteralText() != null) {
            sb.append("  text=\"").append(escape(candidate.getLiteralText())).append("\"");
        }
        if (candidate.getMethodName() != null) {
            sb.append("  ").append(candidate.getMethodName());
        }
        if (candidate.getLength() != SugVertex.UNKNOWN_LENGTH) {
            sb.append("  len=").append(candidate.getLength());
        }
        return sb.toString();
    }

    private static String escape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                case '"' -> sb.append("\\\"");
                default -> sb.append(c);
            }
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return describe();
    }
}
