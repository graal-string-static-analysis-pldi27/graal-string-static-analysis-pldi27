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

public final class ProfileEntry {

    private final String sourceLocation;
    private final OptimizationType type;
    private final String variant;
    /**
     * Unified accumulator lowering: at a {@code STRING_VIEW ACCUMULATOR_VIEW} entry, the exact class of every receiver of the
     * extraction (the child's receiver proof: all receivers are born at {@code new <class>} allocations of pass-1
     * accumulators), written as the line's fourth token; null elsewhere. The parent lowers on it alone.
     */
    private final String accumulatorClass;

    public ProfileEntry(String sourceLocation, OptimizationType type, String variant) {
        this(sourceLocation, type, variant, null);
    }

    public ProfileEntry(String sourceLocation, OptimizationType type, String variant, String accumulatorClass) {
        this.sourceLocation = sourceLocation;
        this.type = type;
        this.variant = variant;
        this.accumulatorClass = accumulatorClass;
    }

    public String getSourceLocation() {
        return sourceLocation;
    }

    public OptimizationType getType() {
        return type;
    }

    public String getVariant() {
        return variant;
    }

    public String getAccumulatorClass() {
        return accumulatorClass;
    }

    @Override
    public String toString() {
        return sourceLocation + " " + type + (variant != null ? " " + variant : "") + (accumulatorClass != null ? " " + accumulatorClass : "");
    }
}