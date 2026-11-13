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

sealed interface CapturedSite permits ConcatSite, ConcatMethodSite, AccumulatorOpSite, SubstringArithSite {
    int bci();
}

record ConcatSite(int bci, String bootstrapName, String sourceLocation, int dynamicOperandCount, int totalOperandCount,
                List<OperandRef> operands, List<String> constantOperands, String recipe, String operandKinds) implements CapturedSite {
    // operandKinds = one char per dynamic operand by its static (indy MethodType) type: S String,
    // P primitive, B final box type (Integer/Long/Boolean/Character/Byte/Short/Float/Double), O any other reference;
    // null when the MethodType is unavailable.
}

/**
 * A captured {@code String.concat(String)} call site: both receiver and argument are dynamic operands
 * ({@code operands} = {@code [receiverRef, argRef]}), with no recipe. Distinct from {@link ConcatSite} so the SUG
 * builder can tell a method-call concat (source flow an {@code InvokeTypeFlow}) from an indy concat.
 */
record ConcatMethodSite(int bci, String sourceLocation, List<OperandRef> operands) implements CapturedSite {
}

record OperandRef(String sourceLocation, int operandBci) {
}

record AccumulatorOpSite(int bci, String targetQualified, String sourceLocation, int argCount,
                String receiverLocation, String receiverSourceKey) implements CapturedSite {
}

/** {@code constRange}: the constant range length ({@code StringAnalysisCapturePlugin.constRangeLength}) or -1. */
record SubstringArithSite(int bci, String name, String sourceLocation, boolean unitRange, int constRange) implements CapturedSite {
}
