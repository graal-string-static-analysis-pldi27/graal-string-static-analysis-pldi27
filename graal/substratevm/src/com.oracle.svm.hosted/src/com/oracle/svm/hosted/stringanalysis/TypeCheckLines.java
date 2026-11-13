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
import java.util.List;

/**
 * Type-check IC: the {@code TYPE_CHECK} line format and the knob, shared by the child ({@link TypeCheckSites}) and the
 * parent (the loader, {@link TypeCheckIcNodePlugin}). Kept free of child-only classes.
 */
final class TypeCheckLines {

    /** {@code svm.stringanalysis.typecheck.ic}: 0 = stock (no observation, line or lowering); 1 = on (default); 2 = CHECK. */
    static final int MODE = Integer.getInteger("svm.stringanalysis.typecheck.ic", 1);
    static final String LINE_TYPE = "TYPE_CHECK";
    static final String CAST = "CAST";
    static final String INST = "INST";
    /** = {@code InlineCacheProfilingHeuristic.UNPROVEN} (the IC's no-proof variant). */
    static final String UNPROVEN = "UNPROVEN";

    private TypeCheckLines() {
    }

    /** The rep names of a variant (KT marker stripped; empty for UNKNOWN/EXACT_STRING; null for UNPROVEN or malformed). */
    static List<String> repNames(String variant) {
        String v = TerminalBodyKinds.stripMarker(variant);
        if (v == null) {
            v = variant;
        }
        if (v == null || v.isEmpty() || UNPROVEN.equals(v)) {
            return null;
        }
        if (v.equals("UNKNOWN") || v.equals("EXACT_STRING")) {
            return List.of();
        }
        List<String> out = new ArrayList<>();
        for (String r : v.split(",")) {
            if (r.isEmpty()) {
                return null;
            }
            if (!r.equals("EXACT") && !out.contains(r)) {
                out.add(r);
            }
        }
        return out;
    }

    /** The profile line's shape: {@code <key> TYPE_CHECK CAST|INST <variant>} (pure; the loader's check). */
    static boolean isLine(String[] parts) {
        if (parts.length != 4 || !LINE_TYPE.equals(parts[1]) || parts[0].indexOf('@') <= 0 || parts[0].indexOf('#') <= 0 || !(CAST.equals(parts[2]) || INST.equals(parts[2]))) {
            return false;
        }
        String unmarked = TerminalBodyKinds.stripMarker(parts[3]);
        return UNPROVEN.equals(unmarked != null ? unmarked : parts[3]) || repNames(parts[3]) != null;
    }
}
