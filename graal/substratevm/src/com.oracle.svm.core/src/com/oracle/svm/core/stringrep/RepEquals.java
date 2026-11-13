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
package com.oracle.svm.core.stringrep;

/**
 * The shared total content comparison behind every rep's {@code equals} slow path. Each rep's {@code equals} (Java
 * body and parent-side intrinsic) keeps its own fast paths (a same-coder plain {@code String}, a same-shape rep of its
 * class); every other argument ends here instead of in a {@code return false}, which would be wrong for two
 * content-equal strings of different representations (and would need a cross-rep conflict pass that treats every
 * rep pair as a conflict as a guard).
 *
 * <p>The body reads only {@code length()} and {@code charAt(int)}, which every rep implements correctly, so it is
 * exact for every combination ({@code String.equals} is "the same sequence of chars"). It never calls {@code equals},
 * so it cannot recurse into an equals intrinsic.
 */
final class RepEquals {

    private RepEquals() {
    }

    /** {@code a.equals(b)} by content, for two non-null strings of any representation. */
    static boolean contentEquals(String a, String b) {
        int n = a.length();
        if (b.length() != n) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            if (a.charAt(i) != b.charAt(i)) {
                return false;
            }
        }
        return true;
    }
}
