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

import org.junit.Assert;

/**
 * Content equality of a JDK String and a representation as the native image computes it. The builder JDK's
 * {@code String.equals} is the stock body (no {@code getClass()} deflection), so {@code jdk.equals(rep)}
 * with a value-null rep argument is not a valid question on HotSpot either (the image answers it only at an
 * {@code EQUALS_MATRIX REDIRECT} site, through the mirror). The tests ask the mirror the image uses there:
 * {@code String.objectMaybeCustomStringEquals(expected, actual)}.
 */
final class RepEq {

    private RepEq() {
    }

    static boolean eq(Object expected, Object actual) {
        if (expected == null || actual == null) {
            return expected == actual;
        }
        return String.objectMaybeCustomStringEquals(expected, actual);
    }

    static void assertRepEquals(String message, Object expected, Object actual) {
        if (!eq(expected, actual)) {
            Assert.fail((message == null ? "" : message + " ") + "expected:<" + expected + "> but was:<" + actual + ">");
        }
    }

    static void assertRepEquals(Object expected, Object actual) {
        assertRepEquals(null, expected, actual);
    }

    /** Element-wise {@link #eq} of two lists (a JDK {@code List.equals} asks {@code expected.get(i).equals(actual.get(i))}). */
    static void assertRepListEquals(String message, java.util.List<?> expected, java.util.List<?> actual) {
        boolean ok = expected.size() == actual.size();
        for (int i = 0; ok && i < expected.size(); i++) {
            ok = eq(expected.get(i), actual.get(i));
        }
        if (!ok) {
            Assert.fail(message + " expected:<" + expected + "> but was:<" + actual + ">");
        }
    }
}
