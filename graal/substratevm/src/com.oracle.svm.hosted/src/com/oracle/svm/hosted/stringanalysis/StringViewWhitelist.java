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

import java.util.Set;

public final class StringViewWhitelist {

    private static final Set<String> EXACT = Set.of(
                    key("length", ""), key("isEmpty", ""), key("charAt", "I"),
                    key("codePointAt", "I"), key("codePointBefore", "I"),
                    key("codePointCount", "I,I"), key("offsetByCodePoints", "I,I"),
                    key("equals", "Ljava/lang/Object;"),
                    key("contentEquals", "Ljava/lang/StringBuffer;"),
                    key("contentEquals", "Ljava/lang/CharSequence;"),
                    key("hashCode", ""), key("compareTo", "Ljava/lang/String;"),
                    key("trim", ""), key("toCharArray", ""), key("isBlank", ""),
                    key("toUpperCase", ""), key("toUpperCase", "Ljava/util/Locale;"),
                    key("toLowerCase", ""), key("toLowerCase", "Ljava/util/Locale;"),
                    key("strip", ""), key("stripLeading", ""), key("stripTrailing", ""),
                    key("coder", ""), key("toString", ""), key("substring", "I"),
                    key("substring", "I,I"), key("subSequence", "I,I"), key("isLatin1", ""),
                    key("valueOf", "Ljava/lang/Object;"), key("valueOf", "[C"),
                    key("valueOf", "[C,I,I"), key("valueOf", "Z"), key("valueOf", "C"),
                    key("valueOf", "I"), key("valueOf", "J"), key("valueOf", "F"),
                    key("valueOf", "D"), key("getBytes", ""), key("getBytes", "[B,I,B"),
                    // The protected ranged copy (AbstractStringBuilder.appendChars(..., String, ...) /
                    // putStringAt copy through it in the builder JDK); StringView overrides it (offset-aware).
                    key("getBytes", "[B,I,I,B,I"),
                    key("getBytes", "I,I,[B,I"), key("getBytes", "Ljava/nio/charset/Charset;"),
                    key("indexOf", "I"), key("indexOf", "I,I"), key("indexOf", "I,I,I"),
                    key("indexOf", "Ljava/lang/String;"),
                    // JDK 25 String.java:3121-3128 + 3141-3164, read-only (the receiver's and the needle's value/coder,
                    // no store; reached from FloatingDecimal.scanSymbolic under Float/Double.parseX). StringView
                    // overrides it.
                    key("indexOf", "Ljava/lang/String;,I,I"),
                    key("lastIndexOf", "I"),
                    key("lastIndexOf", "I,I"), key("getChars", "I,I,[C,I"),
                    key("repeat", "I"), key("startsWith", "Ljava/lang/String;"),
                    key("endsWith", "Ljava/lang/String;"));

    static boolean isWhitelisted(String methodName, String declaringClass, String signature) {
        if (declaringClass == null || !declaringClass.equals("java.lang.String")) {
            return false;
        }
        if (SugNameTables.RAW_CODER_USAGE.equals(methodName)) {
            // A raw read of StringView's inherited coder field. StringView does not override coder(), so the
            // whitelisted coder() is this read:
            // the field is the parent's coder, set by super(coder) (StringView.java:108 via String(byte),
            // String.java:5278), and matches the backing array's encoding. value(raw) is never whitelisted:
            // StringView's value is null (the same constructor).
            return true;
        }
        return EXACT.contains(key(methodName, signature));
    }

    /**
     * The verdict-layer form of {@link #isWhitelisted}: W_view plus the compiler bridge {@code compareTo(Object)} of
     * {@code Comparable<String>}, which only casts and calls the virtual {@code compareTo(String)}, which StringView
     * overrides (recorded as a resolved-target usage: sorting, TreeMap/TreeSet keys). Phase-A site creation keeps using
     * {@link #isWhitelisted}.
     */
    static boolean isWhitelistedUsage(String methodName, String declaringClass, String signature) {
        if ("compareTo".equals(methodName) && "java.lang.String".equals(declaringClass) && "Ljava/lang/Object;".equals(signature)) {
            return true;
        }
        return isWhitelisted(methodName, declaringClass, signature);
    }

    static Set<String> acceptedSignatures() {
        return EXACT;
    }

    private static String key(String name, String signature) {
        return name + "(" + signature + ")";
    }

}
