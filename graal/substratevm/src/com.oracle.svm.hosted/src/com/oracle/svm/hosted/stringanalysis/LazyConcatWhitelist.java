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

public final class LazyConcatWhitelist {

    /** The protected whole-string copy {@code getBytes(byte[],int,byte)}: overridden by every lazy rep. */
    static final String PROTECTED_GETBYTES_SIG = "[B,I,B";

    /**
     * W_lazy by name and parameter signature ({@code SiteKeys.formatSignature} format), restricted to the overloads
     * every lazy representation overrides (RopeString, ThreeWayString, FixedConcat4, ArrayLazyString,
     * InterleavedStringArray all declare {@code length()}, {@code isEmpty()}, {@code charAt(int)}, {@code equals(Object)},
     * {@code toCharArray()}, {@code hashCode()}, {@code coder()}, {@code getChars(int,int,char[],int)} and the four
     * public {@code getBytes} overloads). The protected copies {@code getBytes(byte[],int,byte)} and
     * {@code getBytes(byte[],int,int,byte,int)} (through which {@code AbstractStringBuilder.appendChars(..., String, ...)}
     * and {@code putStringAt} copy instead of reading {@code value()}) are overridden by every lazy rep too, so they are
     * plain rows. A {@code null} signature is the empty one. Constructors are internal calls and reach this table only as
     * enclosing methods.
     */
    static final java.util.Map<String, Set<String>> SIGNATURES = java.util.Map.of(
                    "length", Set.of(""),
                    "isEmpty", Set.of(""),
                    "charAt", Set.of("I"),
                    "equals", Set.of("Ljava/lang/Object;"),
                    "toCharArray", Set.of(""),
                    "hashCode", Set.of(""),
                    "coder", Set.of(""),
                    "getChars", Set.of("I,I,[C,I"),
                    "getBytes", Set.of("", "Ljava/lang/String;", "Ljava/nio/charset/Charset;", "I,I,[B,I", PROTECTED_GETBYTES_SIG, "[B,I,I,B,I"));

    /**
     * String map keys: {@code compareTo(String)} and the {@code Comparable} bridge
     * {@code compareTo(Object)} as a lazy rep's receiver usage. Every lazy rep overrides
     * {@code compareTo(String)} ({@code RepCompareTo}; the inherited body would read {@code value()}, null for a lazy
     * rep), so rep-aware comparisons exist at run time.
     */
    static final Set<String> COMPARE_TO_SIGS = Set.of("Ljava/lang/String;", "Ljava/lang/Object;");

    /** The variant-free form (every row holds for every lazy variant). */
    static boolean isWhitelisted(String methodName, String declaringClass, String signature) {
        return isWhitelisted(methodName, declaringClass, signature, "ROPE");
    }

    /**
     * Per-variant form; {@code variant} is the candidate's lazy variant ({@code null} = not yet known). No row currently
     * depends on the variant.
     */
    static boolean isWhitelisted(String methodName, String declaringClass, String signature, String variant) {
        if (declaringClass == null || !declaringClass.equals("java.lang.String")) {
            return false;
        }
        // No String constructor row: every caller tests isInternalCall first, and isWhitelistedMethod refuses <init>.
        if (SugNameTables.RAW_CODER_USAGE.equals(methodName)) {
            // A raw read of a lazy rep's inherited coder field. Every lazy rep sets it through super(coder) to
            // exactly its own coder() answer (RopeString.java:67 vs :80,
            // ThreeWayString.java:58 vs :72, FixedConcat4.java:59 vs :74 — the OR of final children's coders;
            // ArrayLazyString.java:55 vs :70/:91, InterleavedStringArray.java:54 vs :74/:95 — the same OR over the
            // parts), and coder() is whitelisted. value(raw) is never whitelisted: every lazy rep's value is null.
            return true;
        }
        String sig = signature == null ? "" : signature;
        Set<String> sigs = SIGNATURES.get(methodName);
        if (sigs != null && sigs.contains(sig)) {
            return true;
        }
        if ("compareTo".equals(methodName) && COMPARE_TO_SIGS.contains(sig)) {
            // The lazy receiver rule: sound only with the reps' own compareTo overrides (without them the image throws
            // at a lazy rep's compareTo)
            return true;
        }
        return false;
    }

    static boolean isWhitelistedMethod(com.oracle.graal.pointsto.meta.AnalysisMethod method) {
        return isWhitelistedMethod(method, "ROPE");
    }

    /** The per-variant form (see {@link #isWhitelisted(String, String, String, String)}). */
    static boolean isWhitelistedMethod(com.oracle.graal.pointsto.meta.AnalysisMethod method, String variant) {
        if (method == null) {
            return false;
        }
        if ("<init>".equals(method.getName())) {
            // No String constructor is an exempt enclosing method. A candidate is never the receiver of a String
            // constructor; it reaches one only as the argument of String(String), whose body reads original.value()
            // (null for every lazy rep), and that usage is validated like any other (value() is not whitelisted).
            return false;
        }
        String declaringClass = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        String signature = SiteKeys.formatSignature(method);
        return isWhitelisted(name, declaringClass, signature, variant);
    }

    private static boolean sigIs(String sig, String... options) {
        if (sig == null) {
            return false;
        }
        for (String opt : options) {
            if (sig.equals(opt)) {
                return true;
            }
        }
        return false;
    }
}
