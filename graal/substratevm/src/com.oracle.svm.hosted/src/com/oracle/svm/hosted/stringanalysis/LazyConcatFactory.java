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

import java.util.Arrays;
import java.util.Objects;

import com.oracle.svm.core.AlwaysInline;
import com.oracle.svm.core.NeverInline;
import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.ThreeWayString;

public final class LazyConcatFactory {

    private LazyConcatFactory() {
    }

    /*
     * The lowering converts every dynamic operand at the site, by its static (MethodType) type, with the converters
     * below (JLS 5.1.11, exactly the StringConcatHelper.stringOf overloads, incl. a null toString() result -> "null"),
     * so the rep factories take Strings.
     */

    /**
     * A 2-part rope with an empty side is the JDK's {@code simpleConcat} empty fast path: a new plain String sharing the
     * other side's bytes (JLS 15.18.1: a newly created String; identity is observable). Only when that side is a plain
     * String ({@code new String(s)} reads {@code s.value}, null for a rep or a view); otherwise the rope. A plain String
     * is a valid value of every lazy site: the IC rep guards are exact-class tests. The replacement uses
     * {@link #ropeInlinePrologue}, which has the same semantics.
     */
    public static String rope(String a, String b) {
        if (a.getClass() == String.class && a.isEmpty() && b.getClass() == String.class) {
            return new String(b);
        }
        if (b.getClass() == String.class && b.isEmpty() && a.getClass() == String.class) {
            return new String(a);
        }
        return RopeString.create(a, b);
    }

    /**
     * The ROPE factory ({@link LazyConcatMint#factoryMethod}): {@link #rope} split in two. The empty-operand
     * fast cases are force-inlined into the replaced site, as stock inlines the whole concat; the rope construction
     * {@link #ropeOutOfLine} stays out of line. Same semantics as {@link #rope}, statement for statement. Only a replaced
     * LC site calls it (no JDK code gains an annotation).
     */
    @AlwaysInline("the empty-operand prologue of the replaced 2-part concat is decided inline, as stock inlines the concat")
    public static String ropeInlinePrologue(String a, String b) {
        if (a.getClass() == String.class && a.isEmpty() && b.getClass() == String.class) {
            return new String(b);
        }
        if (b.getClass() == String.class && b.isEmpty() && a.getClass() == String.class) {
            return new String(a);
        }
        return ropeOutOfLine(a, b);
    }

    /** The rope construction of {@link #ropeInlinePrologue}, kept out of line (one call, as {@link #rope}). */
    @NeverInline("the rope construction of ropeInlinePrologue stays out of line")
    static String ropeOutOfLine(String a, String b) {
        return RopeString.create(a, b);
    }

    /**
     * The factory of a replaced {@code String.concat} site. {@code String.concat} returns the receiver itself when the
     * argument is empty (JDK: {@code if (str.isEmpty()) return this;}), unlike the indy concat; every other case is the
     * 2-part rope: {@link #ropeInlinePrologue}'s body without its second case, which is dead after the identity test.
     * Null checks are emitted by the caller.
     * <p>Every operand emptiness test in this class is
     * {@code x.getClass() == String.class && x.isEmpty()}: the exact-class test narrows {@code x} to {@code String}, so
     * {@code isEmpty()} devirtualizes and inlines as stock ({@code value.length == 0}) instead of a vtable call (hosted
     * factory bodies have no IC entry; every rep overrides {@code isEmpty}). Same result as {@code x.isEmpty()} because a
     * rep instance is never empty (every mint path returns a stock String for an empty result; RepNeverEmptyTest).
     */
    @AlwaysInline("String.concat's empty-argument identity is decided inline")
    public static String stringConcat(String a, String b) {
        if (b.getClass() == String.class && b.isEmpty()) {
            return a;
        }
        if (a.getClass() == String.class && a.isEmpty() && b.getClass() == String.class) {
            return new String(b);
        }
        return ropeOutOfLine(a, b);
    }

    public static String threeWay(String a, String b, String c) {
        return ThreeWayString.create(a, b, c);
    }

    public static String fixed4(String a, String b, String c, String d) {
        return FixedConcat4.create(a, b, c, d);
    }

    /** {@code parts} is the lowering's fresh array (no other reference): handed over, no copy. */
    public static String arrayLazy(String[] parts) {
        return ArrayLazyString.createOwned(parts);
    }

    /** {@code parts} is the lowering's fresh array (no other reference): handed over, no copy. */
    public static String interleaved(String[] parts, String delimiter) {
        return InterleavedStringArray.createOwned(parts, parts.length, delimiter);
    }

    /** A String operand: {@code null -> "null"}, otherwise the operand itself (its own type state). */
    public static String str(String s) {
        return s == null ? "null" : s;
    }

    /**
     * The JDK's {@code StringConcatHelper.stringOf(Object)}, not {@code String.valueOf}: a null operand and a
     * {@code toString()} that returns null both give "null" (the rep factories never see a null part).
     * {@code toString()} is called exactly once.
     */
    public static String str(Object o) {
        String s;
        return (o == null || (s = o.toString()) == null) ? "null" : s;
    }

    /** byte/short/int (byte and short widen to int on the operand stack). */
    public static String str(int i) {
        return Integer.toString(i);
    }

    public static String str(long l) {
        return Long.toString(l);
    }

    public static String str(char c) {
        return String.valueOf(c);
    }

    public static String str(boolean z) {
        return z ? "true" : "false";
    }

    public static String str(float f) {
        return Float.toString(f);
    }

    public static String str(double d) {
        return Double.toString(d);
    }

    /**
     * The replacement of {@code String.join(CharSequence, CharSequence...)}: the JDK 25 body step by step
     * ({@code delimiter.toString()}, a fresh {@code String[]} of {@code String.valueOf(element)}), so the same exceptions
     * in the same order and the same snapshot (a later mutation of a CharSequence argument is not seen). The fresh array
     * is handed to the result without a copy.
     */
    public static String join(CharSequence delimiter, CharSequence[] elements) {
        String delim = delimiter.toString();
        String[] elems = new String[elements.length];
        for (int i = 0; i < elements.length; i++) {
            elems[i] = String.valueOf(elements[i]);
        }
        return InterleavedStringArray.createOwned(elems, elems.length, delim);
    }

    /**
     * The replacement of {@code String.join(CharSequence, Iterable)}: the JDK 25 body (the two
     * {@code requireNonNull}s, {@code delimiter.toString()}, one pass of the iterator into a growing {@code String[]} of
     * {@code String.valueOf(element)}). The growth array is handed over with its count (no trimming copy).
     *
     * <p>Retention: unlike the JDK result, the result keeps every part String alive plus this array (up to 2x
     * {@code size} slots), which for long joins of short parts can exceed the flat result.
     */
    public static String join(CharSequence delimiter, Iterable<? extends CharSequence> elements) {
        Objects.requireNonNull(delimiter);
        Objects.requireNonNull(elements);
        String delim = delimiter.toString();
        String[] elems = new String[8];
        int size = 0;
        for (CharSequence cs : elements) {
            if (size >= elems.length) {
                elems = Arrays.copyOf(elems, elems.length << 1);
            }
            elems[size++] = String.valueOf(cs);
        }
        return InterleavedStringArray.createOwned(elems, size, delim);
    }
}