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

import org.graalvm.nativeimage.ImageInfo;

import com.oracle.svm.core.AlwaysInline;
import com.oracle.svm.core.jdk.RuntimeSupport;
import com.oracle.svm.core.log.Log;

import jdk.internal.misc.Unsafe;

/**
 * The replacement of a copying indy concat site that an admitted String View reaches. The child lists such a site in
 * the profile ({@code <key> CONCAT_COPY UNARY|BINARY}); the parent replaces exactly that {@code invokedynamic} with a
 * static call of {@link #concat1} (the JDK's {@code StringConcatHelper.newStringOf}: {@code "" + v}) or
 * {@link #concat2} ({@code simpleConcat}: {@code a + b}). Every other concat keeps the stock linkage.
 * <p>
 * Semantics: the JDK's, statement for statement (the same {@code stringOf} conversion, operands in order, the same
 * empty-operand branches, a newly created String every time, JLS 15.18.1), with one difference: the JDK copies the
 * other side of an empty operand with {@code new String(String)}, which reads the null {@code value()} of a
 * value-null rep; here only a plain String takes that constructor and a non-plain one is copied through its own reads
 * ({@link #flat}). The result is always a plain compact String.
 * <p>
 * The emptiness tests are exact-class ({@code s.getClass() == String.class && s.isEmpty()}): no vtable
 * {@code isEmpty}. Reps are never empty, and an empty rep would still be handled: it takes {@link #doConcat} (same
 * content, a fresh String), or as the copied side {@link #flat} (the shared {@code ""}; identity of empty results is
 * out of scope).
 * <p>
 * {@link #doConcat} mirrors {@code StringConcatHelper.doConcat} (same coder and length rule, same
 * {@code OutOfMemoryError} text) so that no rep enters the JDK concat group from here (the kind-terminal concat group
 * lists a kind only from non-copying stock sites). The class is in the rep package, so its call sites ride the stock
 * pipeline (the layer-1 terminal-body scope); it is reachable only from a replaced site.
 * <p>
 * Diagnostic (default off, folded away when off): {@code -J-Dsvm.stringanalysis.repconcat.count=true} makes the
 * replaced sites count their paths and the image print {@code [repconcat-count] ...} at exit.
 */
public final class RepConcat {

    private RepConcat() {
    }

    /** The build-time diagnostic switch (a static final of a build-time initialised class: the branches fold away). */
    public static final boolean COUNT = Boolean.getBoolean("svm.stringanalysis.repconcat.count");

    /* Diagnostic counters (racy increments: a diagnostic, not a measurement of record). */
    static long unaryCount;
    static long binaryEmptyCount;
    static long binaryNonEmptyCount;

    // ---------------------------------------------------------------- UNARY: newStringOf(arg) = new String(stringOf(arg))

    @AlwaysInline("the replaced unary concat is decided inline, as stock inlines newStringOf")
    public static String concat1(String a) {
        return unary(a == null ? "null" : a);
    }

    @AlwaysInline("the replaced unary concat is decided inline, as stock inlines newStringOf")
    public static String concat1(Object a) {
        return unary(stringOf(a));
    }

    // ---------------------------------------------------------------- BINARY: simpleConcat(first, second)

    @AlwaysInline("the replaced binary concat is decided inline, as stock inlines simpleConcat")
    public static String concat2(String a, String b) {
        return binary(a == null ? "null" : a, b == null ? "null" : b);
    }

    @AlwaysInline("the replaced binary concat is decided inline, as stock inlines simpleConcat")
    public static String concat2(String a, Object b) {
        String s1 = a == null ? "null" : a;
        return binary(s1, stringOf(b));
    }

    @AlwaysInline("the replaced binary concat is decided inline, as stock inlines simpleConcat")
    public static String concat2(Object a, String b) {
        String s1 = stringOf(a);
        return binary(s1, b == null ? "null" : b);
    }

    @AlwaysInline("the replaced binary concat is decided inline, as stock inlines simpleConcat")
    public static String concat2(Object a, Object b) {
        String s1 = stringOf(a);
        String s2 = stringOf(b);
        return binary(s1, s2);
    }

    /** The JDK's {@code StringConcatHelper.stringOf(Object)}: a null operand and a null {@code toString()} give "null". */
    static String stringOf(Object value) {
        String s;
        return (value == null || (s = value.toString()) == null) ? "null" : s;
    }

    @AlwaysInline("the body of concat1")
    private static String unary(String s) {
        if (COUNT) {
            unaryCount++;
        }
        return copyOf(s);
    }

    /** {@code simpleConcat}'s branches with exact-class emptiness tests (class comment). */
    @AlwaysInline("the body of concat2 (simpleConcat's branches)")
    private static String binary(String s1, String s2) {
        if (s1.getClass() == String.class && s1.isEmpty()) {
            if (COUNT) {
                binaryEmptyCount++;
            }
            return copyOf(s2); // newly created string required, see JLS 15.18.1
        }
        if (s2.getClass() == String.class && s2.isEmpty()) {
            if (COUNT) {
                binaryEmptyCount++;
            }
            return copyOf(s1); // newly created string required, see JLS 15.18.1
        }
        if (COUNT) {
            binaryNonEmptyCount++;
        }
        return doConcat(s1, s2);
    }

    /** The JDK's {@code new String(s)} for a plain String; a fresh flat copy of a non-plain one ({@link #flat}). */
    @AlwaysInline("the plain case is the JDK's new String(s), inline")
    private static String copyOf(String s) {
        if (s.getClass() == String.class) {
            return new String(s);
        }
        return flat(s);
    }

    /**
     * A fresh plain compact String with the content of the non-plain {@code s} (a view's range copy, else through
     * {@code toCharArray}); never reads {@code value()}. An empty view would give the shared {@code ""}.
     */
    static String flat(String s) {
        if (s instanceof StringView v) {
            return StringView.flatCopy(v);
        }
        return new String(s.toCharArray());
    }

    /**
     * JDK 25 {@code StringConcatHelper.doConcat}: the coder OR, the overflow check, one buffer, the two
     * {@code getBytes(byte[], int, byte)} copies (a rep's own override) and the value-sharing constructor. Outside an
     * image (hosted JUnit, no alias bodies) the same content and errors through public API.
     */
    static String doConcat(String s1, String s2) {
        int len1 = RepParts.lengthOf(s1);
        int len2 = RepParts.lengthOf(s2);
        byte coder = (byte) (s1.coder() | s2.coder());
        int len = checkOverflow(len1 + len2);
        int newLength = len << coder;
        if (newLength < 0) {
            throw new OutOfMemoryError("Overflow: String length out of range");
        }
        if (ImageInfo.inImageRuntimeCode()) {
            // Uninitialized as StringConcatHelper.newArray: the two copies write every byte before publication.
            byte[] buf = (byte[]) Unsafe.getUnsafe().allocateUninitializedArray(byte.class, newLength);
            asTarget(s1).getBytes(buf, 0, coder);
            asTarget(s2).getBytes(buf, len1, coder);
            return (String) (Object) new Target_java_lang_String_StringRep(buf, coder);
        }
        return new StringBuilder(len).append(s1).append(s2).toString();
    }

    private static Target_java_lang_String_StringRep asTarget(String s) {
        return (Target_java_lang_String_StringRep) (Object) s;
    }

    /** {@code StringConcatHelper.checkOverflow(int)}. */
    private static int checkOverflow(int value) {
        if (value >= 0) {
            return value;
        }
        throw new OutOfMemoryError("Overflow: String length out of range");
    }

    // ---------------------------------------------------------------- diagnostic

    /** The exit hook of the diagnostic (registered by the parent only when {@link #COUNT} is on and a site is lowered). */
    public static RuntimeSupport.Hook countHook() {
        return isFirstIsolate -> printCounts();
    }

    static void printCounts() {
        Log.log().string("[repconcat-count] unary=").signed(unaryCount).string(" binaryEmpty=").signed(binaryEmptyCount).string(" binaryNonEmpty=").signed(binaryNonEmptyCount).newline();
    }

    /** Hosted JUnit access to the counters: {unary, binaryEmpty, binaryNonEmpty}. */
    public static long[] counts() {
        return new long[]{unaryCount, binaryEmptyCount, binaryNonEmptyCount};
    }
}
