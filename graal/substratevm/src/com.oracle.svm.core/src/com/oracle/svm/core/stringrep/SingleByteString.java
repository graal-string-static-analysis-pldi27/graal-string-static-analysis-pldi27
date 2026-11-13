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

import java.util.Locale;

import org.graalvm.nativeimage.ImageInfo;

/**
 * Single Byte representation: a flat {@code String} subclass for one Latin-1 char. The inherited {@code value}/
 * {@code coder} are set by {@code super(...)} to the 1-byte Latin-1 form, so the {@code String.equals} intrinsic's
 * field reads stay correct when it fires with exact stamps. {@code charAt} is overridden (it is not
 * {@code @Uninterruptible} in {@code JavaLangSubstitutions}); {@code length()} is not (the inherited body returns 1),
 * which avoids the {@code @Uninterruptible} override rule.
 *
 * <p>Assumes compact strings: the 1-byte Latin-1 form, and {@link #equals}'s coder test, are the JDK's only when
 * {@code String.COMPACT_STRINGS} is true (a build-time constant; {@code -J-XX:-CompactStrings} makes it false). This
 * rep and the others that hard-code {@code LATIN1} (StringView, the lazy reps, RepParts) are therefore never created
 * without it: the build fails fast when reps are enabled and {@code COMPACT_STRINGS} is false
 * ({@code StringAnalysisFeature.requireCompactStrings}). No emitted code tests it.
 */
public class SingleByteString extends String {

    /**
     * Typed {@code String[]}, not {@code SingleByteString[]}: no rep array type exists in the image, so
     * {@code String[]} stays a leaf array type (exact stores and casts need no dynamic type check).
     * Premise of {@link #exactPoolEntry}: filled once at build time (svm.core is build-time initialized) with 256
     * non-null {@code SingleByteString} instances and never written again (private; read only by the four factories,
     * pinned by RepHeapPoolTest); {@code RepTypeChecks.checkImageHeap} fails the build unless every reference the pool
     * holds is a pool instance of this class.
     */
    private static final String[] POOL = new String[256];

    static {
        for (int i = 0; i < 256; i++) {
            POOL[i] = new SingleByteString((byte) i);
        }
    }

    private final byte value;

    /** The JDK's {@code String.LATIN1} coder value. */
    private static final byte LATIN1 = 0;

    private SingleByteString(byte value) {
        super(String.valueOf((char) (value & 0xFF)));
        this.value = value;
    }

    public static SingleByteString create(byte value) {
        return exactPoolEntry(POOL[value & 0xFF]);
    }

    public static SingleByteString create(char c) {
        if (c > 0xFF) {
            throw new IllegalArgumentException("SingleByteString requires Latin-1 char: " + c);
        }
        return exactPoolEntry(POOL[c & 0xFF]);
    }

    public static String createFromSubstring(String s, int start) {
        char c = s.charAt(start);
        if (c <= 0xFF) {
            return exactPoolEntry(POOL[c & 0xFF]);
        }
        return s.substring(start, start + 1);
    }

    public static String createFromChar(char c) {
        if (c <= 0xFF) {
            return exactPoolEntry(POOL[c & 0xFF]);
        }
        return String.valueOf(c);
    }

    /**
     * An element of {@link #POOL} as the exact, non-null {@code SingleByteString} it is (the premise at {@link #POOL}).
     * In an image the call is intrinsified ({@code SingleByteStringPoolPluginRegistration}): no check is emitted, and
     * points-to and the compiler see the exact type. This checked-cast body runs only on the hosting JVM. Called only
     * with {@code POOL[i]} (RepHeapPoolTest).
     */
    private static SingleByteString exactPoolEntry(String poolEntry) {
        return (SingleByteString) poolEntry;
    }

    /** Any index but 0 goes to the JDK's {@code String.charAt} on the real {@code value[]}: the JDK's exception. */
    @Override
    public char charAt(int index) {
        if (index == 0) {
            return (char) (value & 0xFF);
        }
        return super.charAt(index);
    }

    /**
     * Premise: every SingleByteString is a {@link #POOL} entry, so two are equal iff identical. The premise is
     * structural: the only constructor is private and its only call is the {@code <clinit>} loop (one instance per
     * byte; no nested class, so no subclass). RepHeapPoolTest pins the pool's readers and writers, not the
     * constructor's call sites. An exact-{@code String} argument is compared on its fields (through the
     * {@link Target_java_lang_String_StringRep} aliases, no virtual call): equal iff its coder is Latin-1 and its
     * {@code value} is this one byte, the JDK's {@code String.equals} under compact strings (class comment). On the
     * hosting JVM and for other reps the content arm answers.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof SingleByteString) {
            return false;
        }
        if (ImageInfo.inImageRuntimeCode() && o != null && o.getClass() == String.class) {
            Target_java_lang_String_StringRep t = (Target_java_lang_String_StringRep) o;
            byte[] v = t.value;
            return t.coder == LATIN1 && v.length == 1 && v[0] == value;
        }
        if (o instanceof String s) {
            return s.length() == 1 && s.charAt(0) == (char) (value & 0xFF);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return value & 0xFF;
    }

    /*
     * The case mappings and offsetByCodePoints never hand this to JDK code (the inherited bodies pass it to
     * StringLatin1 / ConditionalSpecialCasing / Character.offsetByCodePoints: flat hand-offs the walk cannot always
     * enter). The case tables are the JDK's own answers, computed at build time on a fresh one-char plain String per
     * Latin-1 char under Locale.ROOT: SAME = the JDK returns its receiver (StringLatin1.to*Case's first scan finds
     * nothing to change; it precedes the locale read, so SAME is locale-independent), 0..255 = the one Latin-1 char of
     * the result, SLOW = any other result (e.g. upper case of U+00DF is "SS"). A changed char under a tr/az/lt locale,
     * and every SLOW char, runs the JDK on a fresh plain copy. A changed one-char Latin-1 result is the pool entry; an
     * unchanged one is this, as in the JDK.
     */

    private static final short SAME = -1;
    private static final short SLOW = -2;
    private static final short[] UPPER = caseTable(true);
    private static final short[] LOWER = caseTable(false);

    private static short[] caseTable(boolean upper) {
        short[] t = new short[256];
        for (int i = 0; i < 256; i++) {
            String s = new String(new char[]{(char) i});
            String r = upper ? s.toUpperCase(Locale.ROOT) : s.toLowerCase(Locale.ROOT);
            if (r == s) {
                t[i] = SAME;
            } else if (r.length() == 1 && r.charAt(0) <= 0xFF) {
                t[i] = (short) r.charAt(0);
            } else {
                t[i] = SLOW;
            }
        }
        return t;
    }

    /** The JDK's special-casing test, verbatim (StringLatin1.to*Case: Locale interns the language, so identity). */
    @SuppressWarnings("StringEquality")
    private static boolean specialCasing(Locale locale) {
        String lang = locale.getLanguage();
        return lang == "tr" || lang == "az" || lang == "lt";
    }

    /** The JDK on a fresh plain copy of the char; a one-char Latin-1 result is the pool entry. */
    private String slowCase(boolean upper, Locale locale) {
        String plain = new String(new char[]{(char) (value & 0xFF)});
        String r = upper ? plain.toUpperCase(locale) : plain.toLowerCase(locale);
        assert r != plain; // SAME (the JDK returns its receiver) is checked before slowCase; no message (it would hand this rep to a String body)
        if (r.length() == 1 && r.charAt(0) <= 0xFF) {
            return create((byte) r.charAt(0));
        }
        return r;
    }

    @Override
    public String toUpperCase(Locale locale) {
        if (locale == null) {
            throw new NullPointerException(); // the JDK's first check (StringLatin1.toUpperCase)
        }
        short r = UPPER[value & 0xFF];
        if (r == SAME) {
            return this;
        }
        if (r == SLOW || specialCasing(locale)) {
            return slowCase(true, locale);
        }
        return create((byte) r);
    }

    /** {@code toUpperCase(Locale.getDefault())}; the default locale is read only when the char changes. */
    @Override
    public String toUpperCase() {
        short r = UPPER[value & 0xFF];
        if (r == SAME) {
            return this;
        }
        Locale locale = Locale.getDefault();
        if (r == SLOW || specialCasing(locale)) {
            return slowCase(true, locale);
        }
        return create((byte) r);
    }

    @Override
    public String toLowerCase(Locale locale) {
        if (locale == null) {
            throw new NullPointerException(); // the JDK's first check (StringLatin1.toLowerCase)
        }
        short r = LOWER[value & 0xFF];
        if (r == SAME) {
            return this;
        }
        if (r == SLOW || specialCasing(locale)) {
            return slowCase(false, locale);
        }
        return create((byte) r);
    }

    /** {@code toLowerCase(Locale.getDefault())}; the default locale is read only when the char changes. */
    @Override
    public String toLowerCase() {
        short r = LOWER[value & 0xFF];
        if (r == SAME) {
            return this;
        }
        Locale locale = Locale.getDefault();
        if (r == SLOW || specialCasing(locale)) {
            return slowCase(false, locale);
        }
        return create((byte) r);
    }

    /**
     * {@code Character.offsetByCodePoints} on one char: {@code index + codePointOffset}, or a message-free
     * {@link IndexOutOfBoundsException} unless the index and the result are both in [0, 1].
     */
    @Override
    public int offsetByCodePoints(int index, int codePointOffset) {
        int r = index + codePointOffset;
        if (index < 0 || index > 1 || r < 0 || r > 1) {
            throw new IndexOutOfBoundsException();
        }
        return r;
    }
}
