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

import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

import com.oracle.svm.core.AlwaysInline;

/**
 * The shared per-part bodies of the lazy reps and {@link StringView}: array compares, copies and the three JDK
 * fast-path encodings (UTF-8, ISO-8859-1, US-ASCII) straight from the parts, with no flat copy.
 *
 * <p>A part is read through its real {@code value()} array when it has one, otherwise through its own
 * {@code getChars}/{@code charAt} (a value-null rep), so each body is total over every part. Results are
 * byte-identical to the JDK's on the flat string: the JDK 25 encodings depend only on the char sequence, and the
 * surrogate state is carried across part boundaries.
 */
final class RepParts {

    private static final byte LATIN1 = 0;

    /** The JDK's {@code StringUTF16} byte order (as {@code StringView.computeHiByteShift}). */
    static final int HI_BYTE_SHIFT;
    static final int LO_BYTE_SHIFT;

    static {
        byte[] b = "Ā".value();
        HI_BYTE_SHIFT = (b[0] == 0x01) ? 8 : 0;
        LO_BYTE_SHIFT = 8 - HI_BYTE_SHIFT;
    }

    static final int UTF8 = 0;
    static final int ISO = 1;
    static final int ASCII = 2;

    private RepParts() {
    }

    // ---------------------------------------------------------------- part reads

    /*
     * The parts of a lazy rep are exact Strings at the default (lc.lazyoperand=2): the nested-LS rule refuses an LS
     * inside a kept LS, and a StringView operand drops the LS site. Two exceptions remain, so every part read below
     * keeps the virtual path for a non-exact part: a lowered String.join stores an admitted view element in an
     * InterleavedStringArray, and lc.lazyoperand=1 (ablation) nests lazy reps. The exact-class test folds away where
     * points-to proves the part exact; otherwise it costs one hub compare instead of a vtable call.
     */

    /** {@code s.length()}, read directly for an exact String (reps override the virtual {@code length()}). */
    @AlwaysInline("devirtualized length of an exact String part")
    static int lengthOf(String s) {
        if (s.getClass() == String.class) {
            return s.value().length >> s.coder();
        }
        return s.length();
    }

    /**
     * {@code s.charAt(index)} with {@code index} already in range (the rep's own bounds check covered it), read
     * directly for an exact String.
     */
    @AlwaysInline("devirtualized charAt of an exact String part")
    static char charAtOf(String s, int index) {
        if (s.getClass() == String.class) {
            byte[] v = s.value();
            return s.coder() == LATIN1 ? (char) (v[index] & 0xff) : getChar(v, index);
        }
        return s.charAt(index);
    }

    static char getChar(byte[] v, int index) {
        int i = index << 1;
        return (char) (((v[i] & 0xff) << HI_BYTE_SHIFT) | ((v[i + 1] & 0xff) << LO_BYTE_SHIFT));
    }

    static void putChar(byte[] v, int index, int c) {
        int i = index << 1;
        v[i] = (byte) (c >> HI_BYTE_SHIFT);
        v[i + 1] = (byte) (c >> LO_BYTE_SHIFT);
    }

    private static char charOf(byte[] v, byte coder, int index) {
        return coder == LATIN1 ? (char) (v[index] & 0xff) : getChar(v, index);
    }

    // ---------------------------------------------------------------- comparison

    /**
     * The first {@code k} in {@code [0, n)} with {@code p.charAt(pFrom + k) != s.charAt(sFrom + k)}, else {@code -1}.
     * Two real arrays of one coder: one vectorized {@link Arrays#mismatch}; mixed coders: a decoding loop; a value-null
     * side: {@code charAt}.
     */
    static int mismatch(String p, int pFrom, String s, int sFrom, int n) {
        if (n <= 0) {
            return -1;
        }
        byte[] pv = p.value();
        byte[] sv = s.value();
        if (pv != null && sv != null) {
            byte pc = p.coder();
            byte sc = s.coder();
            if (pc == sc) {
                if (pc == LATIN1) {
                    return Arrays.mismatch(pv, pFrom, pFrom + n, sv, sFrom, sFrom + n);
                }
                int k = Arrays.mismatch(pv, pFrom << 1, (pFrom + n) << 1, sv, sFrom << 1, (sFrom + n) << 1);
                return k < 0 ? -1 : k >> 1;
            }
            for (int k = 0; k < n; k++) {
                if (charOf(pv, pc, pFrom + k) != charOf(sv, sc, sFrom + k)) {
                    return k;
                }
            }
            return -1;
        }
        for (int k = 0; k < n; k++) {
            if (p.charAt(pFrom + k) != s.charAt(sFrom + k)) {
                return k;
            }
        }
        return -1;
    }

    /**
     * One step of a sequential part walk: part {@code p} starts at {@code pos} of the whole string; it is compared
     * with {@code s[pos, ...)} up to the global limit {@code n}. Returns {@code -(k + 1)} when the strings differ at
     * the global index {@code k < n}, else the next part's start {@code pos + p.length()} (non-negative).
     */
    static int walk(String p, int pos, String s, int n) {
        int pl = lengthOf(p);
        int cmp = Math.min(pl, n - pos);
        if (cmp > 0) {
            int k = mismatch(p, 0, s, pos, cmp);
            if (k >= 0) {
                return -(pos + k + 1);
            }
        }
        return pos + pl;
    }

    /**
     * {@code [from, from + n)} of a real Latin-1 ({@code coder == 0}) or UTF-16 array {@code v} against
     * {@code s[sFrom, sFrom + n)}: the first differing offset, else {@code -1} (StringView's backing).
     */
    static int mismatchArray(byte[] v, byte coder, int from, String s, int sFrom, int n) {
        if (n <= 0) {
            return -1;
        }
        byte[] sv = s.value();
        if (sv != null) {
            byte sc = s.coder();
            if (sc == coder) {
                if (coder == LATIN1) {
                    return Arrays.mismatch(v, from, from + n, sv, sFrom, sFrom + n);
                }
                int k = Arrays.mismatch(v, from << 1, (from + n) << 1, sv, sFrom << 1, (sFrom + n) << 1);
                return k < 0 ? -1 : k >> 1;
            }
            for (int k = 0; k < n; k++) {
                if (charOf(v, coder, from + k) != charOf(sv, sc, sFrom + k)) {
                    return k;
                }
            }
            return -1;
        }
        for (int k = 0; k < n; k++) {
            if (charOf(v, coder, from + k) != s.charAt(sFrom + k)) {
                return k;
            }
        }
        return -1;
    }

    // ---------------------------------------------------------------- copies

    /**
     * The protected {@code String.getBytes(byte[], int, byte)} of one part: one {@code System.arraycopy} or inflate of
     * a real array, else the part's own {@code getChars}. Returns the end position {@code dstBegin + p.length()} (the
     * next part's start), so callers read no part length again.
     */
    static int putPart(String p, byte[] dst, int dstBegin, byte coder) {
        int n = lengthOf(p);
        if (n != 0) {
            copyPart(p, n, dst, dstBegin, coder);
        }
        return dstBegin + n;
    }

    private static void copyPart(String p, int n, byte[] dst, int dstBegin, byte coder) {
        byte[] v = p.value();
        if (v != null) {
            byte pc = p.coder();
            if (pc == coder) {
                System.arraycopy(v, 0, dst, dstBegin << coder, n << coder);
                return;
            }
            if (pc == LATIN1) {
                for (int i = 0; i < n; i++) {
                    putChar(dst, dstBegin + i, v[i] & 0xff);
                }
                return;
            }
        }
        char[] t = new char[n];
        p.getChars(0, n, t, 0);
        putChars(t, n, dst, dstBegin, coder);
    }

    /**
     * The ranged copy {@code getBytes(byte[],int,int,byte,int)} restricted to the part {@code p} starting at
     * {@code pos}: the overlap with {@code [srcBegin, srcEnd)} goes to {@code dst}. Returns the next part's start.
     */
    static int putSlice(String p, int pos, int srcBegin, int srcEnd, byte[] dst, int dstBegin, byte coder) {
        int pl = lengthOf(p);
        int s = Math.max(srcBegin, pos);
        int e = Math.min(srcEnd, pos + pl);
        if (s < e) {
            putRange(p, s - pos, e - pos, dst, dstBegin + (s - srcBegin), coder);
        }
        return pos + pl;
    }

    /**
     * Chars {@code [from, to)} of {@code p} into {@code dst} at {@code dstBegin}. Precondition (the invoker guarantee,
     * carried over since the rep's coder is the OR of its parts'): {@code coder >= p.coder()}; a UTF-16 part into a
     * Latin-1 {@code dst} would reach the narrowing {@code putChars} fallback and lose the high bytes.
     */
    static void putRange(String p, int from, int to, byte[] dst, int dstBegin, byte coder) {
        int n = to - from;
        byte[] v = p.value();
        if (v != null) {
            byte pc = p.coder();
            if (pc == coder) {
                System.arraycopy(v, from << coder, dst, dstBegin << coder, n << coder);
                return;
            }
            if (pc == LATIN1) {
                for (int i = 0; i < n; i++) {
                    putChar(dst, dstBegin + i, v[from + i] & 0xff);
                }
                return;
            }
        }
        char[] t = new char[n];
        p.getChars(from, to, t, 0);
        putChars(t, n, dst, dstBegin, coder);
    }

    private static void putChars(char[] t, int n, byte[] dst, int dstBegin, byte coder) {
        if (coder == LATIN1) {
            for (int i = 0; i < n; i++) {
                dst[dstBegin + i] = (byte) t[i];
            }
        } else {
            for (int i = 0; i < n; i++) {
                putChar(dst, dstBegin + i, t[i]);
            }
        }
    }

    /**
     * The deprecated {@code getBytes(int, int, byte[], int)} (low bytes) restricted to the part {@code p} starting at
     * {@code pos}. Returns the next part's start.
     */
    static int lowBytesSlice(String p, int pos, int srcBegin, int srcEnd, byte[] dst, int dstBegin) {
        int pl = lengthOf(p);
        int s = Math.max(srcBegin, pos);
        int e = Math.min(srcEnd, pos + pl);
        if (s < e) {
            lowBytes(p, s - pos, e - pos, dst, dstBegin + (s - srcBegin));
        }
        return pos + pl;
    }

    private static void lowBytes(String p, int from, int to, byte[] dst, int dstBegin) {
        int n = to - from;
        byte[] v = p.value();
        if (v != null) {
            if (p.coder() == LATIN1) {
                System.arraycopy(v, from, dst, dstBegin, n);
            } else {
                for (int i = 0; i < n; i++) {
                    dst[dstBegin + i] = (byte) getChar(v, from + i);
                }
            }
            return;
        }
        char[] t = new char[n];
        p.getChars(from, to, t, 0);
        for (int i = 0; i < n; i++) {
            dst[dstBegin + i] = (byte) t[i];
        }
    }

    // ---------------------------------------------------------------- encoding

    /** The fast-path encoding of {@code cs} (identity, as the JDK's {@code String.encode}), else {@code -1}. */
    static int kindOf(Charset cs) {
        if (cs == StandardCharsets.UTF_8) {
            return UTF8;
        }
        if (cs == StandardCharsets.ISO_8859_1) {
            return ISO;
        }
        if (cs == StandardCharsets.US_ASCII) {
            return ASCII;
        }
        return -1;
    }

    /**
     * The JDK's {@code String.lookupCharset} without its exceptions: {@code null} when the name is null, illegal or
     * unsupported (the caller then runs the JDK body, which throws exactly the JDK's exception).
     */
    static Charset lookup(String charsetName) {
        if (charsetName == null) {
            return null;
        }
        try {
            return Charset.forName(charsetName);
        } catch (IllegalArgumentException e) {
            return null; // IllegalCharsetNameException, UnsupportedCharsetException
        }
    }

    /**
     * A streaming encoder over a string's parts in order, driven by {@link #pass()}:
     *
     * <pre>
     * Enc e = new Enc(kind, length);
     * while (e.pass()) {
     *     // feed every part, in order: e.part(p) / e.latin1(..) / e.utf16(..)
     * }
     * byte[] r = e.result(); // null: run the JDK body instead
     * </pre>
     *
     * UTF-8 takes two passes (count, then write); ISO-8859-1/US-ASCII one pass into a {@code length}-byte array.
     * {@code pend}: UTF-8, a high surrogate waiting for its low one; ISO/ASCII, a {@code '?'} was written for a high
     * surrogate, so a low surrogate next is consumed with it.
     */
    static final class Enc {
        private final int kind;
        private final int length;
        private byte[] d;
        private int dp;
        private long count;
        private char pend;
        private int passes;
        private boolean tooLarge;

        Enc(int kind, int length) {
            this.kind = kind;
            this.length = length;
        }

        /** Starts the next pass; {@code false} when the encoding is complete. */
        boolean pass() {
            int p = passes++;
            if (p == 0) {
                if (kind != UTF8) {
                    d = new byte[length];
                }
                return true;
            }
            finish();
            if (p == 1 && kind == UTF8) {
                if (count > Integer.MAX_VALUE - 8) {
                    tooLarge = true; // the JDK body reports it (its own OutOfMemoryError)
                    return false;
                }
                d = new byte[(int) count];
                return true;
            }
            return false;
        }

        /** A whole part of any representation. */
        void part(String p) {
            int n = p.length();
            if (n == 0) {
                return;
            }
            byte[] v = p.value();
            if (v != null) {
                if (p.coder() == LATIN1) {
                    latin1(v, 0, n);
                } else {
                    utf16(v, 0, n);
                }
                return;
            }
            char[] t = new char[n];
            p.getChars(0, n, t, 0);
            for (int i = 0; i < n; i++) {
                put(t[i]);
            }
        }

        /** {@code n} Latin-1 chars of {@code v} from {@code off}. A Latin-1 char is never a surrogate. */
        void latin1(byte[] v, int off, int n) {
            if (n == 0) {
                return;
            }
            if (pend != 0) {
                pend = 0; // ISO/ASCII: a Latin-1 char is not the low surrogate to consume
                if (kind == UTF8) {
                    emit((byte) '?'); // the waiting high surrogate is unpaired
                }
            }
            int end = off + n;
            if (kind == UTF8) {
                if (d == null) {
                    long c = n;
                    for (int i = off; i < end; i++) {
                        if (v[i] < 0) {
                            c++;
                        }
                    }
                    count += c;
                } else {
                    byte[] out = d;
                    int o = dp;
                    for (int i = off; i < end; i++) {
                        byte b = v[i];
                        if (b >= 0) {
                            out[o++] = b;
                        } else {
                            out[o++] = (byte) (0xc0 | ((b & 0xff) >> 6));
                            out[o++] = (byte) (0x80 | (b & 0x3f));
                        }
                    }
                    dp = o;
                }
            } else if (kind == ISO) {
                System.arraycopy(v, off, d, dp, n);
                dp += n;
            } else {
                byte[] out = d;
                int o = dp;
                for (int i = off; i < end; i++) {
                    byte b = v[i];
                    out[o++] = b < 0 ? (byte) '?' : b;
                }
                dp = o;
            }
        }

        /** {@code n} UTF-16 chars of {@code v} from char index {@code off}. */
        void utf16(byte[] v, int off, int n) {
            int end = off + n;
            for (int i = off; i < end; i++) {
                put(getChar(v, i));
            }
        }

        private void emit(byte b) {
            if (d == null) {
                count++;
            } else {
                d[dp++] = b;
            }
        }

        void put(char c) {
            if (kind == UTF8) {
                if (pend != 0) {
                    char h = pend;
                    pend = 0;
                    if (Character.isLowSurrogate(c)) {
                        int uc = Character.toCodePoint(h, c);
                        if (d == null) {
                            count += 4;
                        } else {
                            d[dp++] = (byte) (0xf0 | ((uc >> 18)));
                            d[dp++] = (byte) (0x80 | ((uc >> 12) & 0x3f));
                            d[dp++] = (byte) (0x80 | ((uc >> 6) & 0x3f));
                            d[dp++] = (byte) (0x80 | (uc & 0x3f));
                        }
                        return;
                    }
                    emit((byte) '?');
                }
                if (c < 0x80) {
                    emit((byte) c);
                } else if (c < 0x800) {
                    if (d == null) {
                        count += 2;
                    } else {
                        d[dp++] = (byte) (0xc0 | (c >> 6));
                        d[dp++] = (byte) (0x80 | (c & 0x3f));
                    }
                } else if (Character.isSurrogate(c)) {
                    if (Character.isHighSurrogate(c)) {
                        pend = c;
                    } else {
                        emit((byte) '?');
                    }
                } else if (d == null) {
                    count += 3;
                } else {
                    d[dp++] = (byte) (0xe0 | ((c >> 12)));
                    d[dp++] = (byte) (0x80 | ((c >> 6) & 0x3f));
                    d[dp++] = (byte) (0x80 | (c & 0x3f));
                }
                return;
            }
            if (pend != 0) {
                pend = 0;
                if (Character.isLowSurrogate(c)) {
                    return; // the pair was replaced by the one '?' already written
                }
            }
            int limit = kind == ISO ? 0xff : 0x7f;
            if (c <= limit) {
                d[dp++] = (byte) c;
            } else {
                d[dp++] = (byte) '?';
                if (Character.isHighSurrogate(c)) {
                    pend = c;
                }
            }
        }

        /** The end of the input: a UTF-8 high surrogate still waiting is unpaired ({@code '?'}). */
        void finish() {
            if (pend != 0) {
                pend = 0;
                if (kind == UTF8) {
                    emit((byte) '?');
                }
            }
        }

        /** The encoded bytes; {@code null} when the UTF-8 result cannot be an array. ISO/ASCII trim the array when
         * surrogate pairs became one {@code '?'} (as the JDK). */
        byte[] result() {
            if (tooLarge) {
                return null;
            }
            return dp == d.length ? d : Arrays.copyOf(d, dp);
        }
    }
}
