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

import com.oracle.svm.core.Uninterruptible;

import java.nio.charset.Charset;

import jdk.internal.vm.annotation.ForceInline;

/**
 * Lazy Concat representation of {@code a + b + c + d} (the {@code FIXED4} variant): {@link RopeString}'s
 * accessor-routed design (null inherited {@code value}, fail loud; see there for why the sweep is complete and the
 * {@code @Uninterruptible} mirror constraint) with four children. The constructor passes the OR of the children's
 * coders, the exact coder, to {@code super(coder)}, so the inherited {@code coder()}/{@code isLatin1()} are correct.
 * {@code hashCode()} folds the children's cached hashes (as {@link RopeString}) into the inherited
 * {@code hash}/{@code hashIsZero} cache.
 */
public class FixedConcat4 extends String {

    private static final byte LATIN1 = 0;

    private final String a;
    private final String b;
    private final String c;
    private final String d;
    private final int length;

    private FixedConcat4(String a, String b, String c, String d, int length) {
        // The exact coder: the inherited coder()/isLatin1() are correct
        super((byte) (a.coder() | b.coder() | c.coder() | d.coder()));
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.a = a;
        this.b = b;
        this.c = c;
        this.d = d;
        this.length = length;
        this.hashIsZero = false;
    }

    /**
     * A rep is never empty: four empty parts give the literal {@code ""} (the JDK returns a fresh String; identity of
     * empty results is out of scope).
     */
    public static String create(String a, String b, String c, String d) {
        int length = RepParts.lengthOf(a) + RepParts.lengthOf(b) + RepParts.lengthOf(c) + RepParts.lengthOf(d);
        if (length == 0) {
            return "";
        }
        return new FixedConcat4(a, b, c, d, length);
    }

    @Override
    @Uninterruptible(reason = "Called from uninterruptible code.", mayBeInlined = true)
    public int length() {
        return length;
    }

    // A rep is never empty: every empty result is the literal "".
    @Override
    @Uninterruptible(reason = "Called from uninterruptible code.", mayBeInlined = true)
    public boolean isEmpty() {
        return false;
    }

    private char childCharAt(int index, int lenA, int lenAB, int lenABC) {
        if (index < lenA) {
            return RepParts.charAtOf(a, index);
        }
        if (index < lenAB) {
            return RepParts.charAtOf(b, index - lenA);
        }
        if (index < lenABC) {
            return RepParts.charAtOf(c, index - lenAB);
        }
        return RepParts.charAtOf(d, index - lenABC);
    }

    @Override
    public char charAt(int index) {
        int len = length();
        if (index < 0 || index >= len) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + len);
        }
        int lenA = RepParts.lengthOf(a);
        int lenAB = lenA + RepParts.lengthOf(b);
        int lenABC = lenAB + RepParts.lengthOf(c);
        return childCharAt(index, lenA, lenAB, lenABC);
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof String s)) {
            return false;
        }
        int len = length;
        if (s.length() != len) {
            return false;
        }
        return mismatch(s, len) == len; // per-child array compares
    }

    /**
     * The first index in {@code [0, n)} where this string and {@code s} differ, else {@code n}
     * ({@code n <= min(length, s.length())}): each child is compared with its slice of {@code s} by array.
     */
    private int mismatch(String s, int n) {
        int pos = RepParts.walk(a, 0, s, n);
        if (pos >= 0) {
            pos = RepParts.walk(b, pos, s, n);
        }
        if (pos >= 0) {
            pos = RepParts.walk(c, pos, s, n);
        }
        if (pos >= 0) {
            pos = RepParts.walk(d, pos, s, n);
        }
        return pos >= 0 ? n : -pos - 1;
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            int lenA = RepParts.lengthOf(a);
            int lenB = RepParts.lengthOf(b);
            int lenC = RepParts.lengthOf(c);
            int lenD = RepParts.lengthOf(d);
            int pBCD = 1;
            for (int i = 0; i < lenB + lenC + lenD; i++) {
                pBCD *= 31;
            }
            int pCD = 1;
            for (int i = 0; i < lenC + lenD; i++) {
                pCD *= 31;
            }
            int pD = 1;
            for (int i = 0; i < lenD; i++) {
                pD *= 31;
            }
            h = a.hashCode() * pBCD + b.hashCode() * pCD + c.hashCode() * pD + d.hashCode();
            if (h == 0) {
                hashIsZero = true;
            } else {
                hash = h;
            }
        }
        return h;
    }

    /**
     * The inherited {@code compareTo} reads the null {@code value()}. This one is exact and total over plain Strings,
     * flat reps and value-null reps; {@code String.maybeCustomStringCompareTo} deflects a rep argument here.
     */
    @Override
    public int compareTo(String anotherString) {
        // First differing char, else the length difference (exactly negated on the argument side)
        int n = Math.min(length, anotherString.length());
        int k = mismatch(anotherString, n);
        if (k < n) {
            return charAt(k) - anotherString.charAt(k);
        }
        return length - anotherString.length();
    }

    @Override
    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        int len = length();
        if (srcBegin < 0 || srcEnd > len || srcBegin > srcEnd) {
            throw new StringIndexOutOfBoundsException("begin " + srcBegin + ", end " + srcEnd + ", length " + len);
        }
        int count = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - count) {
            throw new StringIndexOutOfBoundsException("offset " + dstBegin + ", count " + count + ", length " + dst.length);
        }
        int lenA = RepParts.lengthOf(a);
        int lenAB = lenA + RepParts.lengthOf(b);
        int lenABC = lenAB + RepParts.lengthOf(c);
        int offset = dstBegin;
        if (srcBegin < lenA) {
            int end = Math.min(srcEnd, lenA);
            a.getChars(srcBegin, end, dst, offset);
            offset += end - srcBegin;
        }
        if (srcBegin < lenAB && srcEnd > lenA) {
            int start = Math.max(srcBegin, lenA);
            int end = Math.min(srcEnd, lenAB);
            b.getChars(start - lenA, end - lenA, dst, offset);
            offset += end - start;
        }
        if (srcBegin < lenABC && srcEnd > lenAB) {
            int start = Math.max(srcBegin, lenAB);
            int end = Math.min(srcEnd, lenABC);
            c.getChars(start - lenAB, end - lenAB, dst, offset);
            offset += end - start;
        }
        if (srcEnd > lenABC) {
            int start = Math.max(srcBegin, lenABC);
            d.getChars(start - lenABC, srcEnd - lenABC, dst, offset);
        }
    }

    @Override
    public char[] toCharArray() {
        char[] out = new char[length()];
        getChars(0, length(), out, 0);
        return out;
    }

    private String materializeFlat() {
        char[] chars = new char[length()];
        getChars(0, length(), chars, 0);
        return new String(chars);
    }

    @Override
    public byte[] getBytes() {
        byte[] r = encode(RepParts.kindOf(Charset.defaultCharset()));
        return r != null ? r : materializeFlat().getBytes();
    }

    @Override
    public byte[] getBytes(String charsetName) throws java.io.UnsupportedEncodingException {
        Charset cs = RepParts.lookup(charsetName);
        if (cs == null) {
            return materializeFlat().getBytes(charsetName); // the JDK's own exception
        }
        byte[] r = encode(RepParts.kindOf(cs));
        return r != null ? r : materializeFlat().getBytes(cs);
    }

    @Override
    public byte[] getBytes(Charset charset) {
        byte[] r = encode(RepParts.kindOf(charset));
        return r != null ? r : materializeFlat().getBytes(charset);
    }

    /**
     * The JDK's UTF-8 / ISO-8859-1 / US-ASCII encoding straight from the children; {@code null} for any other charset
     * or an oversized UTF-8 result.
     */
    private byte[] encode(int kind) {
        if (kind < 0) {
            return null;
        }
        RepParts.Enc e = new RepParts.Enc(kind, length);
        while (e.pass()) {
            e.part(a);
            e.part(b);
            e.part(c);
            e.part(d);
        }
        return e.result();
    }

    @SuppressWarnings("deprecation")
    @Override
    public void getBytes(int srcBegin, int srcEnd, byte[] dst, int dstBegin) {
        if (srcBegin < 0 || srcBegin > srcEnd || srcEnd > length || dst == null || dstBegin < 0 || dstBegin > dst.length - (srcEnd - srcBegin)) {
            materializeFlat().getBytes(srcBegin, srcEnd, dst, dstBegin); // the JDK's own exception
            return;
        }
        // Only the subrange, per child (no flat copy of the whole string).
        int pos = RepParts.lowBytesSlice(a, 0, srcBegin, srcEnd, dst, dstBegin);
        pos = RepParts.lowBytesSlice(b, pos, srcBegin, srcEnd, dst, dstBegin);
        pos = RepParts.lowBytesSlice(c, pos, srcBegin, srcEnd, dst, dstBegin);
        RepParts.lowBytesSlice(d, pos, srcBegin, srcEnd, dst, dstBegin);
    }

    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        // Per child one System.arraycopy or inflate.
        int pos = RepParts.putPart(a, dst, dstBegin, coder);
        pos = RepParts.putPart(b, dst, pos, coder);
        pos = RepParts.putPart(c, dst, pos, coder);
        RepParts.putPart(d, dst, pos, coder);
    }

    /**
     * The builder JDK's ranged copy primitive ({@code AbstractStringBuilder.appendChars(.., String, ..)} and
     * {@code putStringAt} copy through it instead of reading {@code value()}): chars {@code [srcPos, srcPos + length)}
     * to {@code dst} at {@code dstBegin} in {@code dst}'s coder (the caller guarantees {@code coder >= coder()}).
     */
    @Override
    protected void getBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        int end = srcPos + length;
        int pos = RepParts.putSlice(a, 0, srcPos, end, dst, dstBegin, coder);
        pos = RepParts.putSlice(b, pos, srcPos, end, dst, dstBegin, coder);
        pos = RepParts.putSlice(c, pos, srcPos, end, dst, dstBegin, coder);
        RepParts.putSlice(d, pos, srcPos, end, dst, dstBegin, coder);
    }

    @Override
    public boolean maybeCustomStringEquals(Object that) {
        return this.equals(that);
    }

    /**
     * The inherited body deflects to {@code another.compareTo(this)}, which for a flat argument (SingleByteString,
     * TrivialString: the stock body) would read this rep's null {@code value()}; this rep's {@code compareTo} is total.
     */
    @Override
    public int maybeCustomStringCompareTo(String another) {
        return compareTo(another);
    }

    @ForceInline
    static boolean equalsSameType(FixedConcat4 a, FixedConcat4 b) {
        if (a == b) {
            return true;
        }
        String aA = a.a;
        String aB = a.b;
        String aC = a.c;
        String aD = a.d;
        String bA = b.a;
        String bB = b.b;
        String bC = b.c;
        String bD = b.d;
        if (RepParts.lengthOf(aA) != RepParts.lengthOf(bA) || RepParts.lengthOf(aB) != RepParts.lengthOf(bB) || RepParts.lengthOf(aC) != RepParts.lengthOf(bC) ||
                        RepParts.lengthOf(aD) != RepParts.lengthOf(bD)) {
            // A different split of possibly equal content: compare by content.
            return equalsFallback(a, b);
        }
        if (!childEquals(aA, bA)) {
            return false;
        }
        if (!childEquals(aB, bB)) {
            return false;
        }
        if (!childEquals(aC, bC)) {
            return false;
        }
        return childEquals(aD, bD);
    }

    private static boolean childEquals(String a, String b) {
        if (a == b) {
            return true;
        }
        byte aCoder = a.coder();
        byte bCoder = b.coder();
        byte[] av = a.value();
        byte[] bv = b.value();
        if (av == null || bv == null || aCoder != bCoder) {
            // A value-null child or a coder mismatch (equal content can differ in coder when a child is not
            // compact) compares by content
            return RepEquals.contentEquals(a, b);
        }
        if (aCoder == LATIN1) {
            return latin1Equals(av, 0, bv, 0, av.length);
        }
        // utf16Equals takes a char count; av.length is the byte count
        return utf16Equals(av, 0, bv, 0, av.length >> 1);
    }

    @ForceInline
    static boolean equalsFallback(FixedConcat4 a, Object b) {
        if (a == b) {
            return true;
        }
        if (!(b instanceof String s)) {
            return false;
        }
        int len = a.length;
        if (s.length() != len) {
            return false;
        }
        return a.mismatch(s, len) == len; // per-child array compares
    }
}
