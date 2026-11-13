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
 * Lazy Concat representation of {@code left + mid + right} (the {@code THREE_WAY} variant): {@link RopeString}'s
 * accessor-routed design (null inherited {@code value}, fail loud; see there for why the sweep is complete and the
 * {@code @Uninterruptible} mirror constraint) with three children. The constructor passes the OR of the children's
 * coders, the exact coder, to {@code super(coder)}, so the inherited {@code coder()}/{@code isLatin1()} are correct.
 * {@code hashCode()} folds the children's cached hashes (as {@link RopeString}) into the inherited
 * {@code hash}/{@code hashIsZero} cache.
 */
public class ThreeWayString extends String {

    private static final byte LATIN1 = 0;

    private final String left;
    private final String mid;
    private final String right;
    private final int length;

    private ThreeWayString(String left, String mid, String right, int length) {
        // The exact coder: the inherited coder()/isLatin1() are correct
        super((byte) (left.coder() | mid.coder() | right.coder()));
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.left = left;
        this.mid = mid;
        this.right = right;
        this.length = length;
        this.hashIsZero = false;
    }

    /**
     * A rep is never empty: three empty parts give the literal {@code ""} (the JDK returns a fresh String; identity of
     * empty results is out of scope).
     */
    public static String create(String left, String mid, String right) {
        int length = RepParts.lengthOf(left) + RepParts.lengthOf(mid) + RepParts.lengthOf(right);
        if (length == 0) {
            return "";
        }
        return new ThreeWayString(left, mid, right, length);
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

    @Override
    public char charAt(int index) {
        int len = length();
        if (index < 0 || index >= len) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + len);
        }
        int leftLen = RepParts.lengthOf(left);
        if (index < leftLen) {
            return RepParts.charAtOf(left, index);
        }
        int leftMidLen = leftLen + RepParts.lengthOf(mid);
        if (index < leftMidLen) {
            return RepParts.charAtOf(mid, index - leftLen);
        }
        return RepParts.charAtOf(right, index - leftMidLen);
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
        int pos = RepParts.walk(left, 0, s, n);
        if (pos >= 0) {
            pos = RepParts.walk(mid, pos, s, n);
        }
        if (pos >= 0) {
            pos = RepParts.walk(right, pos, s, n);
        }
        return pos >= 0 ? n : -pos - 1;
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            int leftLen = RepParts.lengthOf(left);
            int midLen = RepParts.lengthOf(mid);
            int rightLen = RepParts.lengthOf(right);
            int pMidRight = 1;
            for (int i = 0; i < midLen + rightLen; i++) {
                pMidRight *= 31;
            }
            int pRight = 1;
            for (int i = 0; i < rightLen; i++) {
                pRight *= 31;
            }
            h = left.hashCode() * pMidRight + mid.hashCode() * pRight + right.hashCode();
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
        int leftLen = RepParts.lengthOf(left);
        int leftMidLen = leftLen + RepParts.lengthOf(mid);
        if (srcEnd <= leftLen) {
            left.getChars(srcBegin, srcEnd, dst, dstBegin);
        } else if (srcBegin >= leftMidLen) {
            right.getChars(srcBegin - leftMidLen, srcEnd - leftMidLen, dst, dstBegin);
        } else if (srcBegin >= leftLen && srcEnd <= leftMidLen) {
            mid.getChars(srcBegin - leftLen, srcEnd - leftLen, dst, dstBegin);
        } else {
            int midStart = Math.max(srcBegin, leftLen);
            int midEnd = Math.min(srcEnd, leftMidLen);
            if (srcBegin < leftLen) {
                left.getChars(srcBegin, leftLen, dst, dstBegin);
                dstBegin += leftLen - srcBegin;
            }
            if (midStart < midEnd) {
                mid.getChars(midStart - leftLen, midEnd - leftLen, dst, dstBegin);
                dstBegin += midEnd - midStart;
            }
            if (srcEnd > leftMidLen) {
                right.getChars(0, srcEnd - leftMidLen, dst, dstBegin);
            }
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
            e.part(left);
            e.part(mid);
            e.part(right);
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
        int pos = RepParts.lowBytesSlice(left, 0, srcBegin, srcEnd, dst, dstBegin);
        pos = RepParts.lowBytesSlice(mid, pos, srcBegin, srcEnd, dst, dstBegin);
        RepParts.lowBytesSlice(right, pos, srcBegin, srcEnd, dst, dstBegin);
    }

    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        // Per child one System.arraycopy or inflate.
        int pos = RepParts.putPart(left, dst, dstBegin, coder);
        pos = RepParts.putPart(mid, dst, pos, coder);
        RepParts.putPart(right, dst, pos, coder);
    }

    /**
     * The builder JDK's ranged copy primitive ({@code AbstractStringBuilder.appendChars(.., String, ..)} and
     * {@code putStringAt} copy through it instead of reading {@code value()}): chars {@code [srcPos, srcPos + length)}
     * to {@code dst} at {@code dstBegin} in {@code dst}'s coder (the caller guarantees {@code coder >= coder()}).
     */
    @Override
    protected void getBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        int end = srcPos + length;
        int pos = RepParts.putSlice(left, 0, srcPos, end, dst, dstBegin, coder);
        pos = RepParts.putSlice(mid, pos, srcPos, end, dst, dstBegin, coder);
        RepParts.putSlice(right, pos, srcPos, end, dst, dstBegin, coder);
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
    static boolean equalsSameType(ThreeWayString a, ThreeWayString b) {
        if (a == b) {
            return true;
        }
        String aLeft = a.left;
        String aMid = a.mid;
        String aRight = a.right;
        String bLeft = b.left;
        String bMid = b.mid;
        String bRight = b.right;
        if (RepParts.lengthOf(aLeft) != RepParts.lengthOf(bLeft) || RepParts.lengthOf(aMid) != RepParts.lengthOf(bMid) || RepParts.lengthOf(aRight) != RepParts.lengthOf(bRight)) {
            // A different split of possibly equal content: compare by content.
            return equalsFallback(a, b);
        }
        if (!childEquals(aLeft, bLeft)) {
            return false;
        }
        if (!childEquals(aMid, bMid)) {
            return false;
        }
        return childEquals(aRight, bRight);
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
    static boolean equalsFallback(ThreeWayString a, Object b) {
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
