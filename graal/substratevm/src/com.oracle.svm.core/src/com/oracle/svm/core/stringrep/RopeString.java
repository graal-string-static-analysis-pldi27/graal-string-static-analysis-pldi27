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

import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;

import com.oracle.svm.core.Uninterruptible;

import jdk.internal.vm.annotation.ForceInline;

/**
 * Lazy Concat representation of {@code left + right}.
 *
 * <p><b>Accessor-routed deferred flatten.</b> The builder JDK routes every read of {@code String}'s private
 * {@code value} and {@code coder} fields through the {@code value()}/{@code coder()} accessors; since {@code value} is
 * {@code private final}, no code outside {@code String.java} can read the field, so the sweep is complete by
 * construction in the closed world. The inherited {@code value} is null (set via {@code super(coder)}), so a residual
 * read NPEs (fail loud); the one remaining direct field read is the SVM {@code @Uninterruptible} mirror
 * ({@code Target_java_lang_String.value} via {@code UninterruptibleUtils}), which a rope must not flow into (as for
 * the other lazy reps). The overridden methods read the children directly, never {@code value()}; the charset
 * {@code getBytes} encode UTF-8/ISO-8859-1/US-ASCII from the children and materialize a flat copy otherwise.
 * {@code toString()} is inherited.
 *
 * <p>{@code coder()}/{@code isLatin1()} are inherited (overriding them would make every String-typed
 * {@code coder()} call virtual image-wide): the constructor passes {@code left.coder() | right.coder()}, the exact
 * coder, to {@code super}. {@code hashCode} is {@code left.hashCode() * 31^rightLen + right.hashCode()}, equal to the
 * flat string's hash for all coders since {@code String.hashCode()} is char-wise; it reuses the children's cached
 * hashes and caches the result in the inherited {@code hash}/{@code hashIsZero}.
 */
public class RopeString extends String {

    private static final byte LATIN1 = 0;

    private final String left;
    private final String right;
    private final int length;

    private RopeString(String left, String right, int length) {
        super((byte) (left.coder() | right.coder())); // the exact coder: the inherited coder()/isLatin1() are correct
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.left = left;
        this.right = right;
        this.length = length;
        this.hashIsZero = false;
    }

    /**
     * A rep is never empty: two empty parts give the literal {@code ""} (the JDK returns a fresh String; identity of
     * empty results is out of scope). Through the factories this case does not arise.
     */
    public static String create(String left, String right) {
        int length = RepParts.lengthOf(left) + RepParts.lengthOf(right);
        if (length == 0) {
            return "";
        }
        return new RopeString(left, right, length);
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
        return RepParts.charAtOf(right, index - leftLen);
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
            pos = RepParts.walk(right, pos, s, n);
        }
        return pos >= 0 ? n : -pos - 1;
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            int rightLen = RepParts.lengthOf(right);
            int p = 1;
            for (int i = 0; i < rightLen; i++) {
                p *= 31;
            }
            h = left.hashCode() * p + right.hashCode();
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
        if (srcEnd <= leftLen) {
            left.getChars(srcBegin, srcEnd, dst, dstBegin);
        } else if (srcBegin >= leftLen) {
            right.getChars(srcBegin - leftLen, srcEnd - leftLen, dst, dstBegin);
        } else {
            int rightLen = srcEnd - leftLen;
            left.getChars(srcBegin, leftLen, dst, dstBegin);
            right.getChars(0, rightLen, dst, dstBegin + (leftLen - srcBegin));
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
    public byte[] getBytes(String charsetName) throws UnsupportedEncodingException {
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
        RepParts.lowBytesSlice(right, pos, srcBegin, srcEnd, dst, dstBegin);
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
        RepParts.putSlice(right, pos, srcPos, end, dst, dstBegin, coder);
    }

    /**
     * The whole-string copy primitive ({@code AbstractStringBuilder.append(String)}, {@code insert}, {@code replace},
     * the builder constructor and the non-copying concat strategy copy through it; the inherited body reads the null
     * {@code value()}): one {@code RepParts.putPart} per child (total over value-null children). Not the ranged
     * copy: no svm class may invoke it ({@code RangeCopyParityTest}).
     */
    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        RepParts.putPart(right, dst, RepParts.putPart(left, dst, dstBegin, coder), coder);
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
    static boolean equalsSameType(RopeString a, RopeString b) {
        if (a == b) {
            return true;
        }
        String aLeft = a.left;
        String aRight = a.right;
        String bLeft = b.left;
        String bRight = b.right;
        if (RepParts.lengthOf(aLeft) != RepParts.lengthOf(bLeft) || RepParts.lengthOf(aRight) != RepParts.lengthOf(bRight)) {
            // A different split of possibly equal content: compare by content.
            return equalsFallback(a, b);
        }
        if (!childEquals(aLeft, bLeft)) {
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
    static boolean equalsFallback(RopeString a, Object b) {
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