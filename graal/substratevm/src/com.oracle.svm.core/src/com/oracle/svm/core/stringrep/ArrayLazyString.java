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
 * Lazy Concat representation of the concatenation of N &ge; 5 parts stored in a {@code String[]} (the
 * {@code ARRAY_LAZY} variant): {@link RopeString}'s accessor-routed design (null inherited {@code value}, fail loud;
 * see there for why the sweep is complete and the {@code @Uninterruptible} mirror constraint) generalized to an
 * array. The constructor passes the OR of the parts' coders, the exact coder, to {@code super(coder)}, so the
 * inherited {@code coder()}/{@code isLatin1()} are correct. {@code hashCode()} folds the parts' cached hashes
 * (as {@link RopeString}) into the inherited {@code hash}/{@code hashIsZero} cache.
 */
public class ArrayLazyString extends String {

    private static final byte LATIN1 = 0;

    private final String[] parts;
    private final int length;

    /** {@code ownedParts} is owned by this string (no other reference to it), so never written after construction. */
    private ArrayLazyString(String[] ownedParts, byte coder, int length) {
        // The exact coder: the inherited coder()/isLatin1() are correct
        super(coder);
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.parts = ownedParts;
        this.length = length;
        this.hashIsZero = false;
    }

    private static byte computeCoder(String[] parts) {
        byte c = LATIN1;
        for (int i = 0; i < parts.length; i++) {
            if (parts[i] == null) {
                throw new NullPointerException("parts[" + i + "] is null");
            }
            c |= parts[i].coder();
        }
        return c;
    }

    /** A copying factory: the caller keeps {@code parts} (a caller-visible array). */
    public static String create(String[] parts) {
        return createOwned(parts.clone());
    }

    /**
     * The owning factory: {@code ownedParts} (non-null parts) is handed over, so the caller must hold no other
     * reference to it. All parts empty give the literal {@code ""} (the JDK returns a fresh String; identity of empty
     * results is out of scope), never an empty rep.
     */
    public static String createOwned(String[] ownedParts) {
        byte coder = computeCoder(ownedParts);
        int len = 0;
        for (int i = 0; i < ownedParts.length; i++) {
            len += RepParts.lengthOf(ownedParts[i]);
        }
        if (len == 0) {
            return "";
        }
        return new ArrayLazyString(ownedParts, coder, len);
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
        int len = length;
        if (index < 0 || index >= len) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + len);
        }
        int remaining = index;
        for (int i = 0; i < parts.length; i++) {
            int pl = RepParts.lengthOf(parts[i]);
            if (remaining < pl) {
                return RepParts.charAtOf(parts[i], remaining);
            }
            remaining -= pl;
        }
        throw new InternalError("unreachable");
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
     * ({@code n <= min(length, s.length())}): one walk comparing each part with its slice of {@code s}, O(n).
     */
    private int mismatch(String s, int n) {
        String[] ps = parts;
        int pos = 0;
        for (int i = 0; i < ps.length && pos < n; i++) {
            pos = RepParts.walk(ps[i], pos, s, n);
            if (pos < 0) {
                return -pos - 1;
            }
        }
        return n;
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            for (int i = 0; i < parts.length; i++) {
                int childLen = RepParts.lengthOf(parts[i]);
                int p = 1;
                for (int j = 0; j < childLen; j++) {
                    p *= 31;
                }
                h = h * p + parts[i].hashCode();
            }
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
        int len = length;
        if (srcBegin < 0 || srcEnd > len || srcBegin > srcEnd) {
            throw new StringIndexOutOfBoundsException("begin " + srcBegin + ", end " + srcEnd + ", length " + len);
        }
        int count = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - count) {
            throw new StringIndexOutOfBoundsException("offset " + dstBegin + ", count " + count + ", length " + dst.length);
        }
        int offset = dstBegin;
        int pos = 0;
        for (int i = 0; i < parts.length && pos < srcEnd; i++) {
            int pl = RepParts.lengthOf(parts[i]);
            if (srcBegin < pos + pl) {
                int start = Math.max(srcBegin, pos);
                int end = Math.min(srcEnd, pos + pl);
                parts[i].getChars(start - pos, end - pos, dst, offset);
                offset += end - start;
            }
            pos += pl;
        }
    }

    @Override
    public char[] toCharArray() {
        char[] out = new char[length];
        getChars(0, length, out, 0);
        return out;
    }

    private String materializeFlat() {
        char[] chars = new char[length];
        getChars(0, length, chars, 0);
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
            for (String p : parts) {
                e.part(p);
            }
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
        // Only the subrange, per part (no flat copy of the whole string).
        int pos = 0;
        String[] ps = parts;
        for (int i = 0; i < ps.length && pos < srcEnd; i++) {
            pos = RepParts.lowBytesSlice(ps[i], pos, srcBegin, srcEnd, dst, dstBegin);
        }
    }

    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        // Per part one System.arraycopy or inflate.
        int pos = dstBegin;
        for (String p : parts) {
            pos = RepParts.putPart(p, dst, pos, coder);
        }
    }

    /**
     * The builder JDK's ranged copy primitive ({@code AbstractStringBuilder.appendChars(.., String, ..)} and
     * {@code putStringAt} copy through it instead of reading {@code value()}): chars {@code [srcPos, srcPos + length)}
     * to {@code dst} at {@code dstBegin} in {@code dst}'s coder (the caller guarantees {@code coder >= coder()}).
     */
    @Override
    protected void getBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        int end = srcPos + length;
        int pos = 0;
        String[] ps = parts;
        for (int i = 0; i < ps.length && pos < end; i++) {
            pos = RepParts.putSlice(ps[i], pos, srcPos, end, dst, dstBegin, coder);
        }
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
    static boolean equalsSameType(ArrayLazyString a, ArrayLazyString b) {
        if (a == b) {
            return true;
        }
        String[] aParts = a.parts;
        String[] bParts = b.parts;
        if (aParts.length != bParts.length) {
            // A different split of possibly equal content: compare by content.
            return equalsFallback(a, b);
        }
        for (int i = 0; i < aParts.length; i++) {
            String ap = aParts[i];
            String bp = bParts[i];
            if (ap == bp) {
                continue;
            }
            if (RepParts.lengthOf(ap) != RepParts.lengthOf(bp)) {
                // A different split of possibly equal content: compare by content (checked before the coders)
                return equalsFallback(a, b);
            }
            byte aCoder = ap.coder();
            byte bCoder = bp.coder();
            byte[] av = ap.value();
            byte[] bv = bp.value();
            boolean eq;
            if (av == null || bv == null || aCoder != bCoder) {
                // A value-null part or a coder mismatch (equal content can differ in coder when a part is not
                // compact) compares by content
                eq = RepEquals.contentEquals(ap, bp);
            } else if (aCoder == LATIN1) {
                eq = latin1Equals(av, 0, bv, 0, av.length);
            } else {
                // utf16Equals takes a char count; av.length is the byte count
                eq = utf16Equals(av, 0, bv, 0, av.length >> 1);
            }
            if (!eq) {
                return false;
            }
        }
        return true;
    }

    @ForceInline
    static boolean equalsFallback(ArrayLazyString a, Object b) {
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
        return a.mismatch(s, len) == len; // per-part array compares
    }
}
