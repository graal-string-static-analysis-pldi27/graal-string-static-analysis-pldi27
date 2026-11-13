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

import com.oracle.svm.core.NeverInline;
import com.oracle.svm.core.SubstrateUtil;
import com.oracle.svm.core.Uninterruptible;

import java.nio.charset.Charset;

import jdk.internal.vm.annotation.ForceInline;

/**
 * Lazy Concat representation of a delimiter join: the logical string is
 * {@code e[0] + delim + e[1] + ... + e[N-1]}, stored as the {@code elements} array and one shared {@code delimiter}.
 * As in the other lazy reps the inherited {@code value} is null (any residual read NPEs: fail loud), the overridden
 * methods read the parts directly, and {@code coder()}/{@code isLatin1()} are inherited: the constructor passes the
 * JDK join's coder (the OR of the emitted parts' coders) to {@code super(coder)}. {@code length()} is a field;
 * {@code hashCode()} uses the inherited {@code hash}/{@code hashIsZero} cache; {@code toString()} is inherited.
 *
 * <p>{@code equals}/{@code compareTo} walk the parts once (allocation-free, O(length)); {@code charAt} is a linear
 * walk over the parts, O(count) per call (no cached part offsets, so no extra field).
 *
 * <p><b>The joiner variant.</b> {@link #ofJoiner} (an admitted {@code StringJoiner.toString()}) stores the
 * {@code StringJoiner} itself in the {@code delimiter} slot and shares the joiner's only-growing {@code elts}; the
 * logical string is then {@code prefix + e[0] + delim + ... + e[N-1] + suffix}, read through
 * {@link Target_java_util_StringJoiner}. Every method that reads the delimiter tests {@code delimiter instanceof
 * String} once and otherwise runs a {@code joinerXxx} body that also walks the affixes, whose coders are ORed in.
 */
public class InterleavedStringArray extends String {

    private static final byte LATIN1 = 0;

    /**
     * The parts {@code elements[0, count)}. Either owned by this string (no other reference survives the factory), so
     * never written after construction; or ({@link #ofJoiner}) a StringJoiner's {@code elts}, shared with the joiner,
     * which the child proved only grows (writes at indices {@code >= count} or into a new array), so
     * {@code elements[0, count)} never changes either.
     */
    private final String[] elements;
    /** The number of parts ({@code <= elements.length}; the join factory hands over its growth array). */
    private final int count;
    /**
     * The delimiter {@code String}, or ({@link #ofJoiner}) the {@code StringJoiner} itself, whose final affixes and
     * delimiter are read through {@link #alias}. One slot for both keeps the object at 56 bytes. ({@code serial}: a rep
     * is never serialized as itself; String's serial form writes the chars.)
     */
    @SuppressWarnings("serial") private final Object delimiter;
    private final int length;

    private InterleavedStringArray(String[] ownedElements, int count, Object delimiter, byte coder, int length) {
        super(coder); // the join's exact coder: the inherited coder()/isLatin1() are correct
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.elements = ownedElements;
        this.count = count;
        this.delimiter = delimiter;
        this.length = length;
        this.hashIsZero = false;
    }

    /**
     * The JDK 25 {@code String.join} coder: the OR of the parts' coders, and the delimiter's only when emitted
     * ({@code count > 1}). {@link #createJoined} ORs in the affixes' coders.
     */
    private static byte computeCoder(String[] elements, int count, String delimiter) {
        byte c = count > 1 ? delimiter.coder() : LATIN1;
        for (int i = 0; i < count; i++) {
            if (elements[i] == null) {
                throw new NullPointerException("elements[" + i + "] is null");
            }
            c |= elements[i].coder();
        }
        return c;
    }

    /** The char length of the join; the JDK's overflow rule and message (the byte length must fit an int). */
    private static int computeLength(long affixes, String[] elements, int count, String delimiter, byte coder) {
        long len = affixes;
        if (count > 1) {
            len += (long) (count - 1) * RepParts.lengthOf(delimiter);
        }
        for (int i = 0; i < count; i++) {
            len += RepParts.lengthOf(elements[i]);
        }
        long bytes = len << coder;
        if (len < 0L || bytes != (int) bytes) {
            throw new OutOfMemoryError("Requested string length exceeds VM limit");
        }
        return (int) len;
    }

    /** A copying factory: the caller keeps {@code elements} (the concat lowering). */
    public static String create(String[] elements, String delimiter) {
        return createOwned(elements.clone(), elements.length, delimiter);
    }

    /**
     * The owning factory: {@code ownedElements[0, count)} are the (non-null) parts and the array is handed over, so the
     * caller must hold no other reference to it. {@code delimiter} must be non-null when {@code count > 1}; otherwise it
     * is never read (as in the JDK join) and is normalized to {@code ""}. An empty join gives the literal {@code ""}
     * (the JDK returns a fresh empty String; identity of empty results is out of scope), never an empty rep.
     */
    public static String createOwned(String[] ownedElements, int count, String delimiter) {
        if (count < 0 || count > ownedElements.length) {
            throw new IllegalArgumentException("count " + count + ", length " + ownedElements.length);
        }
        if (count <= 1) {
            delimiter = ""; // unobservable: charAt/getChars read its length, coder/length/hash/equals skip it
        } else if (delimiter == null) {
            throw new NullPointerException("delimiter"); // no Objects.requireNonNull: a rep-typed value never leaves rep code
        }
        byte coder = computeCoder(ownedElements, count, delimiter);
        int len = computeLength(0L, ownedElements, count, delimiter, coder);
        if (len == 0) {
            return "";
        }
        return new InterleavedStringArray(ownedElements, count, delimiter, coder, len);
    }

    /**
     * The smallest joiner {@code len} (parts and delimiters, without affixes) at which {@link #ofJoiner} mints an
     * interleaved string. The rep is 56 bytes (the joiner's array is shared); the JDK result is
     * {@code 24 + align8(16 + bytes)} with {@code bytes >= len}. At {@code len >= 9} that is at least 56, so the rep
     * never allocates more than the JDK (a tie at 9..16 Latin-1 bytes, where the rep is still faster to create); at 8 a
     * Latin-1 JDK result is 48 bytes. {@code len} can exceed the joined length only after a caught OutOfMemoryError in
     * {@code add} (see {@link #createJoined}).
     */
    public static final int JOINER_MIN_CHARS = 9;

    /**
     * The replacement of an admitted {@code StringJoiner.toString()}. Admission means the child proved the joiner only
     * grows: {@code add} writes {@code elts[size++]} or copies into a new array, so {@code elts[0, size)} never changes
     * after this snapshot; a joiner that is the argument of {@code merge} (the one in-place rewrite) is rejected. A
     * join below {@link #JOINER_MIN_CHARS} is the JDK body; otherwise an interleaved string over the joiner's array.
     * <p>The inlined fast path tests {@code len} only. In JDK 25 {@code len} grows only in {@code add}, with
     * {@code size++}, so size 0 normally means {@code len == 0}; size 0 is still decided in {@link #createJoined},
     * since an {@code add} that throws its {@code OutOfMemoryError} after adding the delimiter's length leaves
     * {@code len > 0} at size 0.
     */
    @ForceInline
    public static String ofJoiner(java.util.StringJoiner joiner) {
        if (alias(joiner).len < JOINER_MIN_CHARS) {
            return joiner.toString();
        }
        return createJoined(joiner);
    }

    /** {@code joiner} (a StringJoiner, never a rep) as its field alias; the only cast to the alias. */
    private static Target_java_util_StringJoiner alias(Object joiner) {
        return SubstrateUtil.cast(joiner, Target_java_util_StringJoiner.class);
    }

    /**
     * Pure (pinned by JUnit): whether {@link #ofJoiner} mints the rep for a joiner's {@code size} and {@code len}: not
     * for size 0 (the JDK's {@code emptyValue} identity or {@code prefix + suffix}) nor below {@link #JOINER_MIN_CHARS}.
     */
    @ForceInline
    public static boolean joinerMintsRep(int size, int len) {
        return size != 0 && len >= JOINER_MIN_CHARS;
    }

    /**
     * The joiner's join over its shared, only-growing array, with the JDK's coder, length and overflow rule.
     * {@code size} is read before {@code elts}, in the order of the JDK's {@code toString}.
     */
    @NeverInline("the rep construction stays out of line (ofJoiner's fast path inlines)")
    private static String createJoined(java.util.StringJoiner joiner) {
        Target_java_util_StringJoiner j = alias(joiner);
        int count = j.size;
        if (!joinerMintsRep(count, j.len)) {
            return joiner.toString();
        }
        String[] elements = j.elts;
        String prefix = j.prefix;
        String suffix = j.suffix;
        byte coder = (byte) (computeCoder(elements, count, j.delimiter) | prefix.coder() | suffix.coder());
        int len = computeLength((long) RepParts.lengthOf(prefix) + RepParts.lengthOf(suffix), elements, count, j.delimiter, coder);
        if (len == 0) {
            /*
             * A rep is never empty, and len is not a lower bound of the join: after a caught OutOfMemoryError in
             * StringJoiner.add, size can be 1 with elts[0] == "" while len counts the failed add.
             */
            return joiner.toString();
        }
        return new InterleavedStringArray(elements, count, joiner, coder, len);
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

    /** A linear part walk, O(count) per call (no {@code charAt} loop over an interleaved string is expected). */
    @Override
    public char charAt(int index) {
        int len = length;
        if (index < 0 || index >= len) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + len);
        }
        if (!(delimiter instanceof String delim)) {
            return joinerCharAt(index);
        }
        int remaining = index;
        int delimLen = RepParts.lengthOf(delim);
        for (int i = 0; i < count; i++) {
            int el = RepParts.lengthOf(elements[i]);
            if (remaining < el) {
                return RepParts.charAtOf(elements[i], remaining);
            }
            remaining -= el;
            if (i < count - 1) {
                if (remaining < delimLen) {
                    return RepParts.charAtOf(delim, remaining);
                }
                remaining -= delimLen;
            }
        }
        throw new InternalError("unreachable");
    }

    /** {@link #charAt} of a joiner's join ({@code index} in range). */
    private char joinerCharAt(int index) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String prefix = j.prefix;
        String delim = j.delimiter;
        int remaining = index;
        int pl = RepParts.lengthOf(prefix);
        if (remaining < pl) {
            return RepParts.charAtOf(prefix, remaining);
        }
        remaining -= pl;
        int delimLen = RepParts.lengthOf(delim);
        for (int i = 0; i < count; i++) {
            int el = RepParts.lengthOf(elements[i]);
            if (remaining < el) {
                return RepParts.charAtOf(elements[i], remaining);
            }
            remaining -= el;
            if (i < count - 1) {
                if (remaining < delimLen) {
                    return RepParts.charAtOf(delim, remaining);
                }
                remaining -= delimLen;
            }
        }
        return RepParts.charAtOf(j.suffix, remaining); // index < length: inside the suffix
    }

    /**
     * The first index in {@code [0, n)} where this string and {@code s} differ, else {@code n}
     * ({@code n <= min(length, s.length())}): one walk comparing each part with its slice of {@code s}, O(n).
     */
    private int mismatch(String s, int n) {
        if (!(delimiter instanceof String delim)) {
            return joinerMismatch(s, n);
        }
        String[] es = elements;
        int last = count - 1;
        int pos = 0;
        for (int i = 0; i <= last && pos < n; i++) {
            pos = RepParts.walk(es[i], pos, s, n);
            if (pos >= 0 && i < last) {
                pos = RepParts.walk(delim, pos, s, n);
            }
            if (pos < 0) {
                return -pos - 1;
            }
        }
        return n;
    }

    /** {@link #mismatch} of a joiner's join (the affixes walked too). */
    private int joinerMismatch(String s, int n) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String delim = j.delimiter;
        int pos = RepParts.walk(j.prefix, 0, s, n);
        if (pos < 0) {
            return -pos - 1;
        }
        String[] es = elements;
        int last = count - 1;
        for (int i = 0; i <= last && pos < n; i++) {
            pos = RepParts.walk(es[i], pos, s, n);
            if (pos >= 0 && i < last) {
                pos = RepParts.walk(delim, pos, s, n);
            }
            if (pos < 0) {
                return -pos - 1;
            }
        }
        if (pos < n) {
            pos = RepParts.walk(j.suffix, pos, s, n);
            if (pos < 0) {
                return -pos - 1;
            }
        }
        return n;
    }

    @Override
    public boolean equals(Object o) {
        return equalsFallback(this, o);
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            if (delimiter instanceof String delim) {
                for (int i = 0; i < count; i++) {
                    int elLen = RepParts.lengthOf(elements[i]);
                    int p = 1;
                    for (int j = 0; j < elLen; j++) {
                        p *= 31;
                    }
                    h = h * p + elements[i].hashCode();
                    if (i < count - 1) {
                        int delimLen = RepParts.lengthOf(delim);
                        int pd = 1;
                        for (int j = 0; j < delimLen; j++) {
                            pd *= 31;
                        }
                        h = h * pd + delim.hashCode();
                    }
                }
            } else {
                h = joinerHash();
            }
            if (h == 0) {
                hashIsZero = true;
            } else {
                hash = h;
            }
        }
        return h;
    }

    /** The String hash of a joiner's join (the affixes folded in). */
    private int joinerHash() {
        Target_java_util_StringJoiner j = alias(delimiter);
        String delim = j.delimiter;
        int h = foldHash(0, j.prefix);
        for (int i = 0; i < count; i++) {
            h = foldHash(h, elements[i]);
            if (i < count - 1) {
                h = foldHash(h, delim);
            }
        }
        return foldHash(h, j.suffix);
    }

    /** {@code h} extended by the chars of {@code s} (String's polynomial hash; {@code ""} leaves it unchanged). */
    private static int foldHash(int h, String s) {
        int n = s.length();
        if (n == 0) {
            return h;
        }
        int p = 1;
        for (int j = 0; j < n; j++) {
            p *= 31;
        }
        return h * p + s.hashCode();
    }

    /**
     * The inherited {@code compareTo} reads the null {@code value()}. This one is exact and total over plain Strings,
     * flat reps and value-null reps; {@code String.maybeCustomStringCompareTo} deflects a rep argument here.
     */
    @Override
    public int compareTo(String anotherString) {
        // First differing char, else the length difference (exactly negated on the argument side, as RepCompareTo
        // requires)
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
        int n = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - n) {
            throw new StringIndexOutOfBoundsException("offset " + dstBegin + ", count " + n + ", length " + dst.length);
        }
        if (!(delimiter instanceof String delim)) {
            joinerGetChars(srcBegin, srcEnd, dst, dstBegin);
            return;
        }
        int offset = dstBegin;
        int pos = 0;
        int delimLen = RepParts.lengthOf(delim);
        for (int i = 0; i < this.count && pos < srcEnd; i++) {
            int el = RepParts.lengthOf(elements[i]);
            if (srcBegin < pos + el) {
                int start = Math.max(srcBegin, pos);
                int end = Math.min(srcEnd, pos + el);
                elements[i].getChars(start - pos, end - pos, dst, offset);
                offset += end - start;
            }
            pos += el;
            if (i < this.count - 1 && pos < srcEnd && srcEnd > pos && srcBegin < pos + delimLen) {
                int start = Math.max(srcBegin, pos);
                int end = Math.min(srcEnd, pos + delimLen);
                delim.getChars(start - pos, end - pos, dst, offset);
                offset += end - start;
            }
            pos += delimLen;
        }
    }

    /** {@link #getChars} of a joiner's join (the range already checked). */
    private void joinerGetChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String prefix = j.prefix;
        String delim = j.delimiter;
        String suffix = j.suffix;
        int offset = dstBegin;
        int pl = RepParts.lengthOf(prefix);
        if (srcBegin < pl) {
            int end = Math.min(srcEnd, pl);
            prefix.getChars(srcBegin, end, dst, offset);
            offset += end - srcBegin;
        }
        int pos = pl;
        int delimLen = RepParts.lengthOf(delim);
        for (int i = 0; i < this.count && pos < srcEnd; i++) {
            int el = RepParts.lengthOf(elements[i]);
            if (srcBegin < pos + el) {
                int start = Math.max(srcBegin, pos);
                int end = Math.min(srcEnd, pos + el);
                elements[i].getChars(start - pos, end - pos, dst, offset);
                offset += end - start;
            }
            pos += el;
            if (i < this.count - 1 && pos < srcEnd && srcEnd > pos && srcBegin < pos + delimLen) {
                int start = Math.max(srcBegin, pos);
                int end = Math.min(srcEnd, pos + delimLen);
                delim.getChars(start - pos, end - pos, dst, offset);
                offset += end - start;
            }
            pos += delimLen;
        }
        int sufStart = length - RepParts.lengthOf(suffix);
        if (srcEnd > sufStart) {
            int start = Math.max(srcBegin, sufStart);
            suffix.getChars(start - sufStart, srcEnd - sufStart, dst, offset);
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
     * The JDK's UTF-8 / ISO-8859-1 / US-ASCII encoding straight from the parts; {@code null} for any other charset or
     * an oversized UTF-8 result.
     */
    private byte[] encode(int kind) {
        if (kind < 0) {
            return null;
        }
        if (!(delimiter instanceof String delim)) {
            return joinerEncode(kind);
        }
        RepParts.Enc e = new RepParts.Enc(kind, length);
        while (e.pass()) {
            int last = count - 1;
            for (int i = 0; i <= last; i++) {
                e.part(elements[i]);
                if (i < last) {
                    e.part(delim);
                }
            }
        }
        return e.result();
    }

    /** {@link #encode} of a joiner's join ({@code kind >= 0}). */
    private byte[] joinerEncode(int kind) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String delim = j.delimiter;
        RepParts.Enc e = new RepParts.Enc(kind, length);
        while (e.pass()) {
            e.part(j.prefix);
            int last = count - 1;
            for (int i = 0; i <= last; i++) {
                e.part(elements[i]);
                if (i < last) {
                    e.part(delim);
                }
            }
            e.part(j.suffix);
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
        if (!(delimiter instanceof String delim)) {
            joinerLowBytes(srcBegin, srcEnd, dst, dstBegin);
            return;
        }
        // Only the subrange, per part and delimiter (no flat copy of the whole string).
        int pos = 0;
        int last = count - 1;
        for (int i = 0; i <= last && pos < srcEnd; i++) {
            pos = RepParts.lowBytesSlice(elements[i], pos, srcBegin, srcEnd, dst, dstBegin);
            if (i < last) {
                pos = RepParts.lowBytesSlice(delim, pos, srcBegin, srcEnd, dst, dstBegin);
            }
        }
    }

    /** The deprecated {@code getBytes(int, int, byte[], int)} of a joiner's join (the range already checked). */
    private void joinerLowBytes(int srcBegin, int srcEnd, byte[] dst, int dstBegin) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String delim = j.delimiter;
        int pos = RepParts.lowBytesSlice(j.prefix, 0, srcBegin, srcEnd, dst, dstBegin);
        int last = count - 1;
        for (int i = 0; i <= last && pos < srcEnd; i++) {
            pos = RepParts.lowBytesSlice(elements[i], pos, srcBegin, srcEnd, dst, dstBegin);
            if (i < last) {
                pos = RepParts.lowBytesSlice(delim, pos, srcBegin, srcEnd, dst, dstBegin);
            }
        }
        if (pos < srcEnd) {
            RepParts.lowBytesSlice(j.suffix, pos, srcBegin, srcEnd, dst, dstBegin);
        }
    }

    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        if (!(delimiter instanceof String delim)) {
            joinerGetBytes(dst, dstBegin, coder);
            return;
        }
        // Per part and delimiter one System.arraycopy or inflate.
        int pos = dstBegin;
        int last = count - 1;
        for (int i = 0; i <= last; i++) {
            pos = RepParts.putPart(elements[i], dst, pos, coder);
            if (i < last) {
                pos = RepParts.putPart(delim, dst, pos, coder);
            }
        }
    }

    /** {@link #getBytes(byte[], int, byte)} of a joiner's join. */
    private void joinerGetBytes(byte[] dst, int dstBegin, byte coder) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String prefix = j.prefix;
        String delim = j.delimiter;
        int pos = RepParts.putPart(prefix, dst, dstBegin, coder);
        int last = count - 1;
        for (int i = 0; i <= last; i++) {
            pos = RepParts.putPart(elements[i], dst, pos, coder);
            if (i < last) {
                pos = RepParts.putPart(delim, dst, pos, coder);
            }
        }
        RepParts.putPart(j.suffix, dst, pos, coder);
    }

    /**
     * The builder JDK's ranged copy primitive ({@code AbstractStringBuilder.appendChars(.., String, ..)} and
     * {@code putStringAt} copy through it instead of reading {@code value()}): chars {@code [srcPos, srcPos + length)}
     * to {@code dst} at {@code dstBegin} in {@code dst}'s coder (the caller guarantees {@code coder >= coder()}).
     */
    @Override
    protected void getBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        if (!(delimiter instanceof String delim)) {
            joinerGetBytes(dst, srcPos, dstBegin, coder, length);
            return;
        }
        int end = srcPos + length;
        int pos = 0;
        int last = count - 1;
        for (int i = 0; i <= last && pos < end; i++) {
            pos = RepParts.putSlice(elements[i], pos, srcPos, end, dst, dstBegin, coder);
            if (i < last) {
                pos = RepParts.putSlice(delim, pos, srcPos, end, dst, dstBegin, coder);
            }
        }
    }

    /** The ranged {@link #getBytes(byte[], int, int, byte, int)} of a joiner's join. */
    private void joinerGetBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        Target_java_util_StringJoiner j = alias(delimiter);
        String delim = j.delimiter;
        int end = srcPos + length;
        int pos = RepParts.putSlice(j.prefix, 0, srcPos, end, dst, dstBegin, coder);
        int last = count - 1;
        for (int i = 0; i <= last && pos < end; i++) {
            pos = RepParts.putSlice(elements[i], pos, srcPos, end, dst, dstBegin, coder);
            if (i < last) {
                pos = RepParts.putSlice(delim, pos, srcPos, end, dst, dstBegin, coder);
            }
        }
        if (pos < end) {
            RepParts.putSlice(j.suffix, pos, srcPos, end, dst, dstBegin, coder);
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
    static boolean equalsSameType(InterleavedStringArray a, InterleavedStringArray b) {
        if (a == b) {
            return true;
        }
        if (!(a.delimiter instanceof String aDelim) || !(b.delimiter instanceof String bDelim)) {
            return equalsFallback(a, b); // a joiner's join (affixes): compare by content
        }
        String[] aElems = a.elements;
        String[] bElems = b.elements;
        int n = a.count;
        if (n != b.count || n > 1 && RepParts.lengthOf(aDelim) != RepParts.lengthOf(bDelim)) {
            // A different split of possibly equal content: compare by content.
            return equalsFallback(a, b);
        }
        for (int i = 0; i < n; i++) {
            if (RepParts.lengthOf(aElems[i]) != RepParts.lengthOf(bElems[i])) {
                // As above; with every length equal the pieces align and the piecewise compare is exact
                return equalsFallback(a, b);
            }
        }
        if (n > 1 && !childEquals(aDelim, bDelim)) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            if (!childEquals(aElems[i], bElems[i])) {
                return false;
            }
        }
        return true;
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
        if (av.length != bv.length) {
            return false;
        }
        if (aCoder == LATIN1) {
            return latin1Equals(av, 0, bv, 0, av.length);
        }
        // utf16Equals takes a char count; av.length is the byte count
        return utf16Equals(av, 0, bv, 0, av.length >> 1);
    }

    @ForceInline
    static boolean equalsFallback(InterleavedStringArray a, Object b) {
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
        return a.mismatch(s, len) == len; // sequential, O(len)
    }
}
