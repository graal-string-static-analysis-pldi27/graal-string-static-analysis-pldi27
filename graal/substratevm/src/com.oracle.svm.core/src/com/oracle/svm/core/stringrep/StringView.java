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
import java.util.Arrays;
import java.util.Locale;

import org.graalvm.nativeimage.ImageInfo;

import com.oracle.svm.core.SubstrateUtil;
import com.oracle.svm.core.Uninterruptible;

import jdk.internal.vm.annotation.ForceInline;

/**
 * String View representation: a {@code String} subclass over a sub-range of a shared backing byte array (zero copy
 * at construction). Three new fields record it: {@code backing} (the shared array), {@code offset} and {@code length}
 * (char units). The constructor calls the builder-JDK constructor {@code String(byte coder)}, which leaves the
 * inherited {@code value} null and sets the inherited {@code coder}.
 *
 * <p><b>value = null fast-fail.</b> There is no {@code value()} override, so any inherited method that reaches
 * {@code value()} throws an NPE. The analysis must ensure only overridden methods are reached on a view; an NPE is
 * an analysis gap, never silent corruption. Why not override {@code value()} with a materializing fallback: the
 * accessor sweep routes every {@code value} read in {@code java.lang.String} through {@code value()}, so under
 * context-insensitive points-to an override would put a String-vs-StringView type check at every
 * {@code value()} call site of the image as soon as any view is instantiated, including hot paths that only see plain
 * Strings.
 *
 * <p>The overridden methods read {@code backing[offset ..]} directly and never touch {@code value}: array compares
 * and scans of the range against a plain {@code String} or a same-coder view (equals, hashCode, compareTo,
 * startsWith/endsWith, indexOf/lastIndexOf, getChars, the protected {@code getBytes} copy primitives used by
 * {@code StringBuilder.append}), {@code charAt}-based loops or {@link RepEquals#contentEquals} for any other argument,
 * the UTF-8/ISO-8859-1/US-ASCII encodings straight from the range, and a materialized flat copy
 * ({@code materializeRange}) for the rest. {@code substring} returns {@code this} for the full range (the JDK's rule)
 * and a plain copy otherwise; {@code trim}/{@code strip*} nest through {@link #createView(StringView, int, int)}.
 * {@code maybeCustomStringEquals} delegates to {@link #equals(Object)}, as the inherited body would NPE.
 * {@code toString} is not overridden (the inherited body returns {@code this}; no rep overrides it, since an override
 * makes every {@code toString} call site polymorphic). {@code coder()}/{@code isLatin1()} are inherited and correct:
 * the inherited {@code coder} matches the backing array's encoding, and all byte-offset math scales by it
 * ({@code StringViewMethodTest} covers UTF-16 views).
 *
 * <p>The coder is exact: every substring factory goes through {@link #view}, which returns the compact Latin-1 copy
 * (the JVM's {@code substring} result) instead of a UTF-16 view of a Latin-1-only range. The one exception is a racy
 * builder snapshot with a stale {@code maybeLatin1 = false} (see {@link #ofBuilderSnapshot}), where the JDK's own
 * {@code toString} returns a non-compact String too.
 */
public class StringView extends String {

    private static final byte LATIN1 = 0;
    private static final byte UTF16 = 1;

    private static final int HI_BYTE_SHIFT = computeHiByteShift();
    private static final int LO_BYTE_SHIFT = 8 - HI_BYTE_SHIFT;

    private final byte[] backing;
    private final int offset;
    private final int length;

    private StringView(byte[] shared, byte coder, int offset, int length) {
        super(coder);
        assert length > 0; // a rep is never empty (the factories return a stock String for an empty result)
        this.backing = shared;
        this.offset = offset;
        this.length = length;
    }

    /**
     * The view of {@code parent[from, end)}, coder-exact ({@link #view}): a Latin-1-only range of a UTF-16 backing
     * gives the compact Latin-1 copy the JVM's {@code substring} allocates, never a UTF-16 view of Latin-1 chars (which
     * would inflate an appending builder or a concatenation into a non-compact String not {@code equals} to the
     * literal). The result is a {@code StringView} or a plain compact {@code String}.
     */
    public static String create(String parent, int from, int end) {
        if (parent.getClass() == String.class) {
            // An exact String: its length without the virtual length() call (reps override length()).
            byte[] value = parent.value();
            byte coder = parent.coder();
            int length = value.length >> coder;
            if (from < 0 || end > length || from > end) {
                throw storedOutOfBounds(from, end, length);
            }
            return view(value, coder, from, end - from);
        }
        if (from < 0 || end > parent.length() || from > end) {
            throw new StringIndexOutOfBoundsException(
                            "from " + from + ", end " + end + ", length " + parent.length());
        }
        if (parent instanceof StringView sv) {
            return view(sv.backing, sv.coder(), sv.offset + from, end - from);
        }
        return view(parent.value(), parent.coder(), from, end - from);
    }

    /**
     * Every substring view is made here. A Latin-1-only range of a UTF-16 backing yields the compact copy
     * ({@code utf16NewString} = JDK {@code StringUTF16.newString}); otherwise the zero-copy view. An empty range gives
     * {@code ""}, never an empty view: the concat factories' emptiness tests rely on "a rep is never empty".
     */
    @ForceInline
    private static String view(byte[] backing, byte coder, int off, int len) {
        if (len == 0) {
            return ""; // a rep is never empty; the JDK substring's StringLatin1/UTF16.newString len-0 result
        }
        if (coder == UTF16 && utf16RangeIsLatin1(backing, off, len)) {
            return utf16NewString(backing, off, len);
        }
        return new StringView(backing, coder, off, len);
    }

    /** True when the UTF-16 chars {@code a[off, off + len)} are all Latin-1; exits early as JDK 25 {@code compress}. */
    static boolean utf16RangeIsLatin1(byte[] a, int off, int len) {
        for (int i = 0; i < len; i++) {
            if (utf16CharAt(a, off, i) > 0xFF) {
                return false;
            }
        }
        return true;
    }

    /**
     * The 1-arg {@code substring(int)} form; {@code length()} is virtual, so this is correct for every parent. A null
     * receiver NPEs, as the replaced call. Unlike the JDK's {@code substring(0) == this}, a new view is returned
     * (identity uses are out of scope).
     */
    public static String create(String parent, int from) {
        if (parent.getClass() == String.class) {
            return create(parent, from, parent.value().length >> parent.coder());
        }
        return create(parent, from, parent.length());
    }

    /**
     * A view sharing the builder's array over {@code [0, sb.length())}, zero copy. The builder must not be modified
     * below {@code count} afterwards (see {@link #underThreshold} for why the admitted sites guarantee that).
     *
     * @return the view, the compact copy of a Latin-1-only UTF-16 builder, or on the copy branch (under half full,
     *         torn) the exact {@code String} of the JDK's {@code toString}
     */
    public static String create(StringBuilder sb) {
        return ofBuilderSnapshot(getBuilderValue(sb), getBuilderCoder(sb), getBuilderCount(sb), builderMaybeLatin1(sb));
    }

    /**
     * {@link #create(StringBuilder)} for a {@code StringBuffer}; the field reads happen under its monitor, so the
     * snapshot is never torn.
     */
    public static String create(StringBuffer sb) {
        synchronized (sb) {
            return ofBuilderSnapshot(getBuilderValue(sb), getBuilderCoder(sb), lockedBufferCount(sb), builderMaybeLatin1(sb));
        }
    }

    /**
     * The view of a {@code StringWriter}'s content: {@code StringWriter.toString()} is {@code buf.toString()} and
     * {@code getBuffer()} returns that {@code buf}, so this is {@link #create(StringBuffer)} over it. No class check:
     * the parent lowers only an extraction whose profile entry names {@code java.io.StringWriter} as the receivers'
     * exact class, stated to points-to with the analysis-only exact filter. A null receiver NPEs as the original call.
     */
    public static String create(java.io.StringWriter w) {
        return create(w.getBuffer());
    }

    /**
     * The stack-confined variant of {@link #create(StringBuilder)}, lowered only at a
     * {@code STRING_VIEW ACCUMULATOR_VIEW_SHARED} entry (the child saw no escape event of the extracted string). It
     * skips the occupancy check ({@link #underThreshold}, only a memory-retention policy): a confined string retains
     * the array no longer than its frames. The torn-snapshot copy stays unconditional.
     */
    public static String createSkipCheck(StringBuilder sb) {
        return ofBuilderSnapshot(getBuilderValue(sb), getBuilderCoder(sb), getBuilderCount(sb), builderMaybeLatin1(sb), false);
    }

    /** {@link #createSkipCheck(StringBuilder)} for a {@code StringBuffer}: the same snapshot under its monitor. */
    public static String createSkipCheck(StringBuffer sb) {
        synchronized (sb) {
            return ofBuilderSnapshot(getBuilderValue(sb), getBuilderCoder(sb), lockedBufferCount(sb), builderMaybeLatin1(sb), false);
        }
    }

    /** {@link #createSkipCheck(StringBuilder)} for a {@code java.io.StringWriter}: over its {@code buf}. */
    public static String createSkipCheck(java.io.StringWriter w) {
        return createSkipCheck(w.getBuffer());
    }

    /**
     * {@code sb.length()} for a caller that holds {@code sb}'s monitor: the field {@code count} directly (through the
     * {@link Target_java_lang_AbstractStringBuilder} alias), the same value without the synchronized
     * {@code StringBuffer.length()} re-entering the monitor (the compiler keeps that nested lock). Outside an image
     * (hosted JUnit, no alias) {@code getBuilderCount}.
     */
    @ForceInline
    static int lockedBufferCount(StringBuffer sb) {
        if (ImageInfo.inImageRuntimeCode()) {
            return SubstrateUtil.cast(sb, Target_java_lang_AbstractStringBuilder.class).count;
        }
        return getBuilderCount(sb);
    }

    /**
     * The builder's JDK field {@code AbstractStringBuilder.maybeLatin1} (through the
     * {@link Target_java_lang_AbstractStringBuilder} alias). The factories read it last, after {@code value},
     * {@code coder} and {@code count} (left-to-right argument evaluation), the JDK's order in
     * {@code String(AbstractStringBuilder, Void)}. Outside an image (hosted JUnit) the answer is {@code true}, i.e.
     * the scan, which is never wrong.
     */
    @ForceInline
    static boolean builderMaybeLatin1(Object asb) {
        if (ImageInfo.inImageRuntimeCode()) {
            return SubstrateUtil.cast(asb, Target_java_lang_AbstractStringBuilder.class).maybeLatin1;
        }
        return true;
    }

    /**
     * The builder views' body over one snapshot of {@code (value, coder, count, maybeLatin1)}, each field read once by
     * the caller. An unsynchronized {@code StringBuilder} raced by another thread can yield a torn snapshot (JDK 25
     * {@code append} writes {@code coder} before {@code value}: an old Latin-1 array paired with UTF16, or a
     * {@code count} past the array). Such a snapshot is never shared: when {@code (count << coder) > value.length} it
     * takes the copy branch (zero-padded, like the JDK's {@code toString} under the same race), so every read of the
     * view stays inside its own array. Public only so the hosted JUnit can pin the torn case.
     *
     * <p>Coder-exact by the JDK's rule ({@code String(AbstractStringBuilder, Void)}): a UTF-16 builder is scanned for
     * compression only when {@code maybeLatin1} is set. Without it the JDK guarantees a char above 0xFF in
     * {@code [0, count)} (only the ops that set it can remove one) and does not compress, so the view is made as is.
     * Race: {@code maybeLatin1} is read last, as the JDK reads it; a stale {@code false} with newer content can only
     * miss a compression, which the JDK's {@code toString} under the same interleaving misses too. A stale {@code true}
     * only scans (the scan result is the JDK's compress result on the snapshot).
     */
    @ForceInline
    public static String ofBuilderSnapshot(byte[] value, byte coder, int count, boolean maybeLatin1) {
        return ofBuilderSnapshot(value, coder, count, maybeLatin1, true);
    }

    /**
     * The snapshot body with the occupancy check as an argument: {@code trim} = true copies a builder under half full
     * in bytes; false (the {@code createSkipCheck} factories) shares at any occupancy. A torn snapshot and an empty
     * builder ({@code ""}) are handled first, whatever {@code trim} says. The copy branch returns an exact
     * {@code java.lang.String} by the JDK's {@code toString} rule ({@link #builderCopy}), not a view over a private
     * copy. Inlining parity: the copy branch makes one {@code Arrays.copyOf} call, as in the JDK's {@code toString}.
     */
    @ForceInline
    public static String ofBuilderSnapshot(byte[] value, byte coder, int count, boolean maybeLatin1, boolean trim) {
        if (count == 0) {
            return "";
        }
        int usedBytes = count << coder;
        if (usedBytes > value.length || trim && underThreshold(usedBytes, value.length)) { // torn -> copy (unconditional)
            return builderCopy(value, coder, count, maybeLatin1);
        }
        if (!maybeLatin1) {
            return new StringView(value, coder, 0, count); // JDK toString does not compress either
        }
        return view(value, coder, 0, count);
    }

    /**
     * The builder's JDK 25 {@code toString} result on the snapshot ({@code String(AbstractStringBuilder, Void)}):
     * {@code ""} when empty; a Latin-1 copy for a Latin-1 builder; for a UTF-16 builder the compressed copy when
     * {@code maybeLatin1} is set and every char is Latin-1, else the UTF-16 bytes as they are. The class is exactly
     * {@code java.lang.String}. A torn snapshot is zero-padded to its used bytes, as the JDK's {@code copyOfRange}
     * under the same race. In the image the non-compressing cases make one copy shared by the JDK's value-sharing
     * constructor {@code String(byte[], byte)} (alias {@link Target_java_lang_String_StringRep}). Outside an image
     * (hosted JUnit, where that alias has no body) the JDK's {@code newString} helpers are used; the no-
     * {@code maybeLatin1} case then attempts a compression, which fails under the JDK's invariant and makes the same
     * copy. Force-inlined into the snapshot, which only the {@code create*} builder factories inline (none of them is
     * force-inlined): the copy itself stays the one {@code Arrays.copyOf} call, as in the
     * JDK's {@code toString}.
     */
    @ForceInline
    static String builderCopy(byte[] value, byte coder, int count, boolean maybeLatin1) {
        if (count == 0) {
            return "";
        }
        int usedBytes = count << coder;
        if ((coder == LATIN1 || !maybeLatin1) && ImageInfo.inImageRuntimeCode()) {
            // RepEscapeTest: a checkcast of the fresh plain String, no call out of the rep classes
            return (String) (Object) new Target_java_lang_String_StringRep(Arrays.copyOf(value, usedBytes), coder);
        }
        byte[] a = usedBytes > value.length ? Arrays.copyOf(value, usedBytes) : value; // a byte count
        return coder == LATIN1 ? latin1NewString(a, 0, count) : utf16NewString(a, 0, count);
    }

    /**
     * The stored variant of {@link #create(String, int, int)}, lowered at a {@code STRING_VIEW STORED} entry (the
     * substring is stored into the heap, so it may outlive the frame and retain the backing array): see
     * {@link #storedView}.
     */
    public static String createStored(String parent, int from, int end) {
        if (parent.getClass() == String.class) {
            // An exact String: its length without the virtual length() call (reps override length()).
            byte[] value = parent.value();
            byte coder = parent.coder();
            int length = value.length >> coder;
            if (from < 0 || end > length || from > end) {
                throw storedOutOfBounds(from, end, length);
            }
            return storedView(value, coder, from, end - from);
        }
        if (from < 0 || end > parent.length() || from > end) {
            throw storedOutOfBounds(from, end, parent.length());
        }
        if (parent instanceof StringView sv) {
            return storedView(sv.backing, sv.coder(), sv.offset + from, end - from);
        }
        return storedView(parent.value(), parent.coder(), from, end - from);
    }

    /** The 1-arg form of {@link #createStored(String, int, int)} (the end is the receiver's length). */
    public static String createStored(String parent, int from) {
        if (parent.getClass() == String.class) {
            return createStored(parent, from, parent.value().length >> parent.coder());
        }
        return createStored(parent, from, parent.length());
    }

    private static StringIndexOutOfBoundsException storedOutOfBounds(int from, int end, int length) {
        return new StringIndexOutOfBoundsException("from " + from + ", end " + end + ", length " + length);
    }

    /** The STORED variant of {@link #createView(StringView, int, int)} (an exact-StringView receiver). */
    public static String createViewStored(StringView parent, int from, int end) {
        if (from < 0 || end > parent.length || from > end) {
            throw new StringIndexOutOfBoundsException(
                            "from " + from + ", end " + end + ", length " + parent.length);
        }
        return storedView(parent.backing, parent.coder(), parent.offset + from, end - from);
    }

    /** The 1-arg form of {@link #createViewStored(StringView, int, int)}. */
    public static String createViewStored(StringView parent, int from) {
        return createViewStored(parent, from, parent.length);
    }

    /**
     * The stored-site body: a range under half of its backing array (a stored view would retain the rest) gives the
     * JDK's {@code substring} result ({@link #rangeCopy}, inline: the same code as {@code substring}'s copy); otherwise
     * {@link #view}. No minimum length: a view of 1..8 bytes costs the same 56 B as a copy and is faster to create.
     */
    @ForceInline
    static String storedView(byte[] backing, byte coder, int off, int len) {
        int bytes = len << coder;
        if (underThreshold(bytes, backing.length)) {
            return rangeCopy(backing, coder, off, len);
        }
        return view(backing, coder, off, len);
    }

    /**
     * The JDK {@code substring} body on {@code backing[off, off + len)}: an exact {@code java.lang.String}. Never calls
     * {@code String.substring} (a replaced call could re-enter a factory).
     */
    @ForceInline
    static String rangeCopy(byte[] backing, byte coder, int off, int len) {
        if (len == 0) {
            return "";
        }
        return coder == LATIN1 ? latin1NewString(backing, off, len) : utf16NewString(backing, off, len);
    }

    public static String createView(StringView parent, int from, int end) {
        if (from < 0 || end > parent.length || from > end) {
            throw new StringIndexOutOfBoundsException(
                            "from " + from + ", end " + end + ", length " + parent.length);
        }
        return view(parent.backing, parent.coder(), parent.offset + from, end - from); // coder-exact
    }

    /** The 1-arg form of {@link #createView(StringView, int, int)}. */
    public static String createView(StringView parent, int from) {
        return createView(parent, from, parent.length);
    }

    private static int computeHiByteShift() {
        String probe = "\u0100";
        if (probe.coder() != UTF16) {
            throw new InternalError("StringView endianness probe: expected UTF-16 coder");
        }
        byte[] b = probe.value();
        if (b[0] != 0x01 && b[1] != 0x01) {
            throw new InternalError("StringView endianness probe: unexpected byte layout");
        }
        return (b[0] == 0x01) ? 8 : 0;
    }

    /**
     * True when the used bytes ({@code length << coder}) are under half of the array's capacity: the views then copy.
     *
     * <p>An untrimmed builder view shares the builder's mutable array, so a later write on the builder below
     * {@code count} (e.g. {@code setCharAt}) would show through the view. The builder-view factories are reachable only
     * through a {@code STRING_VIEW} profile entry at a builder {@code toString} site; its producer
     * ({@code ACCUMULATOR_VIEW}) admits an extraction only when every builder its receiver comes
     * from is only growing (no use writes below {@code count}), so the shared prefix never changes. Memory: a shared
     * view retains at most twice its used bytes.
     */
    @ForceInline
    private static boolean underThreshold(int usedBytes, int capacity) {
        return (usedBytes << 1) < capacity;
    }

    @Override
    @Uninterruptible(reason = "Called from uninterruptible code.", mayBeInlined = true)
    public int length() {
        return length;
    }

    @Override
    @Uninterruptible(reason = "Called from uninterruptible code.", mayBeInlined = true)
    public boolean isEmpty() {
        return length == 0;
    }

    @Override
    public char charAt(int index) {
        if (index < 0 || index >= length) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + length);
        }
        if (isLatin1()) {
            return latin1CharAt(backing, offset, index);
        }
        return utf16CharAt(backing, offset, index);
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o instanceof StringView sv) {
            return equalsStringView(this, sv);
        }
        if (!(o instanceof String s)) {
            return false;
        }
        if (s.length() != length) {
            return false;
        }
        if (s.getClass() == String.class) {
            byte[] other = s.value();
            if (isLatin1()) {
                if (s.isLatin1()) {
                    return latin1Equals(backing, offset, other, 0, length);
                }
                // a plain String is compact: UTF-16 means a non-Latin-1 char, which a Latin-1 view cannot hold
                return false;
            }
            if (s.isLatin1()) {
                // A UTF-16 view of Latin-1-only content (only a racy builder snapshot makes one): by content
                return equalsFallback(this, s);
            }
            return utf16Equals(backing, offset, other, 0, length);
        }
        // Any other rep compares by content (a false here would be wrong for equal content)
        return equalsFallback(this, s);
    }

    /**
     * The total slow path of {@link #equals(Object)} and of the {@code StringViewEqualsGraphBuilder} intrinsic for an
     * argument that is not a same-coder plain {@code String} or view. Never calls {@code equals}.
     */
    static boolean equalsFallback(StringView a, String s) {
        return RepEquals.contentEquals(a, s);
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0 && !hashIsZero) {
            if (isLatin1()) {
                h = latin1HashCode(backing, offset, length);
            } else {
                h = utf16HashCode(backing, offset, length);
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
     * A fresh plain copy of {@code v}'s range for {@link RepConcat#flat}. Static, so the rep gets no non-private
     * String-returning instance method.
     */
    static String flatCopy(StringView v) {
        return v.materializeRange();
    }

    private String materializeRange() {
        // One copy of the range, as substring does; utf16NewString compacts a Latin-1-only range exactly as
        // new String(char[]) does
        if (isLatin1()) {
            return latin1NewString(backing, offset, length);
        }
        return utf16NewString(backing, offset, length);
    }

    @Override
    protected void getBytes(byte[] dst, int dstBegin, byte coder) {
        byte[] v = backing;
        byte myCoder = coder();
        int byteOff = (myCoder == LATIN1) ? offset : offset << 1;
        int byteLen = (myCoder == LATIN1) ? length : length << 1;
        if (myCoder == coder) {
            System.arraycopy(v, byteOff, dst, dstBegin << coder, byteLen);
        } else {
            for (int i = 0; i < byteLen; i++) {
                dst[(dstBegin << 1) + (i << 1)] = v[byteOff + i];
                dst[(dstBegin << 1) + (i << 1) + 1] = 0;
            }
        }
    }

    /**
     * The builder JDK's ranged copy primitive ({@code AbstractStringBuilder.appendChars(.., String, ..)} and
     * {@code putStringAt} copy through it instead of reading {@code value()}): chars {@code [srcPos, srcPos + length)}
     * to {@code dst} at {@code dstBegin} in {@code dst}'s coder (the caller guarantees {@code coder >= coder()}).
     */
    @Override
    protected void getBytes(byte[] dst, int srcPos, int dstBegin, byte coder, int length) {
        byte[] v = backing;
        if (coder() == coder) {
            System.arraycopy(v, (offset + srcPos) << coder, dst, dstBegin << coder, length << coder);
        } else { // a Latin-1 view into a UTF-16 dst
            int from = offset + srcPos;
            for (int i = 0; i < length; i++) {
                RepParts.putChar(dst, dstBegin + i, v[from + i] & 0xff);
            }
        }
    }

    @Override
    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        if (srcBegin < 0 || srcEnd > length || srcBegin > srcEnd) {
            throw new StringIndexOutOfBoundsException(
                            "srcBegin " + srcBegin + ", srcEnd " + srcEnd + ", length " + length);
        }
        int count = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - count) {
            throw new StringIndexOutOfBoundsException(
                            "dstBegin " + dstBegin + ", count " + count + ", dst.length " + dst.length);
        }
        if (isLatin1()) {
            latin1GetChars(backing, offset, srcBegin, srcEnd, dst, dstBegin);
        } else {
            utf16GetChars(backing, offset, srcBegin, srcEnd, dst, dstBegin);
        }
    }

    @Override
    public byte[] getBytes() {
        byte[] r = encode(RepParts.kindOf(Charset.defaultCharset()));
        return r != null ? r : materializeRange().getBytes();
    }

    @Override
    public byte[] getBytes(String charsetName) throws java.io.UnsupportedEncodingException {
        Charset cs = RepParts.lookup(charsetName);
        if (cs == null) {
            return materializeRange().getBytes(charsetName); // the JDK's own exception
        }
        byte[] r = encode(RepParts.kindOf(cs));
        return r != null ? r : materializeRange().getBytes(cs);
    }

    @Override
    public byte[] getBytes(Charset charset) {
        byte[] r = encode(RepParts.kindOf(charset));
        return r != null ? r : materializeRange().getBytes(charset);
    }

    /**
     * The JDK's UTF-8 / ISO-8859-1 / US-ASCII encoding straight from the backing range; {@code null} for any other
     * charset or an oversized result (the caller then runs the JDK body on a flat copy, which reports it as the JDK).
     */
    private byte[] encode(int kind) {
        if (kind < 0) {
            return null;
        }
        return isLatin1() ? encodeLatin1(backing, offset, length, kind) : encodeUTF16(backing, offset, length, kind);
    }

    /** The JDK 25 {@code String.encodeUTF8}/{@code encode8859_1}/{@code encodeASCII} Latin-1 bodies over a range. */
    static byte[] encodeLatin1(byte[] a, int off, int n, int kind) {
        int end = off + n;
        if (kind == RepParts.ISO) {
            return Arrays.copyOfRange(a, off, end);
        }
        int pos = countPositives(a, off, n);
        if (pos == n) {
            return Arrays.copyOfRange(a, off, end);
        }
        if (kind == RepParts.ASCII) {
            byte[] d = Arrays.copyOfRange(a, off, end);
            for (int i = pos; i < n; i++) {
                if (d[i] < 0) {
                    d[i] = '?';
                }
            }
            return d;
        }
        if (n > (Integer.MAX_VALUE >> 1)) {
            return null; // the JDK's StringUTF16.newBytesFor limit: its own OutOfMemoryError on the flat copy
        }
        byte[] d = new byte[n << 1];
        System.arraycopy(a, off, d, 0, pos);
        int dp = pos;
        for (int i = off + pos; i < end; i++) {
            byte c = a[i];
            if (c < 0) {
                d[dp++] = (byte) (0xc0 | ((c & 0xff) >> 6));
                d[dp++] = (byte) (0x80 | (c & 0x3f));
            } else {
                d[dp++] = c;
            }
        }
        return dp == d.length ? d : Arrays.copyOf(d, dp);
    }

    /**
     * The JDK 25 {@code String.encodeUTF8_UTF16}/{@code encode8859_1}/{@code encodeASCII} UTF-16 bodies over the chars
     * {@code [off, off + n)}: unpaired surrogates become {@code '?'}, and a valid pair one {@code '?'} (ISO-8859-1 /
     * US-ASCII), as the JDK.
     */
    static byte[] encodeUTF16(byte[] a, int off, int n, int kind) {
        int sp = off;
        int sl = off + n;
        int dp = 0;
        byte[] d;
        if (kind == RepParts.UTF8) {
            if (n > Integer.MAX_VALUE / 3) {
                return null; // the JDK computes the exact size first: run its body on the flat copy
            }
            d = new byte[n * 3];
            while (sp < sl) { // ascii fast loop
                char c = utf16CharAt(a, 0, sp);
                if (c >= 0x80) {
                    break;
                }
                d[dp++] = (byte) c;
                sp++;
            }
            while (sp < sl) {
                char c = utf16CharAt(a, 0, sp++);
                if (c < 0x80) {
                    d[dp++] = (byte) c;
                } else if (c < 0x800) {
                    d[dp++] = (byte) (0xc0 | (c >> 6));
                    d[dp++] = (byte) (0x80 | (c & 0x3f));
                } else if (Character.isSurrogate(c)) {
                    char c2 = Character.isHighSurrogate(c) && sp < sl ? utf16CharAt(a, 0, sp) : 0;
                    if (Character.isLowSurrogate(c2)) {
                        int uc = Character.toCodePoint(c, c2);
                        d[dp++] = (byte) (0xf0 | ((uc >> 18)));
                        d[dp++] = (byte) (0x80 | ((uc >> 12) & 0x3f));
                        d[dp++] = (byte) (0x80 | ((uc >> 6) & 0x3f));
                        d[dp++] = (byte) (0x80 | (uc & 0x3f));
                        sp++; // 2 chars
                    } else {
                        d[dp++] = '?';
                    }
                } else { // 3 bytes, 16 bits
                    d[dp++] = (byte) (0xe0 | ((c >> 12)));
                    d[dp++] = (byte) (0x80 | ((c >> 6) & 0x3f));
                    d[dp++] = (byte) (0x80 | (c & 0x3f));
                }
            }
        } else {
            d = new byte[n];
            int limit = kind == RepParts.ISO ? 0xff : 0x7f;
            while (sp < sl) {
                if (kind == RepParts.ISO) { // the JDK's implEncodeISOArray run (the intrinsic at image runtime)
                    int ret = encodeISOArray(a, sp, d, dp, sl - sp);
                    sp += ret;
                    dp += ret;
                    if (sp == sl) {
                        break;
                    }
                }
                char c = utf16CharAt(a, 0, sp++);
                if (c <= limit) {
                    d[dp++] = (byte) c;
                    continue;
                }
                if (Character.isHighSurrogate(c) && sp < sl && Character.isLowSurrogate(utf16CharAt(a, 0, sp))) {
                    sp++;
                }
                d[dp++] = '?';
            }
        }
        return dp == d.length ? d : Arrays.copyOf(d, dp);
    }

    /**
     * The JDK's {@code StringCoding.countPositives}: at image runtime the JDK method itself through an alias (so its
     * intrinsic applies); hosted, the JDK's loop.
     */
    static int countPositives(byte[] a, int off, int n) {
        if (ImageInfo.inImageRuntimeCode()) {
            return Target_java_lang_StringCoding_StringRep.countPositives(a, off, n);
        }
        for (int i = 0; i < n; i++) {
            if (a[off + i] < 0) {
                return i;
            }
        }
        return n;
    }

    /**
     * The JDK's {@code StringCoding.implEncodeISOArray} (copies chars up to the first one above 0xFF; returns the
     * count): the JDK intrinsic through an alias at image runtime; hosted, the JDK's loop.
     */
    private static int encodeISOArray(byte[] a, int sp, byte[] d, int dp, int len) {
        if (ImageInfo.inImageRuntimeCode()) {
            return Target_java_lang_StringCoding_StringRep.implEncodeISOArray(a, sp, d, dp, len);
        }
        int i = 0;
        for (; i < len; i++) {
            char c = utf16CharAt(a, 0, sp + i);
            if (c > 0xff) {
                break;
            }
            d[dp + i] = (byte) c;
        }
        return i;
    }

    @Override
    @Deprecated(since = "1.1")
    public void getBytes(int srcBegin, int srcEnd, byte[] dst, int dstBegin) {
        if (srcBegin < 0 || srcEnd > length || srcBegin > srcEnd) {
            throw new StringIndexOutOfBoundsException(
                            "srcBegin " + srcBegin + ", srcEnd " + srcEnd + ", length " + length);
        }
        int count = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - count) {
            throw new StringIndexOutOfBoundsException(
                            "dstBegin " + dstBegin + ", count " + count + ", dst.length " + dst.length);
        }
        if (isLatin1()) {
            System.arraycopy(backing, offset + srcBegin, dst, dstBegin, count);
        } else {
            for (int i = 0; i < count; i++) {
                dst[dstBegin + i] = (byte) utf16CharAt(backing, offset, srcBegin + i); // no charAt
            }
        }
    }

    @Override
    public String substring(int beginIndex, int endIndex) {
        if (beginIndex < 0 || endIndex > length || beginIndex > endIndex) {
            throw new StringIndexOutOfBoundsException(
                            "begin " + beginIndex + ", end " + endIndex + ", length " + length);
        }
        if (beginIndex == 0 && endIndex == length) {
            // The JDK's full-range rule (String.substring returns this), so identity is the JDK's.
            return this;
        }
        int subLen = endIndex - beginIndex;
        if (subLen == 0) {
            return "";
        }
        if (isLatin1()) {
            return latin1NewString(backing, offset + beginIndex, subLen);
        }
        return utf16NewString(backing, offset + beginIndex, subLen);
    }

    @Override
    public String substring(int beginIndex) {
        return substring(beginIndex, length);
    }

    @Override
    public CharSequence subSequence(int start, int end) {
        return substring(start, end);
    }

    @Override
    public int compareTo(String anotherString) {
        if (anotherString.getClass() == String.class) {
            byte[] other = anotherString.value();
            if (isLatin1()) {
                if (anotherString.isLatin1()) {
                    return latin1CompareTo(backing, offset, length, other, anotherString.length());
                }
                return latin1CompareToUTF16(backing, offset, length, other, anotherString.length());
            }
            if (anotherString.isLatin1()) {
                return utf16CompareToLatin1(backing, offset, length, other, anotherString.length());
            }
            return utf16CompareTo(backing, offset, length, other, anotherString.length());
        }
        int n = Math.min(length, anotherString.length());
        for (int i = 0; i < n; i++) {
            char c1 = charAt(i);
            char c2 = anotherString.charAt(i);
            if (c1 != c2) {
                return c1 - c2;
            }
        }
        return length - anotherString.length();
    }

    @Override
    public boolean regionMatches(int toffset, String other, int ooffset, int len) {
        if (ooffset < 0 || toffset < 0 || toffset > (long) length - len || ooffset > (long) other.length() - len) {
            return false;
        }
        if (len <= 0) {
            return true;
        }
        for (int k = 0; k < len; k++) {
            if (charAt(toffset + k) != other.charAt(ooffset + k)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean regionMatches(boolean ignoreCase, int toffset, String other, int ooffset, int len) {
        return materializeRange().regionMatches(ignoreCase, toffset, other, ooffset, len);
    }

    @Override
    public boolean contentEquals(CharSequence cs) {
        if (cs instanceof String s) {
            return equals(s); // the JDK's String rule (equals), with its array fast paths
        }
        if (cs.length() != length) {
            return false;
        }
        for (int i = 0; i < length; i++) {
            if (charAt(i) != cs.charAt(i)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean startsWith(String prefix, int toffset) {
        if (toffset < 0 || toffset > length - prefix.length()) {
            return false;
        }
        // One array compare of the backing range against the prefix.
        return RepParts.mismatchArray(backing, coder(), offset + toffset, prefix, 0, prefix.length()) < 0;
    }

    @Override
    public boolean startsWith(String prefix) {
        return startsWith(prefix, 0);
    }

    @Override
    public boolean endsWith(String suffix) {
        return startsWith(suffix, length - suffix.length());
    }

    @Override
    public int indexOf(int ch, int fromIndex) {
        if (fromIndex < 0) {
            fromIndex = 0;
        }
        if (ch > 0xFFFF && !isLatin1()) {
            return materializeRange().indexOf(ch, fromIndex);
        }
        return indexOfChar(ch, fromIndex, length);
    }

    /** The first index of the BMP char {@code ch} in {@code [from, to)}, else {@code -1}, by a scan of the range. */
    private int indexOfChar(int ch, int from, int to) {
        byte[] v = backing;
        int off = offset;
        if (isLatin1()) {
            if ((ch >>> 8) != 0) {
                return -1;
            }
            byte b = (byte) ch;
            for (int i = from; i < to; i++) {
                if (v[off + i] == b) {
                    return i;
                }
            }
            return -1;
        }
        for (int i = from; i < to; i++) {
            if (utf16CharAt(v, off, i) == ch) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int indexOf(int ch) {
        return indexOf(ch, 0);
    }

    @Override
    public int indexOf(int ch, int beginIndex, int endIndex) {
        if (beginIndex < 0 || endIndex > length || beginIndex > endIndex) {
            throw new StringIndexOutOfBoundsException(
                            "begin " + beginIndex + ", end " + endIndex + ", length " + length);
        }
        if (ch > 0xFFFF && !isLatin1()) {
            return materializeRange().indexOf(ch, beginIndex, endIndex);
        }
        return indexOfChar(ch, beginIndex, endIndex);
    }

    @Override
    public int indexOf(String str, int fromIndex) {
        return indexOfRange(str, fromIndex, length);
    }

    /**
     * JDK 25 {@code String.indexOf(String, int, int)}: a length-1 needle takes the char overload first (which checks the
     * bounds itself); otherwise the bounds are checked and the search runs over {@code [0, endIndex)}.
     */
    @Override
    public int indexOf(String str, int beginIndex, int endIndex) {
        if (str.length() == 1) {
            return indexOf(str.charAt(0), beginIndex, endIndex);
        }
        if (beginIndex < 0 || endIndex > length || beginIndex > endIndex) {
            throw new StringIndexOutOfBoundsException(
                            "begin " + beginIndex + ", end " + endIndex + ", length " + length);
        }
        return indexOfRange(str, beginIndex, endIndex);
    }

    /**
     * The JDK 25 rules of {@code String.indexOf(byte[] src, byte srcCoder, int srcCount, String tgtStr, int fromIndex)}
     * over this view's first {@code srcCount} chars ({@code srcCount <= length}).
     */
    private int indexOfRange(String str, int fromIndex, int srcCount) {
        // An empty needle past the end answers srcCount
        fromIndex = Math.clamp(fromIndex, 0, srcCount);
        int slen = str.length();
        if (slen > srcCount - fromIndex) {
            return -1;
        }
        if (slen == 0) {
            return fromIndex;
        }
        int max = srcCount - slen;
        byte[] tv = str.value();
        if (tv != null) {
            // First-char scan plus one array compare per candidate
            byte tc = str.coder();
            byte myCoder = coder();
            if (myCoder == LATIN1 && tc != LATIN1 && str.getClass() == String.class) {
                return -1; // a compact plain UTF-16 needle holds a non-Latin-1 char (the JDK's coder rule)
            }
            char first = tc == LATIN1 ? (char) (tv[0] & 0xff) : RepParts.getChar(tv, 0);
            byte[] v = backing;
            int off = offset;
            for (int i = fromIndex; i <= max; i++) {
                char c = myCoder == LATIN1 ? latin1CharAt(v, off, i) : utf16CharAt(v, off, i);
                if (c == first && RepParts.mismatchArray(v, myCoder, off + i + 1, str, 1, slen - 1) < 0) {
                    return i;
                }
            }
            return -1;
        }
        for (int i = fromIndex; i <= max; i++) {
            boolean match = true;
            for (int j = 0; j < slen; j++) {
                if (charAt(i + j) != str.charAt(j)) {
                    match = false;
                    break;
                }
            }
            if (match) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int indexOf(String str) {
        return indexOf(str, 0);
    }

    @Override
    public int lastIndexOf(int ch, int fromIndex) {
        if (fromIndex >= length) {
            fromIndex = length - 1;
        }
        if (fromIndex < 0) {
            return -1;
        }
        if (ch > 0xFFFF && !isLatin1()) {
            return materializeRange().lastIndexOf(ch, fromIndex);
        }
        // A direct backward scan of the backing range.
        byte[] v = backing;
        int off = offset;
        if (isLatin1()) {
            if ((ch >>> 8) != 0) {
                return -1;
            }
            byte b = (byte) ch;
            for (int i = fromIndex; i >= 0; i--) {
                if (v[off + i] == b) {
                    return i;
                }
            }
            return -1;
        }
        for (int i = fromIndex; i >= 0; i--) {
            if (utf16CharAt(v, off, i) == ch) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int lastIndexOf(int ch) {
        return lastIndexOf(ch, length - 1);
    }

    @Override
    public char[] toCharArray() {
        char[] result = new char[length];
        getChars(0, length, result, 0);
        return result;
    }

    @Override
    public String trim() {
        int st = 0;
        while (st < length && charAt(st) <= ' ') {
            st++;
        }
        int en = length;
        while (en > st && charAt(en - 1) <= ' ') {
            en--;
        }
        // The JDK's identities: nothing trimmed is this, all trimmed is "".
        if (st == 0 && en == length) {
            return this;
        }
        if (st == en) {
            return "";
        }
        return createView(this, st, en);
    }

    @Override
    public String strip() {
        int st = 0;
        while (st < length && Character.isWhitespace(charAt(st))) {
            st++;
        }
        // The JDK's rules: all white space is "", nothing stripped is this.
        if (st == length) {
            return "";
        }
        int en = length;
        while (en > st && Character.isWhitespace(charAt(en - 1))) {
            en--;
        }
        if (st == 0 && en == length) {
            return this;
        }
        return createView(this, st, en);
    }

    @Override
    public String stripLeading() {
        int st = 0;
        while (st < length && Character.isWhitespace(charAt(st))) {
            st++;
        }
        // The JDK's rules: nothing stripped is this, all white space is "".
        if (st == 0) {
            return this;
        }
        if (st == length) {
            return "";
        }
        return createView(this, st, length);
    }

    @Override
    public String stripTrailing() {
        int en = length;
        while (en > 0 && Character.isWhitespace(charAt(en - 1))) {
            en--;
        }
        // The JDK's rules: nothing stripped is this, all white space is "".
        if (en == length) {
            return this;
        }
        if (en == 0) {
            return "";
        }
        return createView(this, 0, en);
    }

    @Override
    public boolean isBlank() {
        for (int i = 0; i < length; i++) {
            if (!Character.isWhitespace(charAt(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toUpperCase(Locale locale) {
        // The JDK returns the receiver when no character changes; the plain copy's identity is mapped back to this.
        if (locale == null) {
            throw new NullPointerException(); // the JDK's first check (StringLatin1/UTF16.toUpperCase)
        }
        if (latin1CaseInvariant(true)) {
            return this; // the no-change fast path, no copy (toUpperCase(Locale) is a returns-this entry)
        }
        String flat = materializeRange();
        String result = flat.toUpperCase(locale);
        return result == flat ? this : result;
    }

    @Override
    public String toUpperCase() {
        return toUpperCase(Locale.getDefault());
    }

    @Override
    public String toLowerCase(Locale locale) {
        // As toUpperCase(Locale): this when no character changes, as in the JDK.
        if (locale == null) {
            throw new NullPointerException(); // the JDK's first check (StringLatin1/UTF16.toLowerCase)
        }
        if (latin1CaseInvariant(false)) {
            return this; // the no-change fast path, no copy (toLowerCase(Locale) is a returns-this entry)
        }
        String flat = materializeRange();
        String result = flat.toLowerCase(locale);
        return result == flat ? this : result;
    }

    /**
     * {@code true} only when the JDK returns the receiver itself: every char is Latin-1 and none changes under the JDK
     * 25 {@code StringLatin1} no-change scan ({@code toUpperCase}: {@code notUpperCaseEx}; {@code toLowerCase}:
     * {@link Character#isUpperCase(int)} on Latin-1). The scan is locale-independent in the JDK too (the tr/az/lt rules
     * apply only after a changing char). Other content takes the plain-copy path.
     */
    private boolean latin1CaseInvariant(boolean upper) {
        byte[] v = backing;
        int off = offset;
        boolean latin1 = isLatin1();
        for (int i = 0; i < length; i++) {
            int cp = latin1 ? v[off + i] & 0xff : utf16CharAt(v, off, i);
            if (cp > 0xff) {
                return false;
            }
            boolean changes = upper ? cp >= 'a' && (cp <= 'z' || cp == 0xb5 || (cp >= 0xdf && cp != 0xf7)) : Character.isUpperCase(cp);
            if (changes) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toLowerCase() {
        return toLowerCase(Locale.getDefault());
    }

    @Override
    public String repeat(int count) {
        // The JDK returns this for count 1; other counts take the plain copy.
        if (count == 1) {
            return this;
        }
        return materializeRange().repeat(count);
    }

    @Override
    public int codePointAt(int index) {
        if (index < 0 || index >= length) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + length);
        }
        char c1 = charAt(index);
        if (Character.isHighSurrogate(c1) && index + 1 < length) {
            char c2 = charAt(index + 1);
            if (Character.isLowSurrogate(c2)) {
                return Character.toCodePoint(c1, c2);
            }
        }
        return c1;
    }

    @Override
    public int codePointBefore(int index) {
        int i = index - 1;
        if (i < 0 || i >= length) {
            throw new StringIndexOutOfBoundsException("index " + index + ", length " + length);
        }
        char c2 = charAt(i);
        if (Character.isLowSurrogate(c2) && i > 0) {
            char c1 = charAt(i - 1);
            if (Character.isHighSurrogate(c1)) {
                return Character.toCodePoint(c1, c2);
            }
        }
        return c2;
    }

    @Override
    public int codePointCount(int beginIndex, int endIndex) {
        if (beginIndex < 0 || endIndex > length || beginIndex > endIndex) {
            throw new StringIndexOutOfBoundsException(
                            "begin " + beginIndex + ", end " + endIndex + ", length " + length);
        }
        int count = endIndex - beginIndex;
        for (int i = beginIndex; i < endIndex - 1;) {
            if (Character.isHighSurrogate(charAt(i++)) && Character.isLowSurrogate(charAt(i))) {
                count--;
                i++;
            }
        }
        return count;
    }

    @Override
    public int offsetByCodePoints(int index, int codePointOffset) {
        // Character.offsetByCodePoints(CharSequence, int, int) over this view's charAt, so rep code never passes
        // the view into shared JDK code (RepEscapeTest).
        int len = length;
        if (index < 0 || index > len) {
            throw new IndexOutOfBoundsException();
        }
        int x = index;
        if (codePointOffset >= 0) {
            int i;
            for (i = 0; x < len && i < codePointOffset; i++) {
                if (Character.isHighSurrogate(charAt(x++)) && x < len && Character.isLowSurrogate(charAt(x))) {
                    x++;
                }
            }
            if (i < codePointOffset) {
                throw new IndexOutOfBoundsException();
            }
        } else {
            int i;
            for (i = codePointOffset; x > 0 && i < 0; i++) {
                if (Character.isLowSurrogate(charAt(--x)) && x > 0 && Character.isHighSurrogate(charAt(x - 1))) {
                    x--;
                }
            }
            if (i < 0) {
                throw new IndexOutOfBoundsException();
            }
        }
        return x;
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
    static boolean equalsStringView(StringView a, StringView b) {
        if (a == b) {
            return true;
        }
        if (a.length != b.length) {
            return false;
        }
        if (a.length == 0) {
            return true;
        }
        if (a.isLatin1() != b.isLatin1()) {
            // The factories are coder-exact, but a racy builder snapshot can make a UTF-16 view of Latin-1 content
            return RepEquals.contentEquals(a, b);
        }
        if (a.isLatin1()) {
            return latin1Equals(a.backing, a.offset, b.backing, b.offset, a.length);
        }
        return utf16Equals(a.backing, a.offset, b.backing, b.offset, a.length);
    }
}
