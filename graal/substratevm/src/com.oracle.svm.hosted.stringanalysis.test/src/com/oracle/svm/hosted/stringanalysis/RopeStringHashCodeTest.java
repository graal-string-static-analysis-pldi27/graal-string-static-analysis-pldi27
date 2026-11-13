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

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.ThreeWayString;

public class RopeStringHashCodeTest {

    private static final String LATIN1_A = "Hello, ";
    private static final String LATIN1_B = "World!";
    private static final String UTF16_A = "\u03b1\u03b2";
    private static final String UTF16_B = "\u03b3\u03b4";

    private static void assertRopeHashEqualsFlat(String left, String right) {
        String rope = RopeString.create(left, right);
        String flat = left + right;
        int lazyHash = rope.hashCode();
        int flatHash = flat.hashCode();
        Assert.assertEquals("lazy hash != flat hash for left=" + escape(left) + " right=" + escape(right),
                        flatHash, lazyHash);
        int lazyHash2 = rope.hashCode();
        Assert.assertEquals("hashCode not stable (cache) for left=" + escape(left) + " right=" + escape(right),
                        lazyHash, lazyHash2);
    }

    private static String escape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= 0x20 && c < 0x7f) {
                sb.append(c);
            } else {
                sb.append(String.format("\\u%04x", (int) c));
            }
        }
        return sb.toString();
    }

    @Test
    public void latin1PlusLatin1() {
        assertRopeHashEqualsFlat(LATIN1_A, LATIN1_B);
    }

    @Test
    public void utf16PlusUtf16() {
        assertRopeHashEqualsFlat(UTF16_A, UTF16_B);
    }

    @Test
    public void latin1PlusUtf16() {
        assertRopeHashEqualsFlat(LATIN1_A, UTF16_B);
    }

    @Test
    public void utf16PlusLatin1() {
        assertRopeHashEqualsFlat(UTF16_A, LATIN1_B);
    }

    @Test
    public void emptyPlusEmpty() {
        assertRopeHashEqualsFlat("", "");
    }

    @Test
    public void emptyPlusNonEmpty() {
        assertRopeHashEqualsFlat("", LATIN1_A);
    }

    @Test
    public void nonEmptyPlusEmpty() {
        assertRopeHashEqualsFlat(LATIN1_A, "");
    }

    @Test
    public void zeroHashNulPair() {
        assertRopeHashEqualsFlat("\u0000", "\u0000");
    }

    @Test
    public void zeroHashEmptyRope() {
        String rope = RopeString.create("", "");
        Assert.assertSame("a rep is never empty (a fresh plain String)", String.class, rope.getClass());
        Assert.assertEquals(0, rope.hashCode());
        Assert.assertEquals(0, rope.hashCode());
    }

    @Test
    public void mixedCoderCombinations() {
        assertRopeHashEqualsFlat("abc", "\u03b1\u03b2\u03b3");
        assertRopeHashEqualsFlat("\u03b1\u03b2\u03b3", "abc");
        assertRopeHashEqualsFlat("x", "\u00e9");
        assertRopeHashEqualsFlat("\u00e9", "x");
    }

    @Test
    public void repeatedCallsUseCache() {
        String rope = RopeString.create(LATIN1_A, LATIN1_B);
        int h1 = rope.hashCode();
        for (int i = 0; i < 100; i++) {
            Assert.assertEquals(h1, rope.hashCode());
        }
    }

    @Test
    public void threeWayLatin1Latin1Latin1() {
        String t = ThreeWayString.create("Hel", "lo, ", "World!");
        String flat = "Hel" + "lo, " + "World!";
        Assert.assertEquals(flat.hashCode(), t.hashCode());
    }

    @Test
    public void threeWayMixedCoders() {
        String t = ThreeWayString.create("ab", "\u03b1\u03b2", "cd");
        String flat = "ab\u03b1\u03b2cd";
        Assert.assertEquals(flat.hashCode(), t.hashCode());
    }

    @Test
    public void threeWayAllUtf16() {
        String t = ThreeWayString.create("\u03b1", "\u03b2", "\u03b3");
        String flat = "\u03b1\u03b2\u03b3";
        Assert.assertEquals(flat.hashCode(), t.hashCode());
    }

    @Test
    public void fixedConcat4Latin1() {
        String f = FixedConcat4.create("a", "b", "c", "d");
        String flat = "abcd";
        Assert.assertEquals(flat.hashCode(), f.hashCode());
    }

    @Test
    public void fixedConcat4Mixed() {
        String f = FixedConcat4.create("a", "\u03b1", "b", "\u03b2");
        String flat = "a\u03b1b\u03b2";
        Assert.assertEquals(flat.hashCode(), f.hashCode());
    }

    @Test
    public void fixedConcat4AllUtf16() {
        String f = FixedConcat4.create("\u03b1", "\u03b2", "\u03b3", "\u03b4");
        String flat = "\u03b1\u03b2\u03b3\u03b4";
        Assert.assertEquals(flat.hashCode(), f.hashCode());
    }

    @Test
    public void arrayLazyLatin1() {
        String a = ArrayLazyString.create(new String[]{"Hel", "lo", ", ", "Wor", "ld!"});
        String flat = "Hello, World!";
        Assert.assertEquals(flat.hashCode(), a.hashCode());
    }

    @Test
    public void arrayLazyMixed() {
        String a = ArrayLazyString.create(new String[]{"ab", "\u03b1\u03b2", "cd", "\u03b3"});
        String flat = "ab\u03b1\u03b2cd\u03b3";
        Assert.assertEquals(flat.hashCode(), a.hashCode());
    }

    @Test
    public void arrayLazyAllUtf16() {
        String a = ArrayLazyString.create(new String[]{"\u03b1", "\u03b2", "\u03b3", "\u03b4", "\u03b5"});
        String flat = "\u03b1\u03b2\u03b3\u03b4\u03b5";
        Assert.assertEquals(flat.hashCode(), a.hashCode());
    }

    @Test
    public void interleavedLatin1() {
        String isa = InterleavedStringArray.create(new String[]{"a", "b", "c"}, ", ");
        String flat = "a, b, c";
        Assert.assertEquals(flat.hashCode(), isa.hashCode());
    }

    @Test
    public void interleavedMixed() {
        String isa = InterleavedStringArray.create(new String[]{"ab", "\u03b1\u03b2", "cd"}, ", ");
        String flat = "ab, \u03b1\u03b2, cd";
        Assert.assertEquals(flat.hashCode(), isa.hashCode());
    }

    @Test
    public void interleavedUtf16Delimiter() {
        String isa = InterleavedStringArray.create(new String[]{"a", "b", "c"}, "\u03b1");
        String flat = "a\u03b1b\u03b1c";
        Assert.assertEquals(flat.hashCode(), isa.hashCode());
    }

    @Test
    public void interleavedSingleElement() {
        String isa = InterleavedStringArray.create(new String[]{"abc"}, ", ");
        String flat = "abc";
        Assert.assertEquals(flat.hashCode(), isa.hashCode());
    }
}