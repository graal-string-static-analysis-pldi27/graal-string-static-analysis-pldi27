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

import java.util.Locale;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

public class StringViewMethodTest {

    private static StringView view(String s, int from, int end) {
        return (StringView) StringView.create(s, from, end);
    }

    private static void assertStringEquals(String label, String got, String exp) {
        RepEq.assertRepEquals(label + " (got=" + got + " exp=" + exp + ")", exp, got);
    }

    @Test
    public void trimLatin1() {
        String s = "  Hello  World  ";
        StringView v = view(s, 2, 13);
        assertStringEquals("trim", v.trim(), s.substring(2, 13).trim());
    }

    @Test
    public void trimAllWhitespace() {
        String s = "   ";
        StringView v = view(s, 0, 3);
        assertStringEquals("trimAllWs", v.trim(), "");
    }

    @Test
    public void trimNoWhitespace() {
        String s = "Hello, World!";
        StringView v = view(s, 0, 13);
        assertStringEquals("trimNoWs", v.trim(), s);
    }

    @Test
    public void stripLatin1() {
        String s = "\t Hello \n";
        StringView v = view(s, 0, 9);
        assertStringEquals("strip", v.strip(), s.strip());
    }

    @Test
    public void stripLeading() {
        String s = "  Hello  ";
        StringView v = view(s, 0, 9);
        assertStringEquals("stripLeading", v.stripLeading(), s.stripLeading());
    }

    @Test
    public void stripTrailing() {
        String s = "  Hello  ";
        StringView v = view(s, 0, 9);
        assertStringEquals("stripTrailing", v.stripTrailing(), s.stripTrailing());
    }

    @Test
    public void stripUtf16() {
        String s = "\u3000\u03b1\u03b2\u3000";
        StringView v = view(s, 0, 4);
        assertStringEquals("stripUtf16", v.strip(), s.strip());
    }

    @Test
    public void stripLeadingTrailingAllWs() {
        String s = "   ";
        StringView v = view(s, 0, 3);
        assertStringEquals("stripAllWs", v.strip(), "");
    }

    @Test
    public void isBlankTrue() {
        String s = "   \t\n ";
        StringView v = view(s, 0, 6);
        Assert.assertTrue(v.isBlank());
    }

    @Test
    public void isBlankFalse() {
        String s = "  a  ";
        StringView v = view(s, 0, 5);
        Assert.assertFalse(v.isBlank());
    }

    @Test
    public void isBlankEmpty() {
        String s = "Hello";
        String v = StringView.create(s, 2, 2);
        Assert.assertSame("a rep is never empty (an empty range is the JDK substring's \"\")", "", v);
        Assert.assertTrue(v.isBlank());
    }

    @Test
    public void toUpperCaseLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        assertStringEquals("toUpperCase", v.toUpperCase(Locale.ROOT), s.substring(2, 9).toUpperCase(Locale.ROOT));
    }

    @Test
    public void toLowerCaseLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        assertStringEquals("toLowerCase", v.toLowerCase(Locale.ROOT), s.substring(2, 9).toLowerCase(Locale.ROOT));
    }

    @Test
    public void toUpperCaseUtf16() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        assertStringEquals("toUpperCaseUtf16", v.toUpperCase(Locale.ROOT), s.substring(2, 8).toUpperCase(Locale.ROOT));
    }

    @Test
    public void toUpperCaseSharpS() {
        String s = "stra\u00dfe";
        StringView v = view(s, 0, 6);
        String got = v.toUpperCase(Locale.ROOT);
        String exp = s.toUpperCase(Locale.ROOT);
        Assert.assertEquals(exp, got);
        Assert.assertEquals(exp.length(), got.length());
    }

    @Test
    public void repeatLatin1() {
        String s = "abc";
        StringView v = view(s, 1, 3);
        assertStringEquals("repeat", v.repeat(3), s.substring(1, 3).repeat(3));
    }

    @Test
    public void repeatZero() {
        String s = "abc";
        StringView v = view(s, 0, 3);
        assertStringEquals("repeat0", v.repeat(0), "");
    }

    @Test
    public void codePointAtLatin1() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        Assert.assertEquals(s.substring(1, 4).codePointAt(0), v.codePointAt(0));
        Assert.assertEquals(s.substring(1, 4).codePointAt(2), v.codePointAt(2));
    }

    @Test
    public void codePointAtSupplementary() {
        String s = "A\uD800\uDC00B";
        StringView v = view(s, 1, 3);
        Assert.assertEquals(s.substring(1, 3).codePointAt(0), v.codePointAt(0));
    }

    @Test
    public void codePointBeforeSupplementary() {
        String s = "A\uD800\uDC00B";
        StringView v = view(s, 1, 3);
        Assert.assertEquals(s.substring(1, 3).codePointBefore(2), v.codePointBefore(2));
    }

    @Test
    public void codePointBeforeLatin1() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        Assert.assertEquals(s.substring(1, 4).codePointBefore(1), v.codePointBefore(1));
        Assert.assertEquals(s.substring(1, 4).codePointBefore(3), v.codePointBefore(3));
    }

    @Test
    public void codePointCountNoSurrogates() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertEquals(s.substring(2, 9).codePointCount(0, 7), v.codePointCount(0, 7));
    }

    @Test
    public void codePointCountWithSurrogates() {
        String s = "A\uD800\uDC00B\uD800\uDC00C";
        StringView v = view(s, 1, 6);
        int exp = s.substring(1, 6).codePointCount(0, 5);
        Assert.assertEquals(exp, v.codePointCount(0, 5));
    }

    @Test
    public void offsetByCodePointsForward() {
        String s = "A\uD800\uDC00BC";
        StringView v = view(s, 0, 5);
        Assert.assertEquals(s.offsetByCodePoints(0, 2), v.offsetByCodePoints(0, 2));
        Assert.assertEquals(s.offsetByCodePoints(0, 3), v.offsetByCodePoints(0, 3));
    }

    @Test
    public void offsetByCodePointsBackward() {
        String s = "A\uD800\uDC00BC";
        StringView v = view(s, 0, 5);
        int idx = v.offsetByCodePoints(0, 2);
        Assert.assertEquals(s.offsetByCodePoints(idx, -1), v.offsetByCodePoints(idx, -1));
    }

    @Test
    public void nestedTrimReturnsStringView() {
        String s = "  Hello  ";
        StringView v = view(s, 1, 8);
        String trimmed = v.trim();
        Assert.assertEquals("com.oracle.svm.core.stringrep.StringView", trimmed.getClass().getName());
        assertStringEquals("nestedTrim", trimmed, "Hello");
    }

    @Test
    public void nestedStripReturnsStringView() {
        String s = "  Hello  ";
        StringView v = view(s, 1, 8);
        String stripped = v.strip();
        Assert.assertEquals("com.oracle.svm.core.stringrep.StringView", stripped.getClass().getName());
        assertStringEquals("nestedStrip", stripped, "Hello");
    }

    @Test
    public void trimStripNoCopyStructural() {
        String s = "  Hello  ";
        StringView v = view(s, 1, 8);
        String trimmed = v.trim();
        String stripped = v.strip();
        StringView trimView = (StringView) StringView.create(s, 3, 8);
        Assert.assertEquals(trimView.getClass().getName(), trimmed.getClass().getName());
        Assert.assertEquals(trimView.getClass().getName(), stripped.getClass().getName());
        Assert.assertEquals(5, trimmed.length());
        Assert.assertEquals(5, stripped.length());
        Assert.assertEquals('H', trimmed.charAt(0));
        Assert.assertEquals('o', trimmed.charAt(4));
        String nested = ((StringView) trimmed).substring(1, 3);
        Assert.assertEquals("java.lang.String", nested.getClass().getName());
        assertStringEquals("nestedOnTrim", nested, "el");
    }

    @Test
    public void equalsLatin1SameContent() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertTrue(v.equals(s.substring(2, 9)));
    }

    @Test
    public void equalsLatin1DifferentContent() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertFalse(v.equals("llo, XYZ"));
    }

    @Test
    public void equalsLengthMismatch() {
        String s = "Hello";
        StringView v = view(s, 0, 5);
        Assert.assertFalse(v.equals("Hi"));
        Assert.assertFalse(v.equals("Helloo"));
    }

    @Test
    public void equalsUtf16SameContent() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        Assert.assertTrue(v.equals(s.substring(2, 8)));
    }

    @Test
    public void equalsUtf16DifferentContent() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        Assert.assertFalse(v.equals("llo wX"));
    }

    @Test
    public void equalsCrossCoder() {
        String latin1 = "abc";
        String utf16 = "a\u03b2c";
        StringView vLatin1 = view(latin1, 0, 3);
        Assert.assertFalse(vLatin1.equals(utf16));
        StringView vUtf16 = view(utf16, 0, 3);
        Assert.assertFalse(vUtf16.equals(latin1));
    }

    @Test
    public void equalsSelf() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        Assert.assertTrue(v.equals(v));
    }

    @Test
    public void equalsNonString() {
        String s = "Hello";
        StringView v = view(s, 0, 5);
        Assert.assertFalse(v.equals(Integer.valueOf(42)));
        Assert.assertFalse(v.equals(null));
    }

    @Test
    public void hashCodeLatin1MatchesString() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertEquals(s.substring(2, 9).hashCode(), v.hashCode());
    }

    @Test
    public void hashCodeUtf16MatchesString() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        Assert.assertEquals(s.substring(2, 8).hashCode(), v.hashCode());
    }

    @Test
    public void hashCodeCached() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        int h1 = v.hashCode();
        int h2 = v.hashCode();
        Assert.assertEquals(h1, h2);
    }

    @Test
    public void hashCodeEmpty() {
        String s = "Hello";
        String v = StringView.create(s, 2, 2);
        Assert.assertSame("a rep is never empty (an empty range is the JDK substring's \"\")", "", v);
        Assert.assertEquals(0, v.hashCode());
    }

    @Test
    public void compareToLatin1Equal() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertEquals(0, v.compareTo(s.substring(2, 9)));
    }

    @Test
    public void compareToLatin1Less() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 5);
        Assert.assertTrue(v.compareTo("xyz") < 0);
    }

    @Test
    public void compareToLatin1Greater() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 5);
        Assert.assertTrue(v.compareTo("abc") > 0);
    }

    @Test
    public void compareToLatin1LengthDiff() {
        String s = "Hello";
        StringView v = view(s, 0, 5);
        Assert.assertTrue(v.compareTo("Helloo") < 0);
        Assert.assertTrue(v.compareTo("Hell") > 0);
    }

    @Test
    public void compareToUtf16Equal() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        Assert.assertEquals(0, v.compareTo(s.substring(2, 8)));
    }

    @Test
    public void compareToCrossCoder() {
        String latin1 = "abc";
        String utf16 = "a\u03b2c";
        StringView vLatin1 = view(latin1, 0, 3);
        StringView vUtf16 = view(utf16, 0, 3);
        Assert.assertTrue(vLatin1.compareTo(utf16) < 0);
        Assert.assertTrue(vUtf16.compareTo(latin1) > 0);
    }

    @Test
    public void getCharsLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        char[] dst = new char[7];
        v.getChars(0, 7, dst, 0);
        Assert.assertEquals(s.substring(2, 9), new String(dst));
    }

    @Test
    public void getCharsUtf16() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        char[] dst = new char[6];
        v.getChars(0, 6, dst, 0);
        Assert.assertEquals(s.substring(2, 8), new String(dst));
    }

    @Test
    public void getCharsSubRange() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        char[] dst = new char[3];
        v.getChars(1, 4, dst, 0);
        Assert.assertEquals("lo,", new String(dst));
    }

    @Test
    public void substringLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        assertStringEquals("sub", v.substring(1, 5), s.substring(3, 7));
    }

    @Test
    public void substringUtf16() {
        String s = "héllo wörld";
        StringView v = view(s, 2, 8);
        assertStringEquals("subUtf16", v.substring(1, 4), s.substring(3, 6));
    }

    @Test
    public void substringEmptyRange() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        assertStringEquals("subEmpty", v.substring(1, 1), "");
    }

    @Test
    public void substringFullRange() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        assertStringEquals("subFull", v.substring(0, 3), "ell");
    }

    @Test
    public void charAtLatin1() {
        String s = "Hello";
        StringView v = view(s, 1, 4);
        Assert.assertEquals('e', v.charAt(0));
        Assert.assertEquals('l', v.charAt(1));
        Assert.assertEquals('l', v.charAt(2));
    }

    @Test
    public void charAtUtf16() {
        String s = "a\u03b2c\u03b3d";
        StringView v = view(s, 1, 4);
        Assert.assertEquals(s.charAt(1), v.charAt(0));
        Assert.assertEquals(s.charAt(2), v.charAt(1));
        Assert.assertEquals(s.charAt(3), v.charAt(2));
    }

    @Test
    public void startsWithLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertTrue(v.startsWith("llo"));
        Assert.assertFalse(v.startsWith("World"));
        Assert.assertTrue(v.startsWith("o, W", 2));
    }

    @Test
    public void endsWithLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertTrue(v.endsWith("Wo"));
        Assert.assertFalse(v.endsWith("Hello"));
    }

    @Test
    public void indexOfLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertEquals(3, v.indexOf(','));
        Assert.assertEquals(0, v.indexOf('l'));
        Assert.assertEquals(-1, v.indexOf('z'));
        Assert.assertEquals(5, v.indexOf("Wo"));
        Assert.assertEquals(-1, v.indexOf("xyz"));
    }

    /**
     * The ranged {@code indexOf(String, int, int)} override answers exactly as the stock body on the equal plain
     * String (Latin-1 and UTF-16 views, a UTF-16 needle in a Latin-1 view, length 0/1/2+ needles, plain and StringView
     * needles, every in-bounds range), and throws {@code StringIndexOutOfBoundsException} wherever the stock body does.
     * A StringView needle ({@code value() == null}, so {@code indexOfRange} takes its per-char loop) follows the same
     * rules; the empty needle is plain only (a rep is never empty: {@code create} returns the {@code ""}
     * literal).
     */
    @Test
    public void indexOfStringRangeMatchesStock() {
        String[] hosts = {"xxInfinity  NaN Infinity yy", "\u20ACab\u20ACabc\u20AC", "aaaaab"};
        String[] needles = {"", "a", "b", "ab", "abc", "Infinity", "NaN", "\u20ACa", "zz"};
        for (String host : hosts) {
            for (int from = 0; from <= 2; from++) {
                for (int end = host.length() - 2; end <= host.length(); end++) {
                    StringView v = view(host, from, end);
                    String plain = host.substring(from, end);
                    for (String n : needles) {
                        for (int b = -1; b <= plain.length() + 1; b++) {
                            for (int e = b - 1; e <= plain.length() + 1; e++) {
                                String label = "'" + plain + "'.indexOf('" + n + "'," + b + "," + e + ")";
                                Integer exp;
                                try {
                                    exp = plain.indexOf(n, b, e);
                                } catch (StringIndexOutOfBoundsException ex) {
                                    exp = null;
                                }
                                Integer got;
                                try {
                                    got = v.indexOf(n, b, e);
                                } catch (StringIndexOutOfBoundsException ex) {
                                    got = null;
                                }
                                Assert.assertEquals(label, exp, got);
                            }
                        }
                    }
                    // the same needles as StringViews: a view needle's value() is null, so the search
                    // takes indexOfRange's per-char loop (a length-1 view needle takes the char-overload shortcut).
                    // The empty needle stays plain: create returns the "" literal, never an empty view.
                    for (String n : needles) {
                        if (n.isEmpty()) {
                            continue;
                        }
                        StringView nv = view(n, 0, n.length());
                        for (int b = -1; b <= plain.length() + 1; b++) {
                            for (int e = b - 1; e <= plain.length() + 1; e++) {
                                String label = "'" + plain + "'.indexOf(view('" + n + "')," + b + "," + e + ")";
                                Integer exp;
                                try {
                                    exp = plain.indexOf(n, b, e);
                                } catch (StringIndexOutOfBoundsException ex) {
                                    exp = null;
                                }
                                Integer got;
                                try {
                                    got = v.indexOf(nv, b, e);
                                } catch (StringIndexOutOfBoundsException ex) {
                                    got = null;
                                }
                                Assert.assertEquals(label, exp, got);
                            }
                        }
                    }
                }
            }
        }
    }

    @Test
    public void contentEqualsLatin1() {
        String s = "Hello, World!";
        StringView v = view(s, 2, 9);
        Assert.assertTrue(v.contentEquals((CharSequence) s.substring(2, 9)));
        Assert.assertFalse(v.contentEquals((CharSequence) "xyz"));
    }
}