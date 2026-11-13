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

import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * (A) the helper-free encode of a Latin-1 StringView equals the JDK byte for byte;
 * (B) the stored substring-view rule: the variant, the profile line, the stored-wins merge, and the
 * {@code createStored}/{@code createViewStored} factories (a copy = the JDK {@code substring} result under 9 bytes or
 * under half occupancy, a view otherwise; {@code ""} for an empty range).
 */
public class StoredSubstringViewTest {

    private static final List<Charset> CHARSETS = List.of(StandardCharsets.UTF_8, StandardCharsets.ISO_8859_1, StandardCharsets.US_ASCII,
                    StandardCharsets.UTF_16, StandardCharsets.UTF_16LE);

    private static void assertEncodesAsJdk(String parent, int from, int end) throws Exception {
        String v = StringView.create(parent, from, end);
        String jdk = parent.substring(from, end);
        for (Charset cs : CHARSETS) {
            Assert.assertArrayEquals(cs + " " + jdk, jdk.getBytes(cs), v.getBytes(cs));
            Assert.assertArrayEquals(cs.name() + " " + jdk, jdk.getBytes(cs.name()), v.getBytes(cs.name()));
        }
        Assert.assertArrayEquals(jdk.getBytes(), v.getBytes());
    }

    @Test
    public void encodeEqualsTheJdk() throws Exception {
        String ascii = "hello world, the quick brown fox";
        String latin1 = "café crème brûlée ÿ\u0080";
        String utf16 = "a€b😀céd\ud800e\udc00f";
        for (String p : List.of(ascii, latin1, utf16)) {
            for (int from = 0; from <= p.length(); from++) {
                for (int end = from; end <= p.length(); end++) {
                    assertEncodesAsJdk(p, from, end);
                }
            }
        }
        Assert.assertTrue("hosted factories make views", StringView.create(ascii, 1, 9) instanceof StringView);
        Assert.assertTrue(StringView.create(latin1, 0, 10) instanceof StringView);
        Assert.assertTrue(StringView.create(utf16, 0, 4) instanceof StringView);
    }

    @Test
    public void variantAndProfileLine() throws Exception {
        Assert.assertEquals("STORED", StringViewHeuristic.svVariant(true));
        Assert.assertNull(StringViewHeuristic.svVariant(false));
        Assert.assertTrue(StringAnalysisFeature.storedAccumulatorWins(null, "STORED"));
        Assert.assertFalse(StringAnalysisFeature.storedAccumulatorWins("STORED", null));
        Path tmp = Files.createTempFile("svsc", ".profile");
        try {
            Files.writeString(tmp, "A#m()V@3 STRING_VIEW STORED\nA#m()V@9 STRING_VIEW\n");
            RepresentationProfile p = RepresentationProfileLoader.load(tmp.toString());
            ProfileEntry stored = p.getEntry("A#m()V@3", OptimizationType.STRING_VIEW);
            ProfileEntry plain = p.getEntry("A#m()V@9", OptimizationType.STRING_VIEW);
            Assert.assertTrue(StringRepresentationReplacementPlugin.isStoredVariant(stored));
            Assert.assertFalse("an old plain line keeps its meaning", StringRepresentationReplacementPlugin.isStoredVariant(plain));
        } finally {
            Files.deleteIfExists(tmp);
        }
    }

    private static void assertJdkCopy(String expected, String got) {
        Assert.assertEquals(String.class, got.getClass());
        Assert.assertEquals(expected, got);
        Assert.assertArrayEquals(expected.getBytes(StandardCharsets.UTF_16BE), got.getBytes(StandardCharsets.UTF_16BE));
    }

    @Test
    public void storedFactoriesCopyShortOrSparseRanges() {
        String p = "0123456789abcdefghij"; // 20 Latin-1 bytes
        // empty -> "" (always under half); 8 of 20 bytes: under half -> a copy
        Assert.assertSame("", StringView.createStored(p, 4, 4));
        Assert.assertSame("", StringView.createStored(p, 20));
        assertJdkCopy("01234567", StringView.createStored(p, 0, 8));
        // >= 9 bytes but under half of the 20-byte backing: a copy
        assertJdkCopy("123456789", StringView.createStored(p, 1, 10));
        // at least half: a view
        Assert.assertTrue(StringView.createStored(p, 0, 10) instanceof StringView);
        RepEq.assertRepEquals("0123456789", StringView.createStored(p, 0, 10));
        Assert.assertTrue(StringView.createStored(p, 5) instanceof StringView);
        // the confined factory: always a view
        Assert.assertTrue(StringView.create(p, 1, 3) instanceof StringView);
        // UTF-16: the rule in bytes (len << 1); a Latin-1-only UTF-16 range compresses as the JDK does
        String u = "€123456789€"; // 11 chars, 22 bytes
        assertJdkCopy("1234", StringView.createStored(u, 1, 5)); // 8 bytes
        assertJdkCopy("€123", StringView.createStored(u, 0, 4)); // 8 bytes, UTF-16 copy
        Assert.assertTrue(StringView.createStored(u, 0, 6) instanceof StringView); // 12 bytes >= 11
        assertJdkCopy("12345", StringView.createStored(u, 1, 6)); // 10 bytes < 11: a copy, Latin-1-only: compact
        assertJdkCopy("€1234", StringView.createStored(u, 0, 5)); // 10 bytes < 11: copy
        // nested: a view parent through createStored and createViewStored
        String v = StringView.create(p, 0, 20);
        Assert.assertTrue(v instanceof StringView);
        assertJdkCopy("cde", StringView.createStored(v, 12, 15));
        assertJdkCopy("cde", StringView.createViewStored((StringView) v, 12, 15));
        Assert.assertTrue(StringView.createViewStored((StringView) v, 2) instanceof StringView);
        RepEq.assertRepEquals("23456789abcdefghij", StringView.createViewStored((StringView) v, 2));
        // bounds as the view factories
        Assert.assertThrows(StringIndexOutOfBoundsException.class, () -> StringView.createStored(p, 3, 2));
        Assert.assertThrows(StringIndexOutOfBoundsException.class, () -> StringView.createViewStored((StringView) v, 0, 21));
        Assert.assertThrows(NullPointerException.class, () -> StringView.createStored(null, 0));
        // no minimum length: a short range covering at least half of its backing is a view
        Assert.assertTrue(StringView.createStored("abcd", 0, 2) instanceof StringView);
    }

    @Test
    public void stringConcatFactoryReturnsTheReceiverForAnEmptyArgument() {
        String x = new String("abc");
        Assert.assertSame(x, LazyConcatFactory.stringConcat(x, ""));
        RepEq.assertRepEquals("abcd", LazyConcatFactory.stringConcat(x, "d").toString());
        Assert.assertEquals("d", LazyConcatFactory.stringConcat("", "d"));
    }
}
