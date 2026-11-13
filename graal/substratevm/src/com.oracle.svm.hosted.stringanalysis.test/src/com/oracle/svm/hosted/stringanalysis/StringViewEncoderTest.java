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
import java.util.List;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * The single-pass range encoder of {@link StringView} (UTF-8, ISO-8859-1,
 * US-ASCII over a Latin-1 or UTF-16 backing range) equals the JDK byte for byte on random ranges, incl. surrogate pairs,
 * unpaired surrogates at the range edges, non-ASCII Latin-1 and the empty range. Hosted: the plain-loop fallbacks of
 * the two JDK intrinsics; the image-runtime aliases are checked in a native image.
 */
public class StringViewEncoderTest {

    private static final List<Charset> CHARSETS = List.of(StandardCharsets.UTF_8, StandardCharsets.ISO_8859_1, StandardCharsets.US_ASCII);

    private static char pick(Random r, boolean latin1) {
        int k = r.nextInt(latin1 ? 4 : 10);
        switch (k) {
            case 0, 1, 2:
                return (char) (0x20 + r.nextInt(0x5f)); // ASCII (weighted)
            case 3:
                return (char) (0x80 + r.nextInt(0x80)); // Latin-1 high
            case 4:
                return (char) (0x100 + r.nextInt(0x700)); // 2-byte UTF-8
            case 5:
                return (char) (0x800 + r.nextInt(0xd000 - 0x800)); // 3-byte UTF-8
            case 6:
                return (char) (0xd800 + r.nextInt(0x400)); // high surrogate
            case 7:
                return (char) (0xdc00 + r.nextInt(0x400)); // low surrogate
            default:
                return (char) (0x20 + r.nextInt(0x5f));
        }
    }

    private static String random(Random r, int n, boolean latin1) {
        StringBuilder sb = new StringBuilder(n);
        while (sb.length() < n) {
            if (!latin1 && r.nextInt(8) == 0) {
                sb.appendCodePoint(0x10000 + r.nextInt(0xF0000)); // a valid pair
            } else {
                sb.append(pick(r, latin1));
            }
        }
        return sb.toString();
    }

    private static int check(String parent, int from, int end) {
        String v = StringView.create(parent, from, end);
        String jdk = parent.substring(from, end);
        for (Charset cs : CHARSETS) {
            Assert.assertArrayEquals(cs + " [" + from + "," + end + ") of " + parent.length(), jdk.getBytes(cs), v.getBytes(cs));
        }
        return v instanceof StringView ? 1 : 0;
    }

    @Test
    public void randomRangesEncodeAsTheJdk() {
        Random r = new Random(0xC96E);
        int views = 0;
        for (int iter = 0; iter < 3000; iter++) {
            boolean latin1 = iter % 2 == 0;
            int n = iter % 50 == 0 ? 2000 + r.nextInt(3000) : r.nextInt(64);
            String p = random(r, n, latin1);
            for (int k = 0; k < 8; k++) {
                int from = r.nextInt(n + 1);
                int end = from + r.nextInt(n - from + 1);
                views += check(p, from, end);
            }
            views += check(p, 0, n);
        }
        // pure-ASCII ranges of a Latin-1 and of a UTF-16 backing (the fast loops alone)
        String ascii = "the quick brown fox jumps over the lazy dog 0123456789".repeat(40);
        views += check(ascii, 3, ascii.length() - 1);
        views += check(ascii + "€", 0, ascii.length() + 1);
        // surrogates at both range edges: a pair cut in half, a lone high at the end, a lone low at the start
        String s = "a😀b𐀀c\ud83d";
        for (int from = 0; from <= s.length(); from++) {
            for (int end = from; end <= s.length(); end++) {
                views += check(s, from, end);
            }
        }
        Assert.assertTrue("most ranges are views: " + views, views > 10000);
    }
}
