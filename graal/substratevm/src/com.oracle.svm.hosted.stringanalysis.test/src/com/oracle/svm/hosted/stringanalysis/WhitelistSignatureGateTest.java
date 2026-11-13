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

public class WhitelistSignatureGateTest {

    private static final String STRING = "java.lang.String";

    @Test
    public void stringViewGetBytesC1Regression() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", STRING, "I,I,[B,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("getBytes", STRING, "I,I,[B,[I"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", STRING, ""));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", STRING, "Ljava/nio/charset/Charset;"));
    }

    @Test
    public void stringViewIndexOfSignatures() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("indexOf", STRING, "I"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("indexOf", STRING, "Ljava/lang/String;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("indexOf", STRING, "I,I,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("indexOf", STRING, "I,I,I,I"));
    }

    @Test
    public void stringViewStartsWithAndReplace() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("startsWith", STRING, "Ljava/lang/String;"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("replace", STRING, "CC"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("replace", STRING, "Ljava/lang/String;,Ljava/lang/String;"));
    }

    @Test
    public void stringViewGetCharsSignatureGate() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getChars", STRING, "I,I,[C,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("getChars", STRING, "I,I,[C"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("getChars", STRING, "I,I,[B,I"));
    }

    @Test
    public void stringViewRepeatSignatureGate() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("repeat", STRING, "I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("repeat", STRING, "I,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("repeat", STRING, null));
    }

    @Test
    public void stringViewLastIndexOfSignatureGate() {
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("lastIndexOf", STRING, "C"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("lastIndexOf", STRING, "I"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("lastIndexOf", STRING, "I,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("lastIndexOf", STRING, "Ljava/lang/String;"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("lastIndexOf", STRING, "I,I,I"));
    }

    @Test
    public void stringViewEndsWithSignatureGate() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("endsWith", STRING, "Ljava/lang/String;"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("endsWith", STRING, "Ljava/lang/String;,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("endsWith", STRING, "I"));
    }

    @Test
    public void stringViewNonStringDeclaringClassRejected() {
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("length", "java.lang.StringBuilder", null));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("length", null, null));
    }

    @Test
    public void stringViewNameOnlyMembers() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("length", STRING, ""));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("toUpperCase", STRING, ""));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("substring", STRING, "I,I"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("substring", STRING, null));
    }

    @Test
    public void lazyConcatWhitelistSignatures() {
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("charAt", STRING, "I"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, ""));
        // the protected getBytes([B,I,B) is overridden by every lazy rep, RopeString included.
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "[B,I,B"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "[B,I,B", "ROPE"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "[B,I,B", "THREE_WAY"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "I,I,[B,I"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "Ljava/nio/charset/Charset;"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getBytes", STRING, "Ljava/lang/String;"));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("getChars", STRING, "I,I,[C,I"));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("replace", STRING, "CC"));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("charAt", "java.lang.StringBuilder", "I"));
        // no String constructor is a lazy whitelist row (String(String) reads original.value()).
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("<init>", STRING, "Ljava/lang/String;"));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("<init>", STRING, ""));
    }

    @Test
    public void lazyConcatLengthAndBroadenedGetBytes() {
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("length", STRING, null));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("length", STRING, ""));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("length", "java.lang.StringBuilder", null));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("length", null, null));
    }

    @Test
    public void accumulatorWhitelistBasics() {
        Assert.assertTrue(AccumulatorWhitelist.isAccumulatorType("java.lang.StringBuilder"));
        Assert.assertTrue(AccumulatorWhitelist.isAccumulatorType("java.lang.StringBuffer"));
        Assert.assertTrue(AccumulatorWhitelist.isAccumulatorType("java.io.StringWriter"));
        Assert.assertFalse(AccumulatorWhitelist.isAccumulatorType("java.lang.String"));
        Assert.assertFalse(AccumulatorWhitelist.isAccumulatorType(null));

        Assert.assertTrue(AccumulatorWhitelist.isWhitelisted("append"));
        Assert.assertTrue(AccumulatorWhitelist.isWhitelisted("toString"));
        Assert.assertFalse(AccumulatorWhitelist.isWhitelisted("insert"));
        Assert.assertFalse(AccumulatorWhitelist.isWhitelisted(null));

        Assert.assertTrue(AccumulatorWhitelist.isExtraction("toString"));
        Assert.assertTrue(AccumulatorWhitelist.isExtraction("substring"));
        Assert.assertTrue(AccumulatorWhitelist.isExtraction("subSequence"));
        Assert.assertFalse(AccumulatorWhitelist.isExtraction("append"));
    }

    @Test
    public void accumulatorWhitelistRecognizesAbstractStringBuilder() {
        Assert.assertTrue(AccumulatorWhitelist.isAccumulatorType("java.lang.AbstractStringBuilder"));
    }
}
