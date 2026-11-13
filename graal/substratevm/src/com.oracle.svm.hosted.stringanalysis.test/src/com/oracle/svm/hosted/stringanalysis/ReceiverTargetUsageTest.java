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

/**
 * The stringy declaring types of a resolved-target usage, and the verdict layer's signature-gated whitelists (W_view,
 * the per-variant W_lazy). The STRING atoms' terminal rows are pinned by StringAtomsTest and
 * HandListLeakWhitelistTest.
 */
public class ReceiverTargetUsageTest {

    /** PIN 6: the stringy declaring types. */
    @Test
    public void stringyDeclaringTypes() {
        for (String t : new String[]{"java.lang.String", "java.lang.StringBuilder", "java.lang.StringBuffer", "java.lang.AbstractStringBuilder",
                        "java.io.StringWriter", "com.oracle.svm.core.stringrep.StringView"}) {
            Assert.assertTrue(t, ForwardFixpoint.isStringyDeclaringType(t));
        }
        for (String t : new String[]{"java.lang.Object", "java.lang.CharSequence", "java.lang.Comparable", "com.example.Helper"}) {
            Assert.assertFalse(t, ForwardFixpoint.isStringyDeclaringType(t));
        }
    }

    /**
     * PIN 7: the signature-gated verdict. W_view rejects the method usage {@code value()} and the non-table methods;
     * W_lazy gates getBytes by signature and variant (RopeString inherits the protected [B,I,B), the package-private
     * 5-arg overload is never allowed) and keeps the common overloads.
     */
    @Test
    public void signatureGatedWhitelists() {
        String s = "java.lang.String";
        for (String[] m : new String[][]{{"value", ""}, {"stripIndent", ""}, {"chars", ""}, {"bytesCompatible", "Ljava/nio/charset/Charset;"},
                        {"formatted", "[Ljava/lang/Object;"}}) {
            Assert.assertFalse(m[0], StringViewWhitelist.isWhitelisted(m[0], s, m[1]));
        }
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", s, "[B,I,B"));
        // the ranged copy is protected in the builder JDK and overridden by every value-null rep
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", s, "[B,I,I,B,I"));
        // the Comparable bridge is admitted at the verdict layer only (Phase-A site creation unchanged)
        Assert.assertTrue(StringViewWhitelist.isWhitelistedUsage("compareTo", s, "Ljava/lang/Object;"));
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("compareTo", s, "Ljava/lang/Object;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelistedUsage("compareTo", s, "Ljava/lang/String;"));
        Assert.assertFalse(StringViewWhitelist.isWhitelistedUsage("compareTo", "java.lang.Object", "Ljava/lang/Object;"));
        for (String v : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            Assert.assertTrue(v, LazyConcatWhitelist.isWhitelisted("getBytes", s, "[B,I,I,B,I", v)); // the ranged copy
            Assert.assertTrue(v, LazyConcatWhitelist.isWhitelisted("getBytes", s, "[B,I,B", v)); // RopeString overrides it too
            for (String[] ok : new String[][]{{"length", ""}, {"charAt", "I"}, {"equals", "Ljava/lang/Object;"}, {"toCharArray", ""}, {"hashCode", ""},
                            {"coder", ""}, {"getChars", "I,I,[C,I"}, {"getBytes", ""}, {"getBytes", "Ljava/lang/String;"}, {"getBytes", "Ljava/nio/charset/Charset;"},
                            {"getBytes", "I,I,[B,I"}}) {
                Assert.assertTrue(v + " " + ok[0] + "(" + ok[1] + ")", LazyConcatWhitelist.isWhitelisted(ok[0], s, ok[1], v));
            }
            Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("value", s, "", v));
            Assert.assertFalse("charAt by name only is gone", LazyConcatWhitelist.isWhitelisted("charAt", s, "J", v));
        }
    }
}
