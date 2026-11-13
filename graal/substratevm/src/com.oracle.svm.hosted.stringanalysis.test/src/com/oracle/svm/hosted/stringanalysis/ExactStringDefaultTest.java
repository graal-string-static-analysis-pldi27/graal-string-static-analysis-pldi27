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

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

/** Exact String by default, mirrors at rep sinks: the gates and the builder JDK's invented members. */
public class ExactStringDefaultTest {

    private static RepresentationProfile profile(String... keyTypeVariant) {
        Map<String, ProfileEntry> m = new LinkedHashMap<>();
        for (int i = 0; i < keyTypeVariant.length; i += 3) {
            m.put(keyTypeVariant[i], new ProfileEntry(keyTypeVariant[i], OptimizationType.valueOf(keyTypeVariant[i + 1]), keyTypeVariant[i + 2]));
        }
        return new RepresentationProfile(m);
    }

    @Test
    public void admitsNoRepOnlyWithoutAnyRepName() {
        Assert.assertTrue(profile().admitsNoRep());
        Assert.assertTrue(profile("a#m()V@1", "INLINE_CACHE", "UNKNOWN", "b#m()V@2", "INLINE_CACHE", "KT:UNKNOWN", "c#m()V@3", "INLINE_CACHE", "EXACT_STRING",
                        "d#m()V@4", "INLINE_CACHE", "UNPROVEN").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "INLINE_CACHE", "EXACT,SV").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "INLINE_CACHE", "KT:EXACT,SBS").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "STRING_VIEW", "ACCUMULATOR_VIEW").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "SINGLE_BYTE", "").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "LAZY_CONCAT", "ROPE").admitsNoRep());
        Assert.assertFalse(profile("a#m()V@1", "EQUALS_MATRIX", "REDIRECT").admitsNoRep());
        Map<String, Map<OptimizationType, ProfileEntry>> none = new LinkedHashMap<>();
        Assert.assertFalse("a CONCAT_COPY site names a rep operand", new RepresentationProfile(none, true, Map.of(), Map.of("a#m()V@1", "BINARY")).admitsNoRep());
        Assert.assertFalse("a LAZY_PAIR names a lazy rep", new RepresentationProfile(none, true, Map.of("a#m()V@1", Set.of("b#m()V@2")), Map.of()).admitsNoRep());
    }

    @Test
    public void zeroAdmitGate() {
        RepresentationProfile empty = profile("a#m()V@1", "INLINE_CACHE", "UNKNOWN");
        RepresentationProfile rep = profile("a#m()V@1", "STRING_VIEW", "SUBSTRING");
        Assert.assertTrue(ZeroAdmitStock.applies(2, false, empty));
        Assert.assertFalse("knob 1 = the OFF-only parse-time String binding", ZeroAdmitStock.applies(1, false, empty));
        Assert.assertFalse("never in the analysis child", ZeroAdmitStock.applies(2, true, empty));
        Assert.assertFalse("no profile = not a zero-admit parent", ZeroAdmitStock.applies(2, false, null));
        Assert.assertFalse(ZeroAdmitStock.applies(2, false, rep));
        Assert.assertTrue(OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, false, false, null, true, false, false));
        Assert.assertTrue("an explicit profile", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, false, false, false, "/p.txt", true, false, false));
        Assert.assertFalse(OffStringFinalBindingPlugin.appliesToZeroAdmit(1, true, false, false, null, true, false, false));
        Assert.assertFalse("child", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, true, false, null, true, false, false));
        Assert.assertFalse("child-only", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, false, true, null, true, false, false));
        Assert.assertFalse("open world", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, false, false, null, false, false, false));
        Assert.assertFalse("layered", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, false, false, null, true, true, false));
        Assert.assertFalse("runtime class loading", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, true, false, false, null, true, false, true));
        Assert.assertFalse("OFF is the other registration", OffStringFinalBindingPlugin.appliesToZeroAdmit(2, false, false, false, null, true, false, false));
    }

    @Test
    public void rangeCopyRedirectWhereARepMayExist() {
        RepresentationProfile empty = profile("a#m()V@1", "INLINE_CACHE", "UNKNOWN");
        RepresentationProfile rep = profile("a#m()V@1", "STRING_VIEW", "SUBSTRING");
        // (mode, fork, OFF binding plugin registered (the OFF binding in the messages), ZeroAdmitStock.applies): the stock body only
        // where the OFF binding's subtype check runs
        Assert.assertTrue("the child walks the twin", RangeCopyRedirectPlugin.redirects(1, true, false, false));
        Assert.assertTrue("the child, even with the OFF parse-time String binding", RangeCopyRedirectPlugin.redirects(1, true, true, true));
        Assert.assertTrue("a rep-admitting parent", RangeCopyRedirectPlugin.redirects(1, false, false, ZeroAdmitStock.applies(2, false, rep)));
        Assert.assertFalse("OFF with the OFF parse-time String binding: stock", RangeCopyRedirectPlugin.redirects(1, false, true, false));
        Assert.assertTrue("OFF without the OFF parse-time String binding (off.stringfinal=0): twin", RangeCopyRedirectPlugin.redirects(1, false, false, false));
        Assert.assertFalse("zero-admit, off.stringfinal=2: stock", RangeCopyRedirectPlugin.redirects(1, false, false, ZeroAdmitStock.applies(2, false, empty)));
        Assert.assertTrue("zero-admit, off.stringfinal=1: twin (M-1)", RangeCopyRedirectPlugin.redirects(1, false, false, ZeroAdmitStock.applies(1, false, empty)));
        Assert.assertTrue("zero-admit, off.stringfinal=0: twin (M-1)", RangeCopyRedirectPlugin.redirects(1, false, false, ZeroAdmitStock.applies(0, false, empty)));
        Assert.assertTrue("before the profile load: twin (M-1)", RangeCopyRedirectPlugin.redirects(1, false, false, ZeroAdmitStock.applies(2, false, null)));
        Assert.assertTrue("knob 2 (or runtime compilation): everywhere", RangeCopyRedirectPlugin.redirects(2, false, true, true));
    }

    @Test
    public void builderJdkInventedMembers() throws Exception {
        for (Method m : Object.class.getDeclaredMethods()) {
            Assert.assertFalse("no invented member on Object (stock vtable): " + m, m.getName().startsWith("maybeCustom"));
        }
        Method s = String.class.getMethod(EqualsMatrixNodePlugin.OBJECT_REDIRECT_TARGET, Object.class, Object.class);
        Assert.assertTrue(Modifier.isStatic(s.getModifiers()));
        Assert.assertEquals("the child roots the String-declared equals REDIRECT target", java.util.List.of(String.class.getMethod("maybeCustomStringEquals", Object.class)),
                        EqualsMatrixNodePlugin.redirectTargets());
        Assert.assertTrue(String.objectMaybeCustomStringEquals("ab", "ab"));
        Assert.assertFalse(String.objectMaybeCustomStringEquals("ab", "ac"));
        Assert.assertTrue(String.objectMaybeCustomStringEquals(Integer.valueOf(7), Integer.valueOf(7)));
        Assert.assertFalse(String.objectMaybeCustomStringEquals(Integer.valueOf(7), "7"));
        Assert.assertThrows(NullPointerException.class, () -> String.objectMaybeCustomStringEquals(null, "a"));
        Class<?> asb = Class.forName("java.lang.AbstractStringBuilder");
        Method stock = asb.getDeclaredMethod(RangeCopyRedirectPlugin.NAME, byte[].class, byte.class, int.class, String.class, int.class, int.class);
        Method twin = asb.getDeclaredMethod(RangeCopyRedirectPlugin.TWIN, byte[].class, byte.class, int.class, String.class, int.class, int.class);
        Assert.assertTrue(Modifier.isStatic(stock.getModifiers()) && Modifier.isStatic(twin.getModifiers()));
    }
}
