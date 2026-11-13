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

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;

/**
 * The premise test for the parent plugin's 1-arg {@code String.substring(int)}
 * replacement. The plugin's {@code resolve*} helpers resolve their factories with
 * {@code getDeclaredMethod(...)} and silently no-op (the site stays unreplaced) if the lookup fails, so
 * a rep-factory refactor that changes a signature would silently disable the replacement. This test pins, on the
 * running JVM:
 * <ol>
 * <li>the arity premise of the match table: {@code java.lang.String} declares {@code substring(I)} and
 * {@code substring(II)} / {@code subSequence(II)} but no 1-arg {@code subSequence}, which is why the
 * plugin's 1-arg branch matches {@code substring} by name and the 2-arg branch also admits
 * {@code subSequence};</li>
 * <li>the factories exist with the exact parameter shapes the plugin dispatches to (and are static);</li>
 * <li>the content and exception-class parity of
 {@link StringView#create(String, int)} /
 * {@link StringView#createView(StringView, int)} with the JDK's {@code substring(int)} (the bounds-exception
 * message text is an accepted divergence — classes only here), including a
 * view parent (the nesting path) and the null receiver (NPE: the replaced virtual-dispatch semantics);</li>
 * <li>the SINGLE_BYTE mapping: {@link SingleByteString#createFromSubstring(String, int)} returns exactly the
 * parent's char at {@code start} (the admit proves a length-1 result), with the JDK's exception classes.</li>
 * </ol>
 */
public class SubstringOneArgPremiseTest {

    private static Method exact(Class<?> owner, String name, Class<?>... params) throws NoSuchMethodException {
        return owner.getDeclaredMethod(name, params);
    }

    private static Method staticExact(Class<?> owner, String name, Class<?>... params) throws NoSuchMethodException {
        Method m = exact(owner, name, params);
        Assert.assertTrue(name + " must be static", Modifier.isStatic(m.getModifiers()));
        return m;
    }

    @Test
    public void stringDeclaresExactlyTheSubstringAritiesThePluginMatches() throws Exception {
        Class<?> s = String.class;
        Method sub1 = exact(s, "substring", int.class); // virtual, like sub2/seq2 (only the factories are static)
        Assert.assertEquals(String.class, sub1.getReturnType());
        Method sub2 = exact(s, "substring", int.class, int.class);
        Assert.assertEquals(String.class, sub2.getReturnType());
        Method seq2 = exact(s, "subSequence", int.class, int.class);
        Assert.assertEquals(CharSequence.class, seq2.getReturnType());
        try {
            s.getDeclaredMethod("subSequence", int.class);
            Assert.fail("String.subSequence(I) must NOT exist: the plugin's 1-arg branch matches substring by name only");
        } catch (NoSuchMethodException expected) {
        }
    }

    @Test
    public void theFactoriesResolveWithTheExactShapesThePluginDispatchesTo() throws Exception {
        Assert.assertEquals(String.class, staticExact(StringView.class, "create", String.class, int.class).getReturnType()); // a view or the compact copy
        Assert.assertEquals(String.class, staticExact(StringView.class, "createView", StringView.class, int.class).getReturnType());
        // the pre-existing shapes the same dispatch block uses (the 2-arg form and SINGLE_BYTE)
        Assert.assertEquals(String.class, staticExact(StringView.class, "create", String.class, int.class, int.class).getReturnType());
        Assert.assertEquals(String.class, staticExact(StringView.class, "createView", StringView.class, int.class, int.class).getReturnType());
        Assert.assertEquals(String.class, staticExact(SingleByteString.class, "createFromSubstring", String.class, int.class).getReturnType());
    }

    private static void assertClass(String label, Class<? extends Throwable> want, Runnable r) {
        try {
            r.run();
            Assert.fail(label + ": no exception (expected " + want.getSimpleName() + ")");
        } catch (Throwable t) {
            Assert.assertEquals(label + ": the exception class (the message text is the accepted divergence)", want, t.getClass());
        }
    }

    @Test
    public void create1MatchesSubstring1ContentAndExceptionClasses() {
        String flat = "hello";
        // content parity, every begin shape (the rep is always the EQUALS receiver: plain String.equals
        // would read the view's null value(); the view's own override is the whitelisted correct one)
        Assert.assertTrue(StringView.create(flat, 1).equals(flat.substring(1)));
        Assert.assertTrue(StringView.create(flat, 0).equals(flat.substring(0)));
        Assert.assertTrue(StringView.create(flat, 5).equals(flat.substring(5))); // begin == length: the empty view
        Assert.assertTrue(StringView.create(flat, 5).isEmpty());
        // the length-1 result (the SINGLE_BYTE admit shape, here as a view)
        Assert.assertTrue(StringView.create(flat, 4).equals(flat.substring(4)));
        Assert.assertEquals(1, StringView.create(flat, 4).length());
        // a view parent: the nesting path of create(String,int,int)'s instanceof branch
        StringView mid = (StringView) StringView.create(flat, 1, 4); // "ell"
        Assert.assertTrue(StringView.create(mid, 2).equals(mid.substring(2))); // create1 over a view
        Assert.assertTrue(((String) StringView.createView(mid, 2)).equals(mid.substring(2))); // the exact-receiver overload
        Assert.assertTrue(((String) StringView.createView(mid, 0)).equals(mid.substring(0)));
        // the null receiver: NPE, the class of the replaced virtual dispatch (create1 reads parent.length() first)
        assertClass("create1(null, 1)", NullPointerException.class, () -> StringView.create(null, 1));
        // bounds: both sides, class only (the message text differs from the JDK's — the accepted divergence)
        assertClass("create1(-1)", StringIndexOutOfBoundsException.class, () -> StringView.create(flat, -1));
        assertClass("create1(6)", StringIndexOutOfBoundsException.class, () -> StringView.create(flat, 6));
        assertClass("createView1(view, -1)", StringIndexOutOfBoundsException.class, () -> StringView.createView(mid, -1));
        assertClass("createView1(view, 9)", StringIndexOutOfBoundsException.class, () -> StringView.createView(mid, 9));
    }

    @Test
    public void singleByteMappingReturnsTheCharAtStart() {
        Assert.assertTrue(SingleByteString.createFromSubstring("hello", 4).equals("o"));
        Assert.assertEquals(1, SingleByteString.createFromSubstring("hello", 4).length());
        Assert.assertTrue(SingleByteString.createFromSubstring("\u00ffx", 0).equals("\u00ff")); // the latin1 pool path
        Assert.assertTrue(SingleByteString.createFromSubstring("a\u1234", 1).equals("\u1234")); // > 0xFF: the fallback
        assertClass("createFromSubstring(hello, 9)", StringIndexOutOfBoundsException.class,
                        () -> SingleByteString.createFromSubstring("hello", 9));
        assertClass("createFromSubstring(null, 0)", NullPointerException.class,
                        () -> SingleByteString.createFromSubstring(null, 0));
    }
}
