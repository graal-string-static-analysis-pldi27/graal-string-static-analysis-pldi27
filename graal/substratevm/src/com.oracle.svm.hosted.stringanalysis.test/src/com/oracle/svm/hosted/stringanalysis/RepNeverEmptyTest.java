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

import java.io.StringWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;
import com.oracle.svm.core.stringrep.TrivialString;

/**
 * The invariant "a rep instance is never empty". Every mint path that can produce a
 * zero-length result returns a stock {@code java.lang.String} instead, with the JDK's identity: the literal {@code ""}
 * where the JDK's {@code substring} / builder {@code toString} return it ({@code StringLatin1/StringUTF16.newString}
 * len 0), a fresh empty String where the JDK makes a new one (indy concat {@code new String(buf, coder)},
 * {@code String.join}'s {@code new String(value, coder)}, {@code simpleConcat}'s {@code new String(s2)}). The concat
 * factories rely on it ({@code x.getClass() == String.class && x.isEmpty()} instead of a vtable {@code isEmpty()}).
 * <p>
 * {@link #everyFactoryIsCovered} is the completeness guard: every public static String-returning method of a rep class
 * and of {@link LazyConcatFactory} must have an entry in {@link #CASES}; {@link #repConstructorsArePrivate} makes the
 * factories the only mint paths. Non-public helpers are reached through the public entries, except the joiner path
 * ({@code InterleavedStringArray.createJoined}), which cannot run hosted: only its mint decision
 * ({@code joinerMintsRep}) is pinned.
 */
public class RepNeverEmptyTest {

    private static final String UTF = "aĀb";

    /** The invariant on one factory result: a stock String, or a non-empty rep. */
    static String ok(String r, String what) {
        Assert.assertNotNull(what, r);
        Assert.assertTrue(what + ": an empty " + r.getClass().getName() + " (a rep is never empty)", r.getClass() == String.class || r.length() > 0);
        Assert.assertEquals(what + ": isEmpty() agrees with the exact-class form (F2)", r.isEmpty(), r.getClass() == String.class && r.isEmpty());
        return r;
    }

    /** An empty result that the JDK returns as the literal {@code ""}. */
    static void literal(String r, String what) {
        ok(r, what);
        Assert.assertSame(what + ": the JDK's \"\"", "", r);
    }

    /** An empty result that the JDK returns as a new String: exact String, empty, not the literal. */
    static void fresh(String r, String what) {
        ok(r, what);
        Assert.assertSame(what + ": a plain String", String.class, r.getClass());
        Assert.assertTrue(what + ": empty", r.isEmpty());
        Assert.assertNotSame(what + ": a fresh String, as the JDK's", "", r);
    }

    static String key(Method m) {
        return m.getDeclaringClass().getSimpleName() + "." + m.getName() +
                        Arrays.stream(m.getParameterTypes()).map(Class::getSimpleName).collect(Collectors.joining(",", "(", ")"));
    }

    /** One entry per factory (key = {@link #key}); each runs the factory's empty cases and a non-empty one. */
    static final Map<String, Runnable> CASES = cases();

    private static Map<String, Runnable> cases() {
        Map<String, Runnable> m = new LinkedHashMap<>();
        StringView sv = (StringView) StringView.create("xabcdefy", 1, 7); // a Latin-1 view parent "abcdef"
        // --- substring family: the JDK substring's "" (StringLatin1/StringUTF16.newString len 0)
        m.put("StringView.create(String,int,int)", () -> {
            literal(StringView.create("abc", 1, 1), "Latin-1 from == end");
            literal(StringView.create(UTF, 1, 1), "UTF-16 from == end");
            literal(StringView.create("", 0, 0), "empty parent");
            literal(StringView.create(sv, 2, 2), "view parent from == end");
            literal(StringView.create("abc", 3, 3), "at the end");
            Assert.assertSame(StringView.class, ok(StringView.create("abc", 0, 2), "non-empty").getClass());
        });
        m.put("StringView.create(String,int)", () -> {
            literal(StringView.create("abc", 3), "from == length");
            literal(StringView.create(sv, sv.length()), "view parent, from == length");
            ok(StringView.create("abc", 1), "non-empty");
        });
        m.put("StringView.createView(StringView,int,int)", () -> {
            literal(StringView.createView(sv, 3, 3), "from == end");
            ok(StringView.createView(sv, 1, 3), "non-empty");
        });
        m.put("StringView.createView(StringView,int)", () -> {
            literal(StringView.createView(sv, sv.length()), "from == length");
            ok(StringView.createView(sv, 2), "non-empty");
        });
        m.put("StringView.createStored(String,int,int)", () -> {
            literal(StringView.createStored("", 0, 0), "empty backing (cap 0: was an empty view)");
            literal(StringView.createStored("abcdef", 2, 2), "from == end");
            ok(StringView.createStored("abcdef", 0, 5), "non-empty");
        });
        m.put("StringView.createStored(String,int)", () -> {
            literal(StringView.createStored("", 0), "empty backing");
            literal(StringView.createStored("abc", 3), "from == length");
            ok(StringView.createStored("abcdef", 1), "non-empty");
        });
        m.put("StringView.createViewStored(StringView,int,int)", () -> {
            literal(StringView.createViewStored(sv, 1, 1), "from == end");
            ok(StringView.createViewStored(sv, 0, 5), "non-empty");
        });
        m.put("StringView.createViewStored(StringView,int)", () -> {
            literal(StringView.createViewStored(sv, sv.length()), "from == length");
            ok(StringView.createViewStored(sv, 1), "non-empty");
        });
        // --- builder views: an empty builder gives the JDK toString's ""
        m.put("StringView.create(StringBuilder)", () -> {
            literal(StringView.create(new StringBuilder()), "empty builder");
            ok(StringView.create(new StringBuilder("abcdefgh")), "non-empty");
        });
        m.put("StringView.create(StringBuffer)", () -> {
            literal(StringView.create(new StringBuffer()), "empty buffer");
            ok(StringView.create(new StringBuffer("abcdefgh")), "non-empty");
        });
        m.put("StringView.create(StringWriter)", () -> {
            literal(StringView.create(new StringWriter()), "empty writer");
            StringWriter w = new StringWriter();
            w.write("abcdefgh");
            ok(StringView.create(w), "non-empty");
        });
        m.put("StringView.createSkipCheck(StringBuilder)", () -> {
            literal(StringView.createSkipCheck(new StringBuilder(64)), "empty builder");
            ok(StringView.createSkipCheck(new StringBuilder("ab")), "non-empty");
        });
        m.put("StringView.createSkipCheck(StringBuffer)", () -> {
            literal(StringView.createSkipCheck(new StringBuffer(64)), "empty buffer");
            ok(StringView.createSkipCheck(new StringBuffer("ab")), "non-empty");
        });
        m.put("StringView.createSkipCheck(StringWriter)", () -> {
            literal(StringView.createSkipCheck(new StringWriter()), "empty writer");
            StringWriter w = new StringWriter();
            w.write("ab");
            ok(StringView.createSkipCheck(w), "non-empty");
        });
        m.put("StringView.ofBuilderSnapshot(byte[],byte,int,boolean)", () -> {
            literal(StringView.ofBuilderSnapshot(new byte[16], (byte) 0, 0, true), "count 0");
            literal(StringView.ofBuilderSnapshot(new byte[16], (byte) 1, 0, false), "count 0, UTF-16, no maybeLatin1");
            ok(StringView.ofBuilderSnapshot("abcdefgh".getBytes(), (byte) 0, 8, true), "non-empty");
        });
        m.put("StringView.ofBuilderSnapshot(byte[],byte,int,boolean,boolean)", () -> {
            literal(StringView.ofBuilderSnapshot(new byte[16], (byte) 0, 0, true, false), "count 0, no trim");
            literal(StringView.ofBuilderSnapshot(new byte[0], (byte) 0, 0, false, true), "count 0, empty array");
            ok(StringView.ofBuilderSnapshot("ab".getBytes(), (byte) 0, 2, true, false), "non-empty");
        });
        // --- one-char reps: length 1 by construction
        m.put("SingleByteString.create(byte)", () -> {
            for (int i = 0; i < 256; i++) {
                Assert.assertEquals(1, ok(SingleByteString.create((byte) i), "byte " + i).length());
            }
        });
        m.put("SingleByteString.create(char)", () -> Assert.assertEquals(1, ok(SingleByteString.create('ÿ'), "char").length()));
        m.put("SingleByteString.createFromSubstring(String,int)", () -> {
            Assert.assertEquals(1, ok(SingleByteString.createFromSubstring("abc", 2), "Latin-1").length());
            Assert.assertEquals(1, ok(SingleByteString.createFromSubstring(UTF, 1), "UTF-16").length());
        });
        m.put("SingleByteString.createFromChar(char)", () -> {
            Assert.assertEquals(1, ok(SingleByteString.createFromChar('\0'), "NUL").length());
            Assert.assertEquals(1, ok(SingleByteString.createFromChar('Ā'), "UTF-16").length());
        });
        m.put("TrivialString.create(byte)", () -> Assert.assertEquals(1, ok(TrivialString.create((byte) 0), "NUL").length()));
        // --- lazy concat reps: all parts empty -> the literal "" (identity of empty results is out of scope)
        m.put("RopeString.create(String,String)", () -> {
            literal(RopeString.create("", ""), "both empty");
            Assert.assertSame(RopeString.class, ok(RopeString.create("", "x"), "one empty side").getClass());
        });
        m.put("ThreeWayString.create(String,String,String)", () -> {
            literal(ThreeWayString.create("", "", ""), "all empty");
            Assert.assertSame(ThreeWayString.class, ok(ThreeWayString.create("", "x", ""), "one non-empty").getClass());
        });
        m.put("FixedConcat4.create(String,String,String,String)", () -> {
            literal(FixedConcat4.create("", "", "", ""), "all empty");
            Assert.assertSame(FixedConcat4.class, ok(FixedConcat4.create("", "", "", UTF), "one non-empty").getClass());
        });
        m.put("ArrayLazyString.create(String[])", () -> {
            literal(ArrayLazyString.create(new String[0]), "no parts");
            literal(ArrayLazyString.create(new String[]{"", "", "", "", ""}), "all empty");
            ok(ArrayLazyString.create(new String[]{"", "a", ""}), "non-empty");
        });
        m.put("ArrayLazyString.createOwned(String[])", () -> {
            literal(ArrayLazyString.createOwned(new String[]{"", ""}), "all empty");
            ok(ArrayLazyString.createOwned(new String[]{"a"}), "non-empty");
        });
        m.put("InterleavedStringArray.create(String[],String)", () -> {
            literal(InterleavedStringArray.create(new String[0], ","), "no elements");
            literal(InterleavedStringArray.create(new String[]{""}, ","), "one empty element");
            literal(InterleavedStringArray.create(new String[]{"", "", ""}, ""), "empty elements, empty delimiter");
            Assert.assertSame(InterleavedStringArray.class, ok(InterleavedStringArray.create(new String[]{"", ""}, ","), "two empties, a delimiter").getClass());
        });
        m.put("InterleavedStringArray.createOwned(String[],int,String)", () -> {
            literal(InterleavedStringArray.createOwned(new String[0], 0, null), "no elements");
            literal(InterleavedStringArray.createOwned(new String[]{"", "x"}, 1, null), "one empty element of a growth array");
            literal(InterleavedStringArray.createOwned(new String[]{"", ""}, 2, ""), "empty elements, empty delimiter");
            ok(InterleavedStringArray.createOwned(new String[]{"a", "b"}, 2, ""), "non-empty");
        });
        m.put("InterleavedStringArray.ofJoiner(StringJoiner)", () -> {
            // the joiner alias only works in an image: the mint decision is pinned instead. Size 0 and a len below the
            // floor are the JDK body. The joiner's len is not a lower bound of the join's length (after a
            // caught OutOfMemoryError in StringJoiner.add, size 1, elts[0] == "" and len >= the floor are possible), so
            // createJoined also returns the JDK body when the computed length is 0 (not runnable hosted)
            Assert.assertFalse(InterleavedStringArray.joinerMintsRep(0, 0));
            Assert.assertFalse(InterleavedStringArray.joinerMintsRep(0, 100));
            Assert.assertFalse(InterleavedStringArray.joinerMintsRep(3, InterleavedStringArray.JOINER_MIN_CHARS - 1));
            Assert.assertTrue(InterleavedStringArray.JOINER_MIN_CHARS > 0);
        });
        // --- the hosted factories the lowering calls
        m.put("LazyConcatFactory.rope(String,String)", () -> {
            fresh(LazyConcatFactory.rope("", ""), "both empty");
            fresh(LazyConcatFactory.rope("", new String()), "both empty, fresh right");
            ok(LazyConcatFactory.rope("", rep()), "empty + rep");
            ok(LazyConcatFactory.rope(rep(), ""), "rep + empty");
        });
        m.put("LazyConcatFactory.ropeInlinePrologue(String,String)", () -> {
            fresh(LazyConcatFactory.ropeInlinePrologue("", ""), "both empty");
            ok(LazyConcatFactory.ropeInlinePrologue("", rep()), "empty + rep");
            ok(LazyConcatFactory.ropeInlinePrologue(rep(), ""), "rep + empty");
        });
        m.put("LazyConcatFactory.stringConcat(String,String)", () -> {
            String a = new String();
            Assert.assertSame("String.concat(\"\") returns the receiver", a, ok(LazyConcatFactory.stringConcat(a, ""), "empty.concat(empty)"));
            String r = rep();
            Assert.assertSame("String.concat(\"\") returns the receiver", r, LazyConcatFactory.stringConcat(r, ""));
            ok(LazyConcatFactory.stringConcat("", r), "empty.concat(rep)");
        });
        // the factories below delegate to the reps' create/createOwned, whose empty result is the literal ""
        m.put("LazyConcatFactory.threeWay(String,String,String)", () -> {
            literal(LazyConcatFactory.threeWay("", "", ""), "all empty");
            ok(LazyConcatFactory.threeWay("", rep(), ""), "non-empty");
        });
        m.put("LazyConcatFactory.fixed4(String,String,String,String)", () -> {
            literal(LazyConcatFactory.fixed4("", "", "", ""), "all empty");
            ok(LazyConcatFactory.fixed4("", "", "", "d"), "non-empty");
        });
        m.put("LazyConcatFactory.arrayLazy(String[])", () -> {
            literal(LazyConcatFactory.arrayLazy(new String[]{"", "", "", "", ""}), "all empty");
            ok(LazyConcatFactory.arrayLazy(new String[]{"", "", "e"}), "non-empty");
        });
        m.put("LazyConcatFactory.interleaved(String[],String)", () -> {
            literal(LazyConcatFactory.interleaved(new String[]{"", "", ""}, ""), "all empty");
            ok(LazyConcatFactory.interleaved(new String[]{"", "", ""}, ","), "delimiters only");
        });
        m.put("LazyConcatFactory.join(CharSequence,CharSequence[])", () -> {
            literal(LazyConcatFactory.join(",", new CharSequence[0]), "0 elements");
            literal(LazyConcatFactory.join(",", new CharSequence[]{new StringBuilder()}), "1 empty element");
            literal(LazyConcatFactory.join("", new CharSequence[]{"", "", ""}), "empty elements, empty delimiter");
            ok(LazyConcatFactory.join(",", new CharSequence[]{"", ""}), "delimiter only");
        });
        m.put("LazyConcatFactory.join(CharSequence,Iterable)", () -> {
            literal(LazyConcatFactory.join(",", List.of()), "0 elements");
            literal(LazyConcatFactory.join(",", List.of("")), "1 empty element");
            literal(LazyConcatFactory.join(new StringBuilder(), List.of("", "", "")), "empty elements, empty delimiter");
            ok(LazyConcatFactory.join(",", List.of("", "")), "delimiter only");
        });
        // --- operand converters: they mint nothing (the operand itself or a JDK String)
        m.put("LazyConcatFactory.str(String)", () -> {
            literal(LazyConcatFactory.str(""), "the operand itself");
            ok(LazyConcatFactory.str((String) null), "null");
        });
        m.put("LazyConcatFactory.str(Object)", () -> {
            literal(LazyConcatFactory.str((Object) ""), "the toString() result");
            ok(LazyConcatFactory.str((Object) null), "null");
        });
        m.put("LazyConcatFactory.str(int)", () -> ok(LazyConcatFactory.str(0), "int"));
        m.put("LazyConcatFactory.str(long)", () -> ok(LazyConcatFactory.str(0L), "long"));
        m.put("LazyConcatFactory.str(char)", () -> ok(LazyConcatFactory.str('\0'), "char"));
        m.put("LazyConcatFactory.str(boolean)", () -> ok(LazyConcatFactory.str(false), "boolean"));
        m.put("LazyConcatFactory.str(float)", () -> ok(LazyConcatFactory.str(0f), "float"));
        m.put("LazyConcatFactory.str(double)", () -> ok(LazyConcatFactory.str(0d), "double"));
        return m;
    }

    private static String rep() {
        return RopeString.create("x", "y");
    }

    @Test
    public void everyFactoryKeepsTheInvariant() {
        for (Map.Entry<String, Runnable> e : CASES.entrySet()) {
            try {
                e.getValue().run();
            } catch (AssertionError err) {
                throw new AssertionError(e.getKey() + ": " + err.getMessage(), err);
            }
        }
    }

    /**
     * The identity premise of the fresh/literal choice, on this JDK: an empty indy concat and an empty
     * {@code String.join} are new Strings; an empty {@code substring} and an empty builder's {@code toString} are the
     * literal.
     */
    @Test
    public void jdkIdentityPremise() {
        String e = new StringBuilder().toString();
        Assert.assertSame("builder toString", "", e);
        String x = "xyz";
        Assert.assertSame("substring(i, i)", "", x.substring(1, 1));
        Assert.assertSame("substring(length)", "", x.substring(3));
        String f = new String();
        Assert.assertNotSame("indy 3 parts", "", f + f + f);
        Assert.assertNotSame("indy 4 parts", "", f + f + f + f);
        Assert.assertNotSame("simpleConcat", "", e + f);
        Assert.assertNotSame("join, 0 elements", "", String.join(",", new String[0]));
        Assert.assertNotSame("join, 1 empty", "", String.join(",", ""));
        Assert.assertNotSame("join, iterable", "", String.join("", List.of("", "")));
        Assert.assertSame("String.concat(empty) is the receiver", f, f.concat(""));
    }

    /** Every rep factory/creation method has an entry (and no entry is stale). */
    @Test
    public void everyFactoryIsCovered() {
        List<Class<?>> classes = new ArrayList<>(RepPinSupport.repClasses());
        classes.add(LazyConcatFactory.class);
        TreeSet<String> found = new TreeSet<>();
        for (Class<?> c : classes) {
            for (Method m : c.getDeclaredMethods()) {
                if (Modifier.isPublic(m.getModifiers()) && Modifier.isStatic(m.getModifiers()) && String.class.isAssignableFrom(m.getReturnType())) {
                    found.add(key(m));
                }
            }
        }
        TreeSet<String> missing = new TreeSet<>(found);
        missing.removeAll(CASES.keySet());
        TreeSet<String> stale = new TreeSet<>(CASES.keySet());
        stale.removeAll(found);
        Assert.assertTrue("factories without a RepNeverEmptyTest case: " + missing, missing.isEmpty());
        Assert.assertTrue("RepNeverEmptyTest cases for no factory: " + stale, stale.isEmpty());
    }

    /** The factories are the only mint paths: every rep constructor is private. */
    @Test
    public void repConstructorsArePrivate() {
        for (Class<?> c : RepPinSupport.repClasses()) {
            for (Constructor<?> k : c.getDeclaredConstructors()) {
                Assert.assertTrue(c.getSimpleName() + ": constructor " + k + " is not private", Modifier.isPrivate(k.getModifiers()));
            }
        }
    }

    /** With assertions on (JUnit, -ea probes) a zero-length rep construction fails fast. */
    @Test
    public void constructorsAssertNonEmpty() throws Exception {
        Object[][] empties = {
                        {StringView.class, new Class<?>[]{byte[].class, byte.class, int.class, int.class}, new Object[]{new byte[4], (byte) 0, 1, 0}},
                        {RopeString.class, new Class<?>[]{String.class, String.class, int.class}, new Object[]{"", "", 0}},
                        {ThreeWayString.class, new Class<?>[]{String.class, String.class, String.class, int.class}, new Object[]{"", "", "", 0}},
                        {FixedConcat4.class, new Class<?>[]{String.class, String.class, String.class, String.class, int.class}, new Object[]{"", "", "", "", 0}},
                        {ArrayLazyString.class, new Class<?>[]{String[].class, byte.class, int.class}, new Object[]{new String[0], (byte) 0, 0}},
                        {InterleavedStringArray.class, new Class<?>[]{String[].class, int.class, Object.class, byte.class, int.class}, new Object[]{new String[0], 0, "", (byte) 0, 0}},
        };
        for (Object[] e : empties) {
            Class<?> c = (Class<?>) e[0];
            if (!c.desiredAssertionStatus()) {
                continue; // assertions off for the rep package: nothing to check (production)
            }
            Constructor<?> k = c.getDeclaredConstructor((Class<?>[]) e[1]);
            k.setAccessible(true);
            try {
                k.newInstance((Object[]) e[2]);
                Assert.fail(c.getSimpleName() + ": an empty rep was constructed");
            } catch (InvocationTargetException ite) {
                Assert.assertTrue(c.getSimpleName() + ": " + ite.getCause(), ite.getCause() instanceof AssertionError);
            }
        }
    }
}
