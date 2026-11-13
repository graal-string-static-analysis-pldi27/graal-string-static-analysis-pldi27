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

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.StringView;

/**
 * The {@code String.join} lazy source.
 * <ul>
 * <li>the source table is exactly the JDK's two public {@code String.join} overloads, and the child's mint function and
 * the parent's factory agree on {@code INTERLEAVED};</li>
 * <li>the replacement ({@link LazyConcatFactory#join}) equals the JDK result on every observable: content, length,
 * hashCode, coder, bytes, equals both ways, compareTo, the exceptions; and is a fresh object (identity);</li>
 * <li>the snapshot: CharSequence arguments mutated after the call are not seen;</li>
 * <li>{@link InterleavedStringArray#createOwned} takes the array over without a copy;</li>
 * <li>the interleaved rep is total over rep children (a view, a rope): its accessors read children only through the
 * String API (a value-null child is fine).</li>
 * </ul>
 */
public class StringJoinSourceTest {

    private static final String UTF = "中";

    @Test
    public void sourceTableIsExactlyTheJdkJoinOverloads() {
        Set<String> jdk = new TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            if (m.getName().equals("join") && Modifier.isPublic(m.getModifiers()) && Modifier.isStatic(m.getModifiers())) {
                StringBuilder sb = new StringBuilder();
                for (Class<?> p : m.getParameterTypes()) {
                    sb.append(sb.length() > 0 ? "," : "").append(p.isArray() ? "[L" + p.getComponentType().getName().replace('.', '/') + ";" : "L" + p.getName().replace('.', '/') + ";");
                }
                jdk.add(sb.toString());
            }
        }
        Assert.assertEquals(new TreeSet<>(LazyConcatMint.JOIN_SIGNATURES), jdk);
        for (String sig : jdk) {
            Assert.assertTrue(LazyConcatMint.isJoinSource("java.lang.String", "join", sig));
            Assert.assertFalse(LazyConcatMint.isJoinSource("java.lang.StringBuilder", "join", sig));
            Assert.assertFalse(LazyConcatMint.isJoinSource("java.lang.String", "concat", sig));
        }
        Assert.assertFalse(LazyConcatMint.isJoinSource("java.lang.String", "join", "Ljava/lang/String;,Ljava/lang/String;,Ljava/lang/String;,[Ljava/lang/String;,I"));
    }

    @Test
    public void childAndParentAgreeOnTheMintedRep() throws Exception {
        SugVertex v = new SugVertex(1);
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setDeclaringClass("java.lang.String");
        v.setMethodName("join");
        v.setMethodSignature(LazyConcatMint.JOIN_ITERABLE_SIG);
        Assert.assertTrue(LazyConcatMint.isJoinSource(v));
        Assert.assertEquals(LazyConcatMint.INTERLEAVED, LazyConcatMint.mintedRep(v, LazyConcatMint.INTERLEAVED));
        Assert.assertNull("a non-INTERLEAVED variant mints nothing at a join site", LazyConcatMint.mintedRep(v, LazyConcatMint.ROPE));
        v.setNodeType(SugNodeType.JDK_LIBRARY_CALL);
        Assert.assertFalse("only the STRING_METHOD_CALL vertex is a source", LazyConcatMint.isJoinSource(v));
        for (String sig : LazyConcatMint.JOIN_SIGNATURES) {
            Method f = LazyConcatMint.joinFactoryMethod(sig);
            Assert.assertNotNull(sig, f);
            Assert.assertTrue(Modifier.isStatic(f.getModifiers()) && Modifier.isPublic(f.getModifiers()));
            Method jdk = String.class.getMethod("join", f.getParameterTypes());
            Assert.assertEquals("the factory has the JDK overload's parameters", Arrays.asList(jdk.getParameterTypes()), Arrays.asList(f.getParameterTypes()));
            Object r = f.getParameterTypes()[1].isArray() ? f.invoke(null, ",", new CharSequence[]{"a", "b"}) : f.invoke(null, ",", List.of("a", "b"));
            Assert.assertSame("the registry class of INTERLEAVED", InlineCacheRegistry.getRepClass(LazyConcatMint.INTERLEAVED), r.getClass());
        }
    }

    static void same(String jdk, String rep, String what) {
        if (jdk.isEmpty()) { // a rep is never empty; an empty join is a fresh plain String, as the JDK's
            Assert.assertSame(what + ": an empty join is a plain String", String.class, rep.getClass());
            Assert.assertTrue(what + ": empty", rep.isEmpty());
            return;
        }
        Assert.assertTrue(what + ": a rep", rep instanceof InterleavedStringArray);
        Assert.assertEquals(what + ": length", jdk.length(), rep.length());
        Assert.assertEquals(what + ": isEmpty", jdk.isEmpty(), rep.isEmpty());
        Assert.assertEquals(what + ": coder", jdk.coder(), rep.coder());
        Assert.assertEquals(what + ": hashCode", jdk.hashCode(), rep.hashCode());
        Assert.assertTrue(what + ": rep.equals(jdk)", rep.equals(jdk));
        Assert.assertTrue(what + ": jdk.equals(rep) (the REDIRECT mirror)", RepEq.eq(jdk, rep));
        Assert.assertEquals(what + ": compareTo", 0, rep.compareTo(jdk));
        // compareTo mirror: a plain receiver's stock compareTo reads the argument's value(); a rep argument reaches
        // String's comparison only through the REDIRECT target maybeCustomStringCompareTo
        Assert.assertEquals(what + ": compareTo (argument)", 0, jdk.maybeCustomStringCompareTo(rep));
        Assert.assertArrayEquals(what + ": UTF-8", jdk.getBytes(StandardCharsets.UTF_8), rep.getBytes(StandardCharsets.UTF_8));
        Assert.assertArrayEquals(what + ": UTF-16", jdk.getBytes(StandardCharsets.UTF_16), rep.getBytes(StandardCharsets.UTF_16));
        Assert.assertArrayEquals(what + ": chars", jdk.toCharArray(), rep.toCharArray());
        for (int i = 0; i < jdk.length(); i++) {
            Assert.assertEquals(what + ": charAt " + i, jdk.charAt(i), rep.charAt(i));
        }
        // every sub-range of getChars (a local named like the part-count field once shadowed it: empty parts lost chars)
        for (int b = 0; b <= jdk.length() && jdk.length() <= 64; b++) {
            for (int e = b; e <= jdk.length(); e++) {
                char[] x = new char[e - b + 2];
                char[] y = new char[e - b + 2];
                jdk.getChars(b, e, x, 1);
                rep.getChars(b, e, y, 1);
                Assert.assertArrayEquals(what + ": getChars " + b + ".." + e, x, y);
            }
        }
        Assert.assertEquals(what + ": concat operand (indy)", "[" + jdk + "]", "[" + rep + "]");
    }

    @Test
    public void arrayJoinMatchesTheJdk() {
        CharSequence[][] cases = {{}, {"one"}, {""}, {null}, {null, "x", null}, {"a1", "b22", "c333"}, {"xé", UTF + "y", "z"}, {"", "", ""},
                        {new StringBuilder("sb"), new StringBuffer("sf"), "s"}};
        for (String delim : new String[]{",", "", " | ", UTF}) {
            for (CharSequence[] c : cases) {
                String what = "join(" + delim + ", " + Arrays.toString(c) + ")";
                String jdk = String.join(delim, c);
                String rep = LazyConcatFactory.join(delim, c);
                same(jdk, rep, what);
                if (rep.isEmpty()) {
                    continue; // an empty result is the literal "" (identity of empty results is out of scope)
                }
                Assert.assertNotSame(what + ": a fresh object (as the JDK's)", jdk, rep);
                if (c.length == 1) {
                    Assert.assertNotSame(what + ": never the element itself (the JDK copies)", c[0], rep);
                }
            }
        }
    }

    @Test
    public void iterableJoinMatchesTheJdk() {
        for (int n : new int[]{0, 1, 2, 7, 8, 9, 16, 17, 40}) {
            List<CharSequence> l = new ArrayList<>();
            for (int i = 0; i < n; i++) {
                l.add(i % 5 == 3 ? null : i % 7 == 2 ? new StringBuilder("b" + i) : (i % 4 == 1 ? UTF : "w") + i);
            }
            for (String delim : new String[]{" ", "", UTF + UTF}) {
                same(String.join(delim, l), LazyConcatFactory.join(delim, l), "iterable n=" + n + " delim=" + delim);
            }
        }
    }

    @Test
    public void lessThanTwoElementsDropTheDelimitersCoder() {
        // String.join(String, String, String, String[], int): the delimiter's coder joins only when size > 1
        same(String.join(UTF, "abc"), LazyConcatFactory.join(UTF, new CharSequence[]{"abc"}), "1 element, UTF-16 delimiter");
        Assert.assertEquals(0, LazyConcatFactory.join(UTF, new CharSequence[]{"abc"}).coder());
        Assert.assertEquals(0, LazyConcatFactory.join(UTF, List.of()).coder());
        // two single-element joins with different delimiters are equal (the delimiter is not part of the content)
        String a = LazyConcatFactory.join(",", new CharSequence[]{"x"});
        String b = LazyConcatFactory.join(";", new CharSequence[]{"x"});
        Assert.assertTrue(RepEq.eq(a, b));
        Assert.assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    public void exceptionsMatchTheJdk() {
        assertNpe(() -> String.join(null, "a"), () -> LazyConcatFactory.join(null, new CharSequence[]{"a"}));
        assertNpe(() -> String.join(",", (CharSequence[]) null), () -> LazyConcatFactory.join(",", (CharSequence[]) null));
        assertNpe(() -> String.join(null, List.of("a")), () -> LazyConcatFactory.join(null, List.of("a")));
        assertNpe(() -> String.join(",", (Iterable<CharSequence>) null), () -> LazyConcatFactory.join(",", (Iterable<CharSequence>) null));
    }

    /** A CharSequence whose {@code toString()} is null (the JDK reads the delimiter only for 2+ elements). */
    private static final CharSequence NULL_TO_STRING = new CharSequence() {
        @Override
        public int length() {
            return 0;
        }

        @Override
        public char charAt(int index) {
            throw new IndexOutOfBoundsException();
        }

        @Override
        public CharSequence subSequence(int start, int end) {
            return this;
        }

        @Override
        @SuppressWarnings("all")
        public String toString() {
            return null;
        }
    };

    @Test
    public void aNullToStringDelimiterIsUnreadBelowTwoElements() {
        // 0 and 1 elements: the JDK returns normally (no NPE for the delimiter)
        same(String.join(NULL_TO_STRING), LazyConcatFactory.join(NULL_TO_STRING, new CharSequence[0]), "array, 0 elements");
        same(String.join(NULL_TO_STRING, "a"), LazyConcatFactory.join(NULL_TO_STRING, new CharSequence[]{"a"}), "array, 1 element");
        same(String.join(NULL_TO_STRING, List.of()), LazyConcatFactory.join(NULL_TO_STRING, List.of()), "iterable, 0 elements");
        same(String.join(NULL_TO_STRING, List.of(UTF)), LazyConcatFactory.join(NULL_TO_STRING, List.of(UTF)), "iterable, 1 element");
        assertNpe(() -> String.join(NULL_TO_STRING, "a", "b"), () -> LazyConcatFactory.join(NULL_TO_STRING, new CharSequence[]{"a", "b"}));
        assertNpe(() -> String.join(NULL_TO_STRING, List.of("a", "b")), () -> LazyConcatFactory.join(NULL_TO_STRING, List.of("a", "b")));
        same("x", InterleavedStringArray.createOwned(new String[]{"x"}, 1, null), "createOwned, 1 part, null delimiter");
        same("", InterleavedStringArray.createOwned(new String[0], 0, null), "createOwned, 0 parts, null delimiter");
        assertNpe(() -> {
            throw new NullPointerException();
        }, () -> InterleavedStringArray.createOwned(new String[]{"x", "y"}, 2, null));
    }

    @Test
    public void theIterableIsIteratedExactlyOnceAsByTheJdk() {
        // exactly one iterator() and n next() calls, the same counts as the JDK body
        for (int n : new int[]{0, 1, 2, 9, 17}) {
            List<String> parts = new ArrayList<>();
            for (int i = 0; i < n; i++) {
                parts.add("p" + i);
            }
            int[] jdkCounts = new int[2];
            int[] repCounts = new int[2];
            String jdk = String.join(",", counting(parts, jdkCounts));
            String rep = LazyConcatFactory.join(",", counting(parts, repCounts));
            same(jdk, rep, "counted iterable n=" + n);
            Assert.assertEquals("iterator() calls", 1, repCounts[0]);
            Assert.assertEquals("next() calls", n, repCounts[1]);
            Assert.assertArrayEquals("the JDK's counts", jdkCounts, repCounts);
        }
    }

    private static Iterable<CharSequence> counting(List<String> parts, int[] counts) {
        return () -> {
            counts[0]++;
            java.util.Iterator<String> it = parts.iterator();
            return new java.util.Iterator<>() {
                @Override
                public boolean hasNext() {
                    return it.hasNext();
                }

                @Override
                public CharSequence next() {
                    counts[1]++;
                    return it.next();
                }
            };
        };
    }

    @Test
    public void aNestedJoinIsTotal() {
        // an interleaved child inside an interleaved string, both directions of equals/compareTo
        String inner = LazyConcatFactory.join("-", new CharSequence[]{"a", UTF, "b"});
        String flatInner = String.join("-", "a", UTF, "b");
        same(String.join(",", flatInner, "c", flatInner), LazyConcatFactory.join(",", new CharSequence[]{inner, "c", inner}), "nested");
        List<CharSequence> many = new ArrayList<>();
        List<CharSequence> manyFlat = new ArrayList<>();
        for (int i = 0; i < 12; i++) {
            many.add(i % 3 == 0 ? inner : "e" + i);
            manyFlat.add(i % 3 == 0 ? flatInner : "e" + i);
        }
        same(String.join("", manyFlat), LazyConcatFactory.join("", many), "nested, many parts");
    }

    @Test
    public void manyPartsCharAtEqualsCompareToMatchTheJdk() {
        // the binary-search charAt (> 8 parts), the sequential equals/compareTo; empty parts at the
        // ends and in a row, mixed coders, an empty and a non-empty delimiter, part counts around the threshold
        for (int n : new int[]{0, 1, 2, 8, 9, 10, 33}) {
            for (String delim : new String[]{"", ",", UTF + "|"}) {
                List<String> l = new ArrayList<>();
                for (int i = 0; i < n; i++) {
                    l.add(i == 0 || i == n - 1 || i % 4 == 2 || i % 4 == 3 ? "" : i % 3 == 0 ? UTF + i : "a" + i);
                }
                String jdk = String.join(delim, l);
                String rep = LazyConcatFactory.join(delim, l);
                String what = "n=" + n + " delim=" + delim;
                same(jdk, rep, what);
                // compareTo/equals against every one-char change, every prefix and a longer string: exact JDK values
                for (int k = 0; k < jdk.length(); k++) {
                    for (char c : new char[]{(char) (jdk.charAt(k) - 1), (char) (jdk.charAt(k) + 1), '\u4e2d', 'a'}) {
                        String other = jdk.substring(0, k) + c + jdk.substring(k + 1);
                        assertCompare(jdk, rep, other, what + " k=" + k + " c=" + (int) c);
                    }
                    assertCompare(jdk, rep, jdk.substring(0, k), what + " prefix " + k);
                }
                assertCompare(jdk, rep, jdk + "z", what + " longer");
                String rep2 = LazyConcatFactory.join(delim, l);
                Assert.assertTrue(what + ": two equal interleaved strings", rep.equals(rep2) && rep.compareTo(rep2) == 0);
            }
        }
    }

    private static void assertCompare(String jdk, String rep, String other, String what) {
        Assert.assertEquals(what + ": equals", jdk.equals(other), rep.equals(other));
        Assert.assertEquals(what + ": equals (argument)", other.equals(jdk), RepEq.eq(other, rep));
        Assert.assertEquals(what + ": compareTo", jdk.compareTo(other), rep.compareTo(other));
        // compareTo mirror: a plain receiver with a rep argument runs through the REDIRECT target (stock compareTo reads value())
        Assert.assertEquals(what + ": compareTo (argument)", other.compareTo(jdk), other.maybeCustomStringCompareTo(rep));
    }

    @Test
    public void manyPartsAreLinearNotQuadratic() throws Exception {
        // a 20,000-part join (~120k chars): equals/compareTo must be O(length), not O(length x parts). 10 rounds must
        // stay far below the quadratic cost; the bound is generous. charAt is the plain linear part walk (no cached part
        // offsets, so the rep has no extra fields), so a charAt loop is not timed here; charAt is spot-checked for
        // content.
        int n = 20_000;
        List<String> l = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            l.add((i % 97 == 0 ? UTF : "w") + i);
        }
        String jdk = String.join(",", l);
        String rep = LazyConcatFactory.join(",", l);
        String last = jdk.substring(0, jdk.length() - 1) + "#";
        long t0 = System.nanoTime();
        for (int round = 0; round < 10; round++) {
            Assert.assertTrue(rep.equals(jdk));
            Assert.assertTrue(RepEq.eq(jdk, rep));
            Assert.assertEquals(0, rep.compareTo(jdk));
            Assert.assertEquals(jdk.compareTo(last), rep.compareTo(last));
            Assert.assertEquals(last.compareTo(jdk), last.maybeCustomStringCompareTo(rep)); // the REDIRECT target
        }
        long ms = (System.nanoTime() - t0) / 1_000_000;
        Assert.assertTrue("10 rounds took " + ms + " ms (quadratic: ~10 s)", ms < 2_500);
        for (int i = 0; i < rep.length(); i += 997) {
            Assert.assertEquals("charAt(" + i + ")", jdk.charAt(i), rep.charAt(i));
        }
        Assert.assertEquals(jdk.charAt(jdk.length() - 1), rep.charAt(rep.length() - 1));
        for (Field f : InterleavedStringArray.class.getDeclaredFields()) {
            Assert.assertFalse("no part-offset cache field (" + f + ")", f.getName().equals("partStarts"));
        }
    }

    private static void assertNpe(Runnable jdk, Runnable rep) {
        for (Runnable r : new Runnable[]{jdk, rep}) {
            try {
                r.run();
                Assert.fail("NPE expected");
            } catch (NullPointerException expected) {
                // as the JDK
            }
        }
    }

    @Test
    public void theResultIsASnapshot() {
        StringBuilder a = new StringBuilder("abc");
        StringBuilder sep = new StringBuilder("--");
        String jdk = String.join(sep, a, "x");
        String rep = LazyConcatFactory.join(sep, new CharSequence[]{a, "x"});
        a.setLength(0);
        a.append("ZZZZZZ");
        sep.setCharAt(0, '#');
        same(jdk, rep, "array, mutated after");
        RepEq.assertRepEquals("abc--x", rep);
        List<StringBuilder> l = new ArrayList<>(List.of(new StringBuilder("p"), new StringBuilder("q")));
        String jdk2 = String.join("+", l);
        String rep2 = LazyConcatFactory.join("+", l);
        l.get(0).insert(0, "pre");
        l.add(new StringBuilder("late"));
        same(jdk2, rep2, "iterable, mutated after");
        RepEq.assertRepEquals("p+q", rep2);
    }

    @Test
    public void createOwnedTakesTheArrayOver() throws Exception {
        String[] parts = {"a", "b", "c", null, null};
        String r = InterleavedStringArray.createOwned(parts, 3, "-");
        Field f = InterleavedStringArray.class.getDeclaredField("elements");
        f.setAccessible(true);
        Assert.assertSame("no copy", parts, f.get(r));
        same("a-b-c", r, "owned prefix of a growth array");
        String[] mine = {"x", "y"};
        Assert.assertNotSame("create copies", mine, f.get(InterleavedStringArray.create(mine, ",")));
        try {
            InterleavedStringArray.createOwned(new String[]{"a", null}, 2, ",");
            Assert.fail("a null part inside the count");
        } catch (NullPointerException expected) {
            // as before
        }
    }

    @Test
    public void totalOverRepChildren() {
        String view = StringView.create("hello world", 2, 7);
        String rope = RopeString.create("ab", UTF + "c");
        String rep = LazyConcatFactory.join(view, new CharSequence[]{rope, view, "z"});
        String flat = String.join(new String(view.toCharArray()), new String(rope.toCharArray()), new String(view.toCharArray()), "z");
        same(flat, rep, "rep children");
        String rep2 = LazyConcatFactory.join(new String(view.toCharArray()), List.of(new String(rope.toCharArray()), new String(view.toCharArray()), "z"));
        Assert.assertTrue("two interleaved strings, rep vs flat children", rep.equals(rep2) && RepEq.eq(rep2, rep));
    }
}
