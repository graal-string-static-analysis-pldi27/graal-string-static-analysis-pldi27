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
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.regex.Pattern;

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
 * The runtime premise: every rep's equals path is
 * content-correct for an argument of any kind: a plain {@code String}, a flat rep ({@code SingleByteString},
 * {@code TrivialString}), a {@code value == null} rep of the same or another class, the same content split
 * differently, and a {@code StringView} whose coder is not its content's compact coder (a UTF-16 view of a
 * Latin-1-only range). The expected result is the JVM definition: the same sequence of chars.
 *
 * <p>Covered per receiver: the Java {@code equals} body, {@code maybeCustomStringEquals}, the plain-String receiver's
 * deflection ({@code plain.equals(rep)}), and the static {@code equals*} helpers the parent's equals intrinsics invoke
 * (their inline fast paths cover only same-coder exact-String arguments).
 *
 * <p>A new rep fails {@link #everyRegisteredRepHasAMaker} until {@link #MAKERS} has a maker for it, and every static
 * {@code equals*(Rep, …)} helper of a rep class is called by {@link #theIntrinsicHelpersAreTotal}.
 */
public class RepEqualsMatrixTest {

    /** Contents: empty, Latin-1, UTF-16, mixed; pairs that differ in one char, in length, and in coder. */
    static final String[] CONTENTS = {"", "a", "b", "é", "€", "ab", "ba", "abc", "abd", "a€c", "a,b", "a,b,c", "éèê", "ab€"};

    /** Per registered rep class, every instance this test builds for a content (empty if the rep cannot hold it). */
    static final Map<Class<?>, Function<String, List<String>>> MAKERS = new LinkedHashMap<>();

    static {
        MAKERS.put(SingleByteString.class, c -> c.length() == 1 && c.charAt(0) <= 0xFF ? List.of(SingleByteString.create(c.charAt(0))) : List.of());
        // a TrivialString holds one byte, its content (char) payload: 0..0x7F or (negative) 0xFF80..0xFFFF
        MAKERS.put(TrivialString.class, c -> c.length() == 1 && (c.charAt(0) < 0x80 || c.charAt(0) >= 0xFF80) ? List.of(TrivialString.create((byte) c.charAt(0))) : List.of());
        MAKERS.put(StringView.class, RepEqualsMatrixTest::views);
        MAKERS.put(RopeString.class, c -> {
            List<String> out = new ArrayList<>();
            for (int i = 0; i <= c.length(); i++) {
                out.add(RopeString.create(c.substring(0, i), c.substring(i)));
            }
            return out;
        });
        MAKERS.put(ThreeWayString.class, c -> {
            List<String> out = new ArrayList<>();
            for (int i = 0; i <= c.length(); i++) {
                for (int j = i; j <= c.length(); j++) {
                    out.add(ThreeWayString.create(c.substring(0, i), c.substring(i, j), c.substring(j)));
                }
            }
            return out;
        });
        MAKERS.put(FixedConcat4.class, c -> {
            List<String> out = new ArrayList<>();
            for (int i = 0; i <= c.length(); i++) {
                for (int j = i; j <= c.length(); j++) {
                    for (int k = j; k <= c.length(); k++) {
                        out.add(FixedConcat4.create(c.substring(0, i), c.substring(i, j), c.substring(j, k), c.substring(k)));
                    }
                }
            }
            return out;
        });
        MAKERS.put(ArrayLazyString.class, c -> {
            List<String> out = new ArrayList<>();
            for (List<String> parts : splits(c)) {
                out.add(ArrayLazyString.create(parts.toArray(new String[0])));
            }
            return out;
        });
        MAKERS.put(InterleavedStringArray.class, c -> {
            List<String> out = new ArrayList<>();
            for (List<String> parts : splits(c)) {
                out.add(InterleavedStringArray.create(parts.toArray(new String[0]), ""));
            }
            Set<Character> seen = new TreeSet<>();
            for (char d : c.toCharArray()) {
                if (seen.add(d)) {
                    String delim = String.valueOf(d);
                    out.add(InterleavedStringArray.create(c.split(Pattern.quote(delim), -1), delim));
                }
            }
            return out;
        });
    }

    /** Every split of {@code c} into contiguous (possibly single) non-empty pieces, plus one with an empty piece. */
    static List<List<String>> splits(String c) {
        List<List<String>> out = new ArrayList<>();
        int n = c.length();
        if (n == 0) {
            out.add(List.of());
            out.add(List.of(""));
            return out;
        }
        for (int mask = 0; mask < (1 << (n - 1)); mask++) {
            List<String> parts = new ArrayList<>();
            int start = 0;
            for (int i = 1; i < n; i++) {
                if ((mask & (1 << (i - 1))) != 0) {
                    parts.add(c.substring(start, i));
                    start = i;
                }
            }
            parts.add(c.substring(start));
            out.add(parts);
        }
        List<String> withEmpty = new ArrayList<>(List.of("", c));
        out.add(withEmpty);
        return out;
    }

    /**
     * Views of {@code c}: of a Latin-1 or a UTF-16 parent (a Latin-1-only range of a UTF-16 parent is the compact copy,
     * not a view; otherwise the view keeps its parent's coder), nested in a view, and of a StringBuilder.
     */
    static List<String> views(String c) {
        List<String> out = new ArrayList<>();
        String latinParent = "x" + c + "y";
        addView(out, StringView.create(latinParent, 1, 1 + c.length()), c);
        String utf16Parent = "€" + c + "€";
        addView(out, StringView.create(utf16Parent, 1, 1 + c.length()), c);
        StringView outer = (StringView) StringView.create(utf16Parent, 0, utf16Parent.length());
        addView(out, StringView.create(outer, 1, 1 + c.length()), c);
        // a builder under half full is the exact-String copy; sized exactly, the factories share (a view)
        StringBuilder sb = new StringBuilder(c.length());
        sb.append(c);
        addView(out, StringView.create(sb), c);
        StringBuffer sbuf = new StringBuffer(c.length());
        sbuf.append(c);
        addView(out, StringView.create(sbuf), c);
        return out;
    }

    /**
     * A factory returns a view, or (a Latin-1-only range of a UTF-16 backing) the compact
     * plain copy, which is not a StringView instance and is left out here.
     */
    static void addView(List<String> out, String made, String c) {
        if (made instanceof StringView) {
            out.add(made);
        } else {
            Assert.assertSame("a factory's non-view result is a plain String", String.class, made.getClass());
            Assert.assertTrue("the compact copy of a Latin-1-only range [" + c + "]", made.isLatin1() && c.chars().allMatch(ch -> ch <= 0xFF));
        }
    }

    record Inst(String label, String s, String content) {
    }

    static String contentOf(String s) {
        char[] a = new char[s.length()];
        for (int i = 0; i < a.length; i++) {
            a[i] = s.charAt(i);
        }
        return new String(a);
    }

    /**
     * Every instance of every kind: plain Strings and every rep instance of every content, built twice (copies "/0" and
     * "/1"), so the same-class same-split pairs compare two distinct objects with distinct children (the identity
     * short-cuts do not hide the piecewise paths).
     */
    static List<Inst> instances() {
        List<Inst> out = new ArrayList<>();
        for (int copy = 0; copy < 2; copy++) {
            for (String c : CONTENTS) {
                out.add(new Inst("String/" + copy + "[" + c + "]", new String(c.toCharArray()), c));
                for (Map.Entry<Class<?>, Function<String, List<String>>> e : MAKERS.entrySet()) {
                    int i = 0;
                    for (String s : e.getValue().apply(new String(c.toCharArray()))) {
                        Assert.assertSame("maker class", c.isEmpty() ? String.class : e.getKey(), s.getClass()); // a rep is never empty
                        Assert.assertEquals("maker content of " + e.getKey().getSimpleName(), c, contentOf(s));
                        out.add(new Inst(e.getKey().getSimpleName() + "/" + copy + "#" + (i++) + "[" + c + "]", s, c));
                    }
                }
            }
        }
        return out;
    }

    @Test
    public void everyRegisteredRepHasAMaker() {
        Set<String> registered = new TreeSet<>();
        for (Class<?> c : RepPinSupport.repClasses()) {
            registered.add(c.getName());
        }
        Set<String> made = new TreeSet<>();
        for (Class<?> c : MAKERS.keySet()) {
            made.add(c.getName());
        }
        Assert.assertEquals("a maker per registered rep class", registered, made);
        // positive control: every maker produces some instance (the matrix is not vacuous for any rep)
        for (Map.Entry<Class<?>, Function<String, List<String>>> e : MAKERS.entrySet()) {
            int n = 0;
            for (String c : CONTENTS) {
                n += e.getValue().apply(c).size();
            }
            Assert.assertTrue(e.getKey() + " has instances", n > 0);
        }
    }

    /**
     * The factories are coder-exact. A Latin-1-only range of a UTF-16 parent is the compact
     * plain copy (as the JVM's substring), a range holding a char above 0xFF stays a UTF-16 view, so no view has a
     * UTF-16 coder over Latin-1 content (such a view would inflate an appending builder).
     */
    @Test
    public void aUtf16ParentsLatin1RangeIsTheCompactCopy() {
        String copy = StringView.create("€ab€", 1, 3);
        Assert.assertSame(String.class, copy.getClass());
        Assert.assertTrue("compact Latin-1", copy.isLatin1());
        Assert.assertTrue(copy.equals("ab") && "ab".equals(copy));
        String view = StringView.create("€a€b€", 1, 4);
        Assert.assertTrue("still a view", view instanceof StringView);
        Assert.assertFalse("UTF-16 view of UTF-16 content", view.isLatin1());
        for (String c : CONTENTS) {
            for (String v : views(c)) {
                Assert.assertEquals("view coder of [" + c + "]", c.chars().anyMatch(ch -> ch > 0xFF), !v.isLatin1());
            }
        }
    }

    /**
     * {@code StringView.create(StringBuilder|StringBuffer)} trims a mostly-empty builder with
     * {@code Arrays.copyOf(backing, length << coder)} (a byte count; {@code length} alone would truncate a UTF-16
     * builder: charAt/equals would throw AIOOBE). Every content, Latin-1 and UTF-16, through both builder kinds.
     */
    @Test
    public void builderViewsKeepTheirContent() {
        for (String c : CONTENTS) {
            StringBuilder sb = new StringBuilder(64);
            sb.append(c);
            Assert.assertEquals("StringBuilder view of [" + c + "]", c, contentOf(StringView.create(sb)));
            StringBuffer sbuf = new StringBuffer(64);
            sbuf.append(c);
            Assert.assertEquals("StringBuffer view of [" + c + "]", c, contentOf(StringView.create(sbuf)));
        }
    }

    @Test
    public void equalsIsContentEqualityForEveryReceiverAndArgument() {
        List<Inst> all = instances();
        List<String> wrong = new ArrayList<>();
        int cells = 0;
        for (Inst r : all) {
            for (Inst a : all) {
                boolean expected = r.content().equals(a.content());
                cells++;
                // String.equals is the stock body; an exact-String receiver with a non-String
                // argument is answered by the redirect mirror (the static Object-declared twin below), not by equals
                boolean stockEqualsCell = r.s().getClass() == String.class && a.s().getClass() != String.class;
                if (!stockEqualsCell && r.s().equals(a.s()) != expected) {
                    wrong.add(r.label() + ".equals(" + a.label() + ")");
                }
                if (String.objectMaybeCustomStringEquals(r.s(), a.s()) != expected) {
                    wrong.add("String.objectMaybeCustomStringEquals(" + r.label() + ", " + a.label() + ")");
                }
                if (r.s().maybeCustomStringEquals(a.s()) != expected) {
                    wrong.add(r.label() + ".maybeCustomStringEquals(" + a.label() + ")");
                }
                // the Object-declared redirect form (EqualsMatrixNodePlugin.emitObjectRedirectSwap): an exact
                // String receiver with a String argument is asked a.equals(r), every other pair r.equals(a)
                boolean swap = r.s().getClass() == String.class;
                boolean split = swap ? a.s().equals(r.s()) : r.s().equals(a.s());
                if (split != expected) {
                    wrong.add("split(" + r.label() + ", " + a.label() + ")");
                }
            }
            Assert.assertFalse(r.label() + ".equals(null)", r.s().equals(null));
            Assert.assertFalse(r.label() + ".equals(Object)", r.s().equals(new Object()));
            Assert.assertTrue(r.label() + ".equals(itself)", r.s().equals(r.s()));
        }
        Assert.assertTrue("cells " + cells, cells > 10000);
        Assert.assertEquals("wrong cells (first 20 of " + wrong.size() + "): " + wrong.subList(0, Math.min(20, wrong.size())), 0, wrong.size());
    }

    /**
     * The static helpers the parent's equals intrinsics invoke: every static boolean {@code equals*} method of a rep
     * class whose first parameter is the rep and whose second is a reference ({@code equalsStringView},
     * {@code equalsSameType}, {@code equalsFallback}), over every argument it accepts.
     */
    @Test
    public void theIntrinsicHelpersAreTotal() throws ReflectiveOperationException {
        List<Inst> all = instances();
        List<String> wrong = new ArrayList<>();
        int helpers = 0;
        for (Class<?> rep : MAKERS.keySet()) {
            for (Method m : rep.getDeclaredMethods()) {
                if (!Modifier.isStatic(m.getModifiers()) || m.getReturnType() != boolean.class || !m.getName().startsWith("equals") || m.getParameterCount() != 2 ||
                                m.getParameterTypes()[0] != rep || m.getParameterTypes()[1].isPrimitive()) {
                    continue;
                }
                m.setAccessible(true);
                helpers++;
                for (Inst r : all) {
                    if (r.s().getClass() != rep) {
                        continue;
                    }
                    for (Inst a : all) {
                        if (!m.getParameterTypes()[1].isInstance(a.s())) {
                            continue;
                        }
                        boolean expected = r.content().equals(a.content());
                        if ((boolean) m.invoke(null, r.s(), a.s()) != expected) {
                            wrong.add(rep.getSimpleName() + "." + m.getName() + "(" + r.label() + ", " + a.label() + ")");
                        }
                    }
                }
            }
        }
        Assert.assertTrue("helpers found: " + helpers, helpers >= 11);
        Assert.assertEquals("wrong cells (first 20 of " + wrong.size() + "): " + wrong.subList(0, Math.min(20, wrong.size())), 0, wrong.size());
    }

    /**
     * The lazy reps' same-type helper ({@code equalsSameType}, the piecewise compare the intrinsics
     * call for a same-class argument) is total for any child, not only flat compact ones: a value-null child (a view, a
     * lazy rep) and a UTF-16 view of a Latin-1-only range compare by content. Same split on both sides, every pair of
     * child kinds, equal and unequal content.
     */
    @Test
    public void lazySameTypeIsTotalForViewLazyAndNonCompactChildren() throws ReflectiveOperationException {
        List<Function<String, String>> kinds = List.of(
                        p -> new String(p.toCharArray()),
                        p -> StringView.create("x" + p + "y", 1, 1 + p.length()),
                        p -> StringView.create("\u20ac" + p + "\u20ac", 1, 1 + p.length()),
                        p -> p.isEmpty() ? p : RopeString.create(p.substring(0, 1), p.substring(1)));
        Map<Class<?>, Function<String[], String>> lazy = new LinkedHashMap<>();
        lazy.put(RopeString.class, ps -> RopeString.create(ps[0], ps[1]));
        lazy.put(ThreeWayString.class, ps -> ThreeWayString.create(ps[0], ps[1], ps[2]));
        lazy.put(FixedConcat4.class, ps -> FixedConcat4.create(ps[0], ps[1], ps[2], ps[3]));
        lazy.put(ArrayLazyString.class, ArrayLazyString::create);
        lazy.put(InterleavedStringArray.class, ps -> InterleavedStringArray.create(ps, ""));
        int[] arity = {2, 3, 4, 5, 5};
        String[][] contents = {{"abcdefghij", "abcdefghij"}, {"abcdefghij", "abcdefghiX"}, {"ab\u20acdefghij", "ab\u20acdefghij"}, {"ab\u20acdefghij", "ab\u20acdefghiX"}};
        List<String> wrong = new ArrayList<>();
        int cells = 0;
        int ci = 0;
        for (Map.Entry<Class<?>, Function<String[], String>> e : lazy.entrySet()) {
            int n = arity[ci++];
            Method sameType = e.getKey().getDeclaredMethod("equalsSameType", e.getKey(), e.getKey());
            sameType.setAccessible(true);
            for (String[] pair : contents) {
                for (Function<String, String> ka : kinds) {
                    for (Function<String, String> kb : kinds) {
                        String a = e.getValue().apply(split(pair[0], n, ka));
                        String b = e.getValue().apply(split(pair[1], n, kb));
                        boolean expected = pair[0].equals(pair[1]);
                        cells++;
                        if ((boolean) sameType.invoke(null, a, b) != expected || a.equals(b) != expected) {
                            wrong.add(e.getKey().getSimpleName() + "[" + pair[0] + " vs " + pair[1] + "] kinds " + kinds.indexOf(ka) + "/" + kinds.indexOf(kb));
                        }
                    }
                }
            }
        }
        Assert.assertEquals("wrong cells of " + cells + ": " + wrong, 0, wrong.size());
    }

    /** {@code c} cut into {@code n} non-empty pieces of near-equal length, each built by {@code kind}. */
    private static String[] split(String c, int n, Function<String, String> kind) {
        String[] out = new String[n];
        int step = c.length() / n;
        for (int i = 0; i < n; i++) {
            out[i] = kind.apply(c.substring(i * step, i == n - 1 ? c.length() : (i + 1) * step));
        }
        return out;
    }
}
