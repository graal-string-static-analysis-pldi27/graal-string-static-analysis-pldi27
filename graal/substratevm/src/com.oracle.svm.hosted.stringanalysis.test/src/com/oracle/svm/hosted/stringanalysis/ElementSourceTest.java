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
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Spliterator;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ElementSourceFactory;
import com.oracle.svm.core.stringrep.StringView;

/**
 * Element sources: the element-source table is exact, every row has its factory, and
 * every factory is equivalent to the JDK 25 method it replaces (contents, lengths, identities, coders, the empty-input,
 * leading/trailing-empty and limit rules, stream characteristics, laziness, exceptions), for both view variants.
 */
public class ElementSourceTest {

    private static final String UTF = "中";

    private static final String[] INPUTS = {"", "a", ",", ",,", "a,b", "a,b,,", ",a,b", "a,,b,,", ",,a,,", "abc", "a.b.c", "a|b||c|",
                    "  a  b ", "xaxbx", "aaa", UTF + "," + UTF + ",x", "x,y" + UTF, "\u00e9,\u00e8,", "line1\nline2\r\nline3\rline4", "\n", "\r\n\r\n", "a\n\nb\n",
                    "\n\na", "trailing\n", UTF + "\n" + UTF + "x\r\n", UTF + "\ra\r\r\n", "ab12cd345ef", "a\\b\\c"};
    private static final String[] REGEXES = {",", "\\|", ".", "", "\\s*", "\\s+", "(?=a)", "a*", "a", "x", "\\d", "\\d+", UTF, "\\.", "ab", "\\\\", "b", ",,", "\n", "[,|]"};
    private static final int[] LIMITS = {-1, 0, 1, 2, 3, 10};

    @Test
    public void tableIsExactAndEveryRowHasItsFactory() throws Exception {
        Assert.assertEquals(8, ElementSources.ROWS.size());
        Assert.assertEquals(java.util.Set.of("splitAsStream", "lines", "split", "splitWithDelimiters"), ElementSources.ROW_NAMES);
        for (Map.Entry<String, ElementSources.Kind> e : ElementSources.ROWS.entrySet()) {
            String row = e.getKey();
            String decl = row.substring(0, row.indexOf('#'));
            String name = row.substring(row.indexOf('#') + 1, row.indexOf('('));
            String sig = row.substring(row.indexOf('(') + 1, row.length() - 1);
            Class<?> owner = Class.forName(decl);
            // Pattern is final; String is de-finalized in the builder JDK (the reps): the factory takes the virtual stock
            // call for every receiver that is not an exact String, so a rep's own method is still the one that runs
            Assert.assertTrue(row + ": the receiver class is final, or String (non-exact receivers take the stock call)", Modifier.isFinal(owner.getModifiers()) || owner == String.class);
            Method jdk = null;
            for (Method m : owner.getDeclaredMethods()) {
                if (m.getName().equals(name) && Modifier.isPublic(m.getModifiers()) && !Modifier.isStatic(m.getModifiers()) && sigOf(m.getParameterTypes()).equals(sig)) {
                    jdk = m;
                }
            }
            Assert.assertNotNull(row + ": a public JDK method", jdk);
            Assert.assertEquals(row, e.getValue() == ElementSources.Kind.STREAM ? Stream.class : String[].class, jdk.getReturnType());
            Assert.assertTrue(ElementSources.isSource(decl, name, sig));
            Method f = ElementSources.factoryMethod(decl, name, sig);
            Assert.assertNotNull(row + ": a factory", f);
            Assert.assertTrue(Modifier.isStatic(f.getModifiers()) && Modifier.isPublic(f.getModifiers()));
            Class<?>[] want = new Class<?>[jdk.getParameterCount() + 2];
            want[0] = owner;
            System.arraycopy(jdk.getParameterTypes(), 0, want, 1, jdk.getParameterCount());
            want[want.length - 1] = boolean.class;
            Assert.assertArrayEquals(row + ": receiver, the arguments, stored", want, f.getParameterTypes());
            Assert.assertEquals(row, ElementSources.containerClass(e.getValue()), f.getReturnType());
        }
        Assert.assertFalse(ElementSources.isSource("java.lang.String", "split", "Ljava/lang/CharSequence;"));
        Assert.assertFalse(ElementSources.isSource("java.util.regex.Matcher", "splitAsStream", "Ljava/lang/CharSequence;"));
        Assert.assertNull(ElementSources.factoryMethod("java.lang.String", "substring", "I"));
        Assert.assertEquals(ElementSources.ELEMENT_VIEW, ElementSources.variant(false));
        Assert.assertEquals(ElementSources.ELEMENT_VIEW_STORED, ElementSources.variant(true));
        Assert.assertTrue(ElementSources.isElementVariant(ElementSources.ELEMENT_VIEW) && ElementSources.isElementVariant(ElementSources.ELEMENT_VIEW_STORED));
        Assert.assertFalse(ElementSources.isElementVariant(StringViewHeuristic.STORED) || ElementSources.isElementVariant(null));
    }

    private static String sigOf(Class<?>[] ps) {
        StringBuilder sb = new StringBuilder();
        for (Class<?> p : ps) {
            sb.append(sb.length() > 0 ? "," : "").append(p.isPrimitive() ? (p == int.class ? "I" : "?") : "L" + p.getName().replace('.', '/') + ";");
        }
        return sb.toString();
    }

    /** One piece: equal content and coder; the JDK's identity with the input is kept; a non-identical non-empty piece is a view. */
    private static void samePiece(String input, String jdk, String rep, String what) {
        RepEq.assertRepEquals(what + ": content", jdk, rep);
        Assert.assertTrue(what + ": rep.equals(jdk)", rep.equals(jdk));
        Assert.assertEquals(what + ": hashCode", jdk.hashCode(), rep.hashCode());
        Assert.assertEquals(what + ": coder", jdk.coder(), rep.coder());
        Assert.assertEquals(what + ": identity with the input", jdk == input, rep == input);
        if (jdk.isEmpty()) {
            Assert.assertSame(what + ": an empty piece is the JDK's \"\"", jdk, rep);
        }
    }

    private static void sameArray(String input, String[] jdk, String[] rep, String what) {
        Assert.assertSame(what + ": array class", String[].class, rep.getClass());
        Assert.assertEquals(what + ": length " + List.of(jdk) + " vs " + List.of(rep), jdk.length, rep.length);
        for (int i = 0; i < jdk.length; i++) {
            samePiece(input, jdk[i], rep[i], what + " [" + i + "]");
        }
    }

    @Test
    public void stringSplitMatrix() {
        int views = 0;
        for (String in : INPUTS) {
            for (String re : REGEXES) {
                for (boolean stored : new boolean[]{false, true}) {
                    String w = "'" + in + "'.split('" + re + "') stored=" + stored;
                    sameArray(in, in.split(re), ElementSourceFactory.stringSplit(in, re, stored), w);
                    for (int lim : LIMITS) {
                        String[] r = ElementSourceFactory.stringSplit(in, re, lim, stored);
                        sameArray(in, in.split(re, lim), r, w + " limit=" + lim);
                        sameArray(in, in.splitWithDelimiters(re, lim), ElementSourceFactory.stringSplitWithDelimiters(in, re, lim, stored), w + " withDelimiters limit=" + lim);
                        for (String p : r) {
                            views += p instanceof StringView ? 1 : 0;
                        }
                    }
                }
            }
        }
        Assert.assertTrue("the matrix produces views", views > 100);
    }

    @Test
    public void patternSplitMatrix() {
        for (String in : INPUTS) {
            for (String re : REGEXES) {
                Pattern p = Pattern.compile(re);
                for (boolean stored : new boolean[]{false, true}) {
                    String w = "Pattern('" + re + "').split('" + in + "') stored=" + stored;
                    sameArray(in, p.split(in), ElementSourceFactory.patternSplit(p, in, stored), w);
                    for (int lim : LIMITS) {
                        sameArray(in, p.split(in, lim), ElementSourceFactory.patternSplit(p, in, lim, stored), w + " limit=" + lim);
                        sameArray(in, p.splitWithDelimiters(in, lim), ElementSourceFactory.patternSplitWithDelimiters(p, in, lim, stored), w + " withDelimiters limit=" + lim);
                    }
                }
            }
        }
    }

    @Test
    public void splitAsStreamMatrix() {
        for (String in : INPUTS) {
            for (String re : REGEXES) {
                Pattern p = Pattern.compile(re);
                for (boolean stored : new boolean[]{false, true}) {
                    String w = "Pattern('" + re + "').splitAsStream('" + in + "') stored=" + stored;
                    List<String> jdk = p.splitAsStream(in).collect(Collectors.toList());
                    List<String> rep = ElementSourceFactory.splitAsStream(p, in, stored).collect(Collectors.toList());
                    Assert.assertEquals(w + ": count", p.splitAsStream(in).count(), ElementSourceFactory.splitAsStream(p, in, stored).count());
                    sameArray(in, jdk.toArray(new String[0]), rep.toArray(new String[0]), w);
                    Spliterator<String> js = p.splitAsStream(in).spliterator();
                    Spliterator<String> rs = ElementSourceFactory.splitAsStream(p, in, stored).spliterator();
                    Assert.assertEquals(w + ": characteristics", js.characteristics(), rs.characteristics());
                    Assert.assertEquals(w + ": estimateSize", js.estimateSize(), rs.estimateSize());
                    Iterator<String> ji = p.splitAsStream(in).iterator();
                    Iterator<String> ri = ElementSourceFactory.splitAsStream(p, in, stored).iterator();
                    while (ji.hasNext()) {
                        Assert.assertTrue(w + ": hasNext", ri.hasNext());
                        samePiece(in, ji.next(), ri.next(), w + " iterator");
                    }
                    Assert.assertFalse(w + ": exhausted", ri.hasNext());
                    Assert.assertThrows(java.util.NoSuchElementException.class, ri::next);
                }
            }
        }
    }

    @Test
    public void linesMatrix() {
        for (String in : INPUTS) {
            for (boolean stored : new boolean[]{false, true}) {
                String w = "'" + in.replace("\n", "\\n").replace("\r", "\\r") + "'.lines() stored=" + stored;
                List<String> jdk = in.lines().collect(Collectors.toList());
                List<String> rep = ElementSourceFactory.lines(in, stored).collect(Collectors.toList());
                Assert.assertEquals(w + ": count", jdk.size(), rep.size());
                for (int i = 0; i < jdk.size(); i++) {
                    samePiece(in, jdk.get(i), rep.get(i), w + " [" + i + "]");
                }
                Spliterator<String> js = in.lines().spliterator();
                Spliterator<String> rs = ElementSourceFactory.lines(in, stored).spliterator();
                Assert.assertEquals(w + ": characteristics", js.characteristics(), rs.characteristics());
                Assert.assertEquals(w + ": estimateSize", js.estimateSize(), rs.estimateSize());
                // trySplit at the JDK's line boundaries: both halves equal
                Spliterator<String> jp = js.trySplit();
                Spliterator<String> rp = rs.trySplit();
                Assert.assertEquals(w + ": trySplit", jp == null, rp == null);
                if (jp != null) {
                    List<String> a = new ArrayList<>();
                    List<String> b = new ArrayList<>();
                    jp.forEachRemaining(a::add);
                    rp.forEachRemaining(b::add);
                    RepEq.assertRepListEquals(w + ": prefix", a, b);
                    Assert.assertEquals(w + ": rest estimate", js.estimateSize(), rs.estimateSize());
                }
                RepEq.assertRepListEquals(w + ": parallel", in.lines().parallel().collect(Collectors.toList()), ElementSourceFactory.lines(in, stored).parallel().collect(Collectors.toList()));
            }
        }
        Assert.assertThrows(NullPointerException.class, () -> ElementSourceFactory.lines("a\nb", false).spliterator().tryAdvance(null));
    }

    @Test
    public void piecesAreViewsOverTheInputAndStoredCopiesSmallRanges() {
        String big = "x".repeat(100) + "," + "y".repeat(100) + "," + "z";
        String[] shared = ElementSourceFactory.stringSplit(big, ",", false);
        Assert.assertTrue("a SHARED piece is a view", shared[0] instanceof StringView && shared[1] instanceof StringView && shared[2] instanceof StringView);
        String[] st = ElementSourceFactory.stringSplit(big, ",", true);
        Assert.assertSame("a STORED piece under half of the backing is the JDK copy", String.class, st[0].getClass());
        Assert.assertSame(String.class, st[2].getClass());
        String half = "a".repeat(80) + "," + "b";
        Assert.assertTrue("a STORED piece over half of the backing is a view", ElementSourceFactory.stringSplit(half, ",", true)[0] instanceof StringView);
        // a non-String CharSequence input / a rep receiver: the stock call (no view)
        Pattern p = Pattern.compile(",");
        CharBuffer cb = CharBuffer.wrap("aa,bb");
        for (String s : ElementSourceFactory.patternSplit(p, cb, false)) {
            Assert.assertSame(String.class, s.getClass());
        }
        Assert.assertEquals(List.of("aa", "bb"), ElementSourceFactory.splitAsStream(p, CharBuffer.wrap("aa,bb"), false).collect(Collectors.toList()));
    }

    /**
     * A StringView input (the only rep that reaches the factories' non-exact branch) runs the factories'
     * own JDK copy, never the stock call: the oracle is the JDK on a flat copy of the same content, with the input
     * identity mapped (a JDK piece == the flat input iff the rep piece == the view). Pieces nest (views of the view).
     */
    private static List<StringView> repInputs() {
        List<StringView> out = new ArrayList<>();
        for (String in : INPUTS) {
            if (in.isEmpty()) {
                continue; // a rep is never empty
            }
            for (String pad : new String[]{"#", UTF}) {
                String parent = pad + in + pad;
                String v = StringView.create(parent, pad.length(), pad.length() + in.length());
                if (v instanceof StringView sv) {
                    out.add(sv);
                    String outer = StringView.create(pad + parent + pad, pad.length(), pad.length() + parent.length());
                    if (outer instanceof StringView osv && StringView.createView(osv, pad.length(), pad.length() + in.length()) instanceof StringView nested) {
                        out.add(nested); // a view of a view
                    }
                }
            }
        }
        return out;
    }

    private static String flat(StringView v) {
        return new String(v.toCharArray());
    }

    private static void sameRepPiece(StringView view, String flat, String jdk, String rep, String what) {
        RepEq.assertRepEquals(what + ": content", jdk, rep);
        Assert.assertTrue(what + ": rep.equals(jdk)", rep.equals(jdk));
        Assert.assertEquals(what + ": hashCode", jdk.hashCode(), rep.hashCode());
        Assert.assertEquals(what + ": coder", jdk.coder(), rep.coder());
        Assert.assertEquals(what + ": identity with the input", jdk == flat, rep == view);
        if (jdk.isEmpty()) {
            Assert.assertSame(what + ": an empty piece is the JDK's \"\"", jdk, rep);
        }
    }

    private static int sameRepArray(StringView view, String flat, String[] jdk, String[] rep, String what) {
        Assert.assertSame(what + ": array class", String[].class, rep.getClass());
        Assert.assertEquals(what + ": length " + List.of(jdk) + " vs " + List.of(rep), jdk.length, rep.length);
        int views = 0;
        for (int i = 0; i < jdk.length; i++) {
            sameRepPiece(view, flat, jdk[i], rep[i], what + " [" + i + "]");
            views += rep[i] instanceof StringView && rep[i] != view ? 1 : 0;
        }
        return views;
    }

    @Test
    public void repInputSplitMatrix() {
        List<StringView> reps = repInputs();
        Assert.assertTrue("rep inputs incl. UTF-16 views", reps.size() > 40 && reps.stream().anyMatch(v -> v.coder() == 1));
        int views = 0;
        for (StringView v : reps) {
            String f = flat(v);
            Assert.assertNotSame(v, f);
            for (String re : REGEXES) {
                Pattern p = Pattern.compile(re);
                for (boolean stored : new boolean[]{false, true}) {
                    String w = "view('" + f + "').split('" + re + "') stored=" + stored;
                    views += sameRepArray(v, f, f.split(re), ElementSourceFactory.stringSplit(v, re, stored), w);
                    sameRepArray(v, f, p.split(f), ElementSourceFactory.patternSplit(p, v, stored), w + " Pattern");
                    for (int lim : LIMITS) {
                        sameRepArray(v, f, f.split(re, lim), ElementSourceFactory.stringSplit(v, re, lim, stored), w + " limit=" + lim);
                        sameRepArray(v, f, f.splitWithDelimiters(re, lim), ElementSourceFactory.stringSplitWithDelimiters(v, re, lim, stored), w + " withDelimiters limit=" + lim);
                        sameRepArray(v, f, p.split(f, lim), ElementSourceFactory.patternSplit(p, v, lim, stored), w + " Pattern limit=" + lim);
                        sameRepArray(v, f, p.splitWithDelimiters(f, lim), ElementSourceFactory.patternSplitWithDelimiters(p, v, lim, stored), w + " Pattern withDelimiters limit=" + lim);
                    }
                    List<String> js = p.splitAsStream(f).collect(Collectors.toList());
                    List<String> rs = ElementSourceFactory.splitAsStream(p, v, stored).collect(Collectors.toList());
                    sameRepArray(v, f, js.toArray(new String[0]), rs.toArray(new String[0]), w + " splitAsStream");
                    Assert.assertEquals(w + ": characteristics", p.splitAsStream(f).spliterator().characteristics(), ElementSourceFactory.splitAsStream(p, v, stored).spliterator().characteristics());
                    Iterator<String> ri = ElementSourceFactory.splitAsStream(p, v, stored).iterator();
                    for (int i = 0; i < js.size(); i++) {
                        Assert.assertTrue(w + ": hasNext", ri.hasNext());
                        ri.next();
                    }
                    Assert.assertFalse(w + ": exhausted", ri.hasNext());
                    Assert.assertThrows(java.util.NoSuchElementException.class, ri::next);
                }
            }
        }
        Assert.assertTrue("rep pieces are nested views", views > 50);
        StringView v = reps.get(0);
        Assert.assertThrows(java.util.regex.PatternSyntaxException.class, () -> ElementSourceFactory.stringSplit(v, "(", false));
        assertNpe(() -> flat(v).split(null), () -> ElementSourceFactory.stringSplit(v, null, false));
        assertNpe(() -> ((Pattern) null).split(flat(v)), () -> ElementSourceFactory.patternSplit(null, v, false));
        assertNpe(() -> ((Pattern) null).splitAsStream(flat(v)), () -> ElementSourceFactory.splitAsStream(null, v, false));
    }

    @Test
    public void repInputLinesMatrix() {
        for (StringView v : repInputs()) {
            String f = flat(v);
            for (boolean stored : new boolean[]{false, true}) {
                String w = "view('" + f.replace("\n", "\\n").replace("\r", "\\r") + "').lines() stored=" + stored;
                List<String> jdk = f.lines().collect(Collectors.toList());
                List<String> rep = ElementSourceFactory.lines(v, stored).collect(Collectors.toList());
                sameRepArray(v, f, jdk.toArray(new String[0]), rep.toArray(new String[0]), w);
                Spliterator<String> js = f.lines().spliterator();
                Spliterator<String> rs = ElementSourceFactory.lines(v, stored).spliterator();
                Assert.assertEquals(w + ": characteristics", js.characteristics(), rs.characteristics());
                Assert.assertEquals(w + ": estimateSize", js.estimateSize(), rs.estimateSize());
                Spliterator<String> jp = js.trySplit();
                Spliterator<String> rp = rs.trySplit();
                Assert.assertEquals(w + ": trySplit", jp == null, rp == null);
                if (jp != null) {
                    List<String> a = new ArrayList<>();
                    List<String> b = new ArrayList<>();
                    jp.forEachRemaining(a::add);
                    rp.forEachRemaining(b::add);
                    RepEq.assertRepListEquals(w + ": prefix", a, b);
                }
                RepEq.assertRepListEquals(w + ": parallel", f.lines().parallel().collect(Collectors.toList()), ElementSourceFactory.lines(v, stored).parallel().collect(Collectors.toList()));
            }
        }
    }

    @Test
    public void nullsAndLaziness() {
        Pattern p = Pattern.compile(",");
        assertNpe(() -> ((Pattern) null).splitAsStream("a"), () -> ElementSourceFactory.splitAsStream(null, "a", false));
        // a null input: splitAsStream is lazy (no NPE until the terminal), as the JDK's
        Stream<String> js = p.splitAsStream(null);
        Stream<String> rs = ElementSourceFactory.splitAsStream(p, null, false);
        assertNpe(js::count, rs::count);
        assertNpe(() -> p.split(null), () -> ElementSourceFactory.patternSplit(p, null, false));
        assertNpe(() -> p.split(null, 2), () -> ElementSourceFactory.patternSplit(p, null, 2, false));
        assertNpe(() -> ((String) null).split(","), () -> ElementSourceFactory.stringSplit(null, ",", false));
        assertNpe(() -> "a,b".split(null), () -> ElementSourceFactory.stringSplit("a,b", null, false));
        assertNpe(() -> "a,b".split(null, 1), () -> ElementSourceFactory.stringSplit("a,b", null, 1, false));
        assertNpe(() -> ((String) null).lines(), () -> ElementSourceFactory.lines(null, false));
        Assert.assertThrows(java.util.regex.PatternSyntaxException.class, () -> "a".split("("));
        Assert.assertThrows(java.util.regex.PatternSyntaxException.class, () -> ElementSourceFactory.stringSplit("a", "(", false));
        // the matcher is created lazily: a pattern over a mutated builder input sees the content at the terminal
        StringBuilder sb = new StringBuilder("a,b");
        Stream<String> lazy = ElementSourceFactory.splitAsStream(p, sb, false);
        sb.append(",c");
        Assert.assertEquals(3, lazy.count());
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
}
