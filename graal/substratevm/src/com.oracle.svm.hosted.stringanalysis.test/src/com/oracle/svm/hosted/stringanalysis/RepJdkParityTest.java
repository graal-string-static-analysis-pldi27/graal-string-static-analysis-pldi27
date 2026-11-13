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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Supplier;

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
 * Every rep method with its own body answers exactly as the JDK
 * does on the plain string with the same chars — the same bytes, the same int, the same boolean, the same exception
 * class (and message where the JDK body produces it), and for the case mappings the same identity rule (the receiver
 * itself exactly when the JDK returns its receiver).
 *
 * <p>Inputs: Latin-1 and UTF-16 contents with empty parts, high Latin-1 bytes, chars unmappable in ISO-8859-1 or
 * US-ASCII, paired and unpaired surrogates; every rep kind of {@link RepEqualsMatrixTest#MAKERS} (every split, so
 * surrogate pairs straddle part boundaries), plus lazy reps over value-null children (a view, a rope, a nested
 * array-lazy string).
 */
public class RepJdkParityTest {

    static final String[] CONTENTS = {"", "a", "é", "ÿß", "aé€", "😀", "a😀b", "\ud800x", "x\udc00",
                    "􏿿\ud800", "€éÿA", "AbC", "Ωmega", "İi", "µß", "x,y,z", "a\u0080 ", "ZZ"};

    static final Charset[] CHARSETS = {StandardCharsets.UTF_8, StandardCharsets.ISO_8859_1, StandardCharsets.US_ASCII, StandardCharsets.UTF_16,
                    Charset.forName("windows-1252")};

    static final String[] CHARSET_NAMES = {"UTF-8", "utf8", "ISO-8859-1", "latin1", "US-ASCII", "ascii", "UTF-16LE", "no-such-charset", "bad name!"};

    record Inst(String label, String s, String content) {
    }

    /** Every rep instance of every content, plus lazy reps over value-null children. */
    static List<Inst> instances() {
        List<Inst> out = new ArrayList<>();
        for (String c : CONTENTS) {
            for (Map.Entry<Class<?>, Function<String, List<String>>> e : RepEqualsMatrixTest.MAKERS.entrySet()) {
                if (e.getKey() == ArrayLazyString.class && c.length() > 6 || e.getKey() == InterleavedStringArray.class && c.length() > 6) {
                    continue;
                }
                int i = 0;
                for (String s : e.getValue().apply(new String(c.toCharArray()))) {
                    Assert.assertEquals("maker content", c, RepEqualsMatrixTest.contentOf(s));
                    out.add(new Inst(e.getKey().getSimpleName() + "#" + (i++) + "[" + esc(c) + "]", s, c));
                }
            }
            for (int i = 0; i <= c.length(); i++) {
                String l = c.substring(0, i);
                String r = c.substring(i);
                String vl = StringView.create("€" + l, 1, 1 + l.length());
                String vr = StringView.create("q" + r + "q", 1, 1 + r.length());
                if (r.chars().allMatch(ch -> ch <= 0xff)) {
                    out.add(new Inst("ThreeWay(view,rope,\"\")#" + i + "[" + esc(c) + "]", ThreeWayString.create(vl, RopeString.create("", r), ""), c));
                }
                out.add(new Inst("Rope(view,view)#" + i + "[" + esc(c) + "]", RopeString.create(vl, StringView.create("€" + r, 1, 1 + r.length())), c));
                out.add(new Inst("FixedConcat4(view,ALS,\"\",rope)#" + i + "[" + esc(c) + "]",
                                FixedConcat4.create(vl, ArrayLazyString.create(new String[]{"", r}), "", RopeString.create("", "")), c));
                out.add(new Inst("ALS(view,rope,view)#" + i + "[" + esc(c) + "]",
                                ArrayLazyString.create(new String[]{vl, RopeString.create("", ""), StringView.create("€" + r, 1, 1 + r.length())}), c));
                out.add(new Inst("ISA(view|rope)#" + i + "[" + esc(c) + "]", InterleavedStringArray.create(new String[]{vl, RopeString.create(r, "")}, ""), c));
                if (!r.isEmpty()) {
                    Assert.assertEquals(r, RepEqualsMatrixTest.contentOf(vr));
                }
            }
        }
        for (Inst in : out) {
            Assert.assertEquals(in.label(), in.content(), RepEqualsMatrixTest.contentOf(in.s()));
        }
        return out;
    }

    static String esc(String c) {
        StringBuilder sb = new StringBuilder();
        for (char ch : c.toCharArray()) {
            if (ch >= 0x20 && ch < 0x7f) {
                sb.append(ch);
            } else {
                sb.append(String.format("\\u%04x", (int) ch));
            }
        }
        return sb.toString();
    }

    static String plain(String c) {
        return new String(c.toCharArray());
    }

    /** The outcome of an operation: its value rendered, or its exception class (and message when asked). */
    static String outcome(Supplier<Object> op, boolean withMessage) {
        return render(eval(op), withMessage);
    }

    /** The value of an operation, or the RuntimeException it threw (wrapped, so a thrown value is not a result). */
    record Thrown(RuntimeException ex) {
    }

    static Object eval(Supplier<Object> op) {
        try {
            return op.get();
        } catch (RuntimeException ex) {
            return new Thrown(ex);
        }
    }

    static String render(Object r, boolean withMessage) {
        if (r instanceof Thrown t) {
            return "throws " + t.ex().getClass().getName() + (withMessage ? ": " + t.ex().getMessage() : "");
        }
        if (r instanceof byte[] b) {
            return "bytes" + Arrays.toString(b);
        }
        if (r instanceof String str) {
            // by content here; the coder-sensitive String.equals against the JDK's result is checked in same()
            return "string:" + RepEqualsMatrixTest.contentOf(str);
        }
        return "value:" + r;
    }

    interface Op {
        Object run() throws Exception;
    }

    static Supplier<Object> s(Op op) {
        return () -> {
            try {
                return op.run();
            } catch (RuntimeException e) {
                throw e;
            } catch (Exception e) {
                throw new IllegalStateException("checked " + e.getClass().getName() + ": " + e.getMessage());
            }
        };
    }

    static int checks;

    static void same(String what, Supplier<Object> jdk, Supplier<Object> rep, boolean withMessage) {
        checks++;
        Object j = eval(jdk);
        Object r = eval(rep);
        Assert.assertEquals(what, render(j, withMessage), render(r, withMessage));
        if (j instanceof String js && r instanceof String rs) {
            assertJdkEquals(what, js, rs);
        }
    }

    /**
     * A String result must be {@code equals} to the JDK's in both directions, with the same
     * hash. A plain String's {@code equals} compares coders (JDK 25 {@code String.equals}), so a non-compact UTF-16
     * result with Latin-1 chars fails here while the content comparison above passes. A plain result
     * must also have the JDK result's coder (the compact one).
     */
    static void assertJdkEquals(String what, String jdkResult, String repResult) {
        Assert.assertTrue(what + ": rep result equals the JDK's", repResult.equals(jdkResult));
        Assert.assertTrue(what + ": the JDK's result equals the rep result", RepEq.eq(jdkResult, repResult));
        Assert.assertEquals(what + ": hashCode", jdkResult.hashCode(), repResult.hashCode());
        Assert.assertTrue(what + ": the JDK's result is compact", jdkResult.coder() == compactCoder(jdkResult));
        if (repResult.getClass() == String.class) {
            Assert.assertEquals(what + ": a plain result has the compact coder", compactCoder(jdkResult), repResult.coder());
        }
    }

    /** The coder the JDK gives a String of these chars: LATIN1 (0) when every char is at most 0xFF, else UTF16 (1). */
    static byte compactCoder(String s) {
        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) > 0xFF) {
                return 1;
            }
        }
        return 0;
    }

    @Test
    public void charsetGetBytesIsTheJdks() {
        checks = 0;
        for (Inst in : instances()) {
            String p = plain(in.content());
            String r = in.s();
            for (Charset cs : CHARSETS) {
                same(in.label() + ".getBytes(" + cs + ")", () -> p.getBytes(cs), () -> r.getBytes(cs), true);
            }
            same(in.label() + ".getBytes((Charset) null)", () -> p.getBytes((Charset) null), () -> r.getBytes((Charset) null), true);
            same(in.label() + ".getBytes()", () -> p.getBytes(), () -> r.getBytes(), true);
            for (String name : CHARSET_NAMES) {
                same(in.label() + ".getBytes(\"" + name + "\")", s(() -> p.getBytes(name)), s(() -> r.getBytes(name)), true);
            }
            same(in.label() + ".getBytes((String) null)", s(() -> p.getBytes((String) null)), s(() -> r.getBytes((String) null)), true);
        }
        Assert.assertTrue("checks " + checks, checks > 10000);
    }

    @Test
    @SuppressWarnings("deprecation")
    public void deprecatedRangeGetBytesIsTheJdks() {
        for (Inst in : instances()) {
            String p = plain(in.content());
            String r = in.s();
            int n = p.length();
            // exact messages from the lazy reps (their failure path is the JDK body); StringView keeps its own
            // bounds messages (a known difference), so only the exception class there
            boolean msg = !(r instanceof StringView);
            for (int b = -1; b <= n + 1; b++) {
                for (int e = b - 1; e <= n + 1; e++) {
                    for (int d = -1; d <= 2; d++) {
                        int fb = b;
                        int fe = e;
                        int fd = d;
                        int size = Math.max(0, n + 1);
                        same(in.label() + ".getBytes(" + b + "," + e + ",dst," + d + ")", () -> {
                            byte[] dst = new byte[size];
                            Arrays.fill(dst, (byte) 7);
                            p.getBytes(fb, fe, dst, fd);
                            return dst;
                        }, () -> {
                            byte[] dst = new byte[size];
                            Arrays.fill(dst, (byte) 7);
                            r.getBytes(fb, fe, dst, fd);
                            return dst;
                        }, msg);
                    }
                }
            }
            same(in.label() + ".getBytes(0,n,null,0)", () -> {
                p.getBytes(0, n, null, 0);
                return "";
            }, () -> {
                r.getBytes(0, n, null, 0);
                return "";
            }, false);
        }
    }

    /**
     * The protected {@code getBytes(byte[], int, byte)}: {@code StringBuilder.append(String)} into Latin-1 and UTF-16
     * builders (every rep, RopeString included).
     */
    @Test
    public void builderAppendIsTheJdks() {
        for (Inst in : instances()) {
            String p = plain(in.content());
            String r = in.s();
            for (String prefix : new String[]{"", "x", "€"}) {
                same(in.label() + " append after " + esc(prefix), () -> new StringBuilder(prefix).append(p).append('!').toString(),
                                () -> new StringBuilder(prefix).append(r).append('!').toString(), true);
                same(in.label() + " StringBuffer append after " + esc(prefix), () -> new StringBuffer(prefix).append(p).append(p).toString(),
                                () -> new StringBuffer(prefix).append(r).append(r).toString(), true);
            }
        }
    }

    @Test
    public void equalsAndCompareToAreTheJdks() {
        List<Inst> all = instances();
        List<String> args = new ArrayList<>();
        for (String c : CONTENTS) {
            args.add(plain(c));
            args.add(plain(c) + "a");
            if (!c.isEmpty()) {
                args.add(plain(c.substring(0, c.length() - 1)));
                args.add(plain(c.substring(0, c.length() - 1) + "￿"));
                args.add(StringView.create("€" + c, 1, 1 + c.length()));
                args.add(RopeString.create(c.substring(0, 1), c.substring(1)));
                args.add(ArrayLazyString.create(new String[]{c.substring(0, 1), "", c.substring(1)}));
            }
        }
        args.add(SingleByteString.create('a'));
        args.add(TrivialString.create((byte) 'Z'));
        for (Inst in : all) {
            String p = plain(in.content());
            String r = in.s();
            for (String a : args) {
                String pa = plain(RepEqualsMatrixTest.contentOf(a));
                // a plain or flat receiver runs the stock equals body; with a rep argument the parent calls the REDIRECT target
                same(in.label() + ".equals(" + esc(pa) + ")", () -> p.equals(pa), () -> flatOrPlain(r) ? r.maybeCustomStringEquals(a) : r.equals(a), true);
                // a plain or flat receiver runs the stock body, which reads the argument's value();
                // with a rep argument the parent calls the redirect target maybeCustomStringCompareTo there
                same(in.label() + ".compareTo(" + esc(pa) + ")", () -> p.compareTo(pa), () -> flatOrPlain(r) ? r.maybeCustomStringCompareTo(a) : r.compareTo(a), true);
            }
            same(in.label() + ".equals(null)", () -> p.equals(null), () -> r.equals(null), true);
            same(in.label() + ".equals(Integer)", () -> p.equals(42), () -> r.equals(42), true);
            same(in.label() + ".compareTo(null)", () -> p.compareTo(null), () -> r.compareTo(null), false);
        }
    }

    static boolean flatOrPlain(String s) {
        return s.getClass() == String.class || InlineCacheRegistry.isValueCarryingFlatRep(s.getClass());
    }

    static boolean isView(Inst in) {
        return in.s() instanceof StringView;
    }

    @Test
    public void stringViewMethodsAreTheJdks() {
        Locale[] locales = {Locale.ROOT, Locale.ENGLISH, Locale.forLanguageTag("tr"), Locale.forLanguageTag("lt"), Locale.forLanguageTag("az")};
        int views = 0;
        for (Inst in : instances()) {
            if (!isView(in)) {
                continue;
            }
            views++;
            String p = plain(in.content());
            String r = in.s();
            int n = p.length();
            for (Locale l : locales) {
                same(in.label() + ".toUpperCase(" + l + ")", () -> RepEqualsMatrixTest.contentOf(p.toUpperCase(l)) + " same=" + (p.toUpperCase(l) == p),
                                () -> RepEqualsMatrixTest.contentOf(r.toUpperCase(l)) + " same=" + (r.toUpperCase(l) == r), true);
                same(in.label() + ".toLowerCase(" + l + ")", () -> RepEqualsMatrixTest.contentOf(p.toLowerCase(l)) + " same=" + (p.toLowerCase(l) == p),
                                () -> RepEqualsMatrixTest.contentOf(r.toLowerCase(l)) + " same=" + (r.toLowerCase(l) == r), true);
            }
            same(in.label() + ".toUpperCase(null)", () -> p.toUpperCase(null), () -> r.toUpperCase(null), true);
            same(in.label() + ".toLowerCase(null)", () -> p.toLowerCase(null), () -> r.toLowerCase(null), true);
            List<String> needles = new ArrayList<>(List.of("", "zz", "€", "a", "é", "\ud83d", "\ude00", "😀", "y,"));
            for (int b = 0; b <= n; b++) {
                for (int e = b; e <= n; e++) {
                    needles.add(plain(p.substring(b, e)));
                }
            }
            List<String> needleReps = new ArrayList<>();
            for (String nd : needles) {
                needleReps.add(nd);
                needleReps.add(StringView.create("€" + nd, 1, 1 + nd.length()));
                needleReps.add(RopeString.create(nd, ""));
            }
            for (String nd : needleReps) {
                String pn = plain(RepEqualsMatrixTest.contentOf(nd));
                for (int f = -2; f <= n + 2; f++) {
                    int ff = f;
                    same(in.label() + ".indexOf(" + esc(pn) + "," + f + ")", () -> p.indexOf(pn, ff), () -> r.indexOf(nd, ff), true);
                    same(in.label() + ".startsWith(" + esc(pn) + "," + f + ")", () -> p.startsWith(pn, ff), () -> r.startsWith(nd, ff), true);
                }
                same(in.label() + ".indexOf(" + esc(pn) + ")", () -> p.indexOf(pn), () -> r.indexOf(nd), true);
                same(in.label() + ".startsWith(" + esc(pn) + ")", () -> p.startsWith(pn), () -> r.startsWith(nd), true);
                same(in.label() + ".endsWith(" + esc(pn) + ")", () -> p.endsWith(pn), () -> r.endsWith(nd), true);
                same(in.label() + ".contentEquals(" + esc(pn) + ")", () -> p.contentEquals(pn), () -> r.contentEquals(nd), true);
                same(in.label() + ".contentEquals(SB " + esc(pn) + ")", () -> p.contentEquals(new StringBuilder(pn)), () -> r.contentEquals(new StringBuilder(pn)), true);
            }
            int[] chars = {-1, 'a', 'z', 0xe9, 0xff, 0x100, 0x20ac, 0xd83d, 0xde00, 0x1f600, 0x10ffff + 1, ','};
            for (int ch : chars) {
                for (int f = -2; f <= n + 2; f++) {
                    int ff = f;
                    same(in.label() + ".indexOf(" + ch + "," + f + ")", () -> p.indexOf(ch, ff), () -> r.indexOf(ch, ff), true);
                    same(in.label() + ".lastIndexOf(" + ch + "," + f + ")", () -> p.lastIndexOf(ch, ff), () -> r.lastIndexOf(ch, ff), true);
                    for (int g = -1; g <= n + 1; g++) {
                        int fg = g;
                        same(in.label() + ".indexOf(" + ch + "," + f + "," + g + ")", () -> p.indexOf(ch, ff, fg), () -> r.indexOf(ch, ff, fg), false);
                    }
                }
                same(in.label() + ".indexOf(" + ch + ")", () -> p.indexOf(ch), () -> r.indexOf(ch), true);
                same(in.label() + ".lastIndexOf(" + ch + ")", () -> p.lastIndexOf(ch), () -> r.lastIndexOf(ch), true);
            }
            for (int k = -1; k <= 3; k++) {
                int fk = k;
                same(in.label() + ".repeat(" + k + ")", () -> p.repeat(fk), () -> r.repeat(fk), true);
            }
            same(in.label() + ".regionMatches(ic)", () -> p.regionMatches(true, 0, "A", 0, 1), () -> r.regionMatches(true, 0, "A", 0, 1), true);
        }
        Assert.assertTrue("views " + views, views > 50);
    }

    /**
     * Every view factory is coder-exact. A view of a Latin-1-only range of a UTF-16 parent
     * (substring, nested, trim/strip of a UTF-16 view, a UTF-16 builder holding only Latin-1 chars) is the compact
     * String the JDK makes, so appending/concatenating it gives a String that {@code equals} the literal; a range with a
     * char above 0xFF stays a view, and every view has the compact coder of its content.
     */
    @Test
    public void viewsAreCoderExact() {
        int views = 0;
        int copies = 0;
        for (String c : CONTENTS) {
            String parent = "€€" + c + "€";
            List<String> made = new ArrayList<>();
            made.add(StringView.create(plain(parent), 2, 2 + c.length()));
            made.add(StringView.create(plain(parent).substring(1), 1, 1 + c.length())); // a plain UTF-16 parent, 1-arg base
            String outer = StringView.create(plain(parent), 1, parent.length());
            made.add(StringView.create(outer, 1, 1 + c.length())); // nested
            if (outer instanceof StringView ov) {
                made.add(StringView.createView(ov, 1, 1 + c.length()));
            }
            if (!c.isEmpty() && c.equals(c.strip())) {
                // strip* can remove non-Latin-1 white space (U+2000), so a UTF-16 view strips to a Latin-1-only range
                // (trim removes only chars <= ' ', so it keeps every char above 0xFF of a coder-exact view)
                String padded = StringView.create(plain("€ \u2000" + c + "\u2000 "), 1);
                Assert.assertTrue(padded instanceof StringView);
                made.add(((StringView) padded).strip());
                made.add(((StringView) ((StringView) padded).stripLeading()).stripTrailing());
                made.add(((StringView) ((StringView) padded).stripTrailing()).stripLeading());
            }
            StringBuilder sb = new StringBuilder("€").append(c);
            sb.deleteCharAt(0); // a UTF-16 builder holding c (JDK: maybeLatin1, toString compresses)
            made.add(StringView.create(sb));
            StringBuffer sbuf = new StringBuffer("€").append(c);
            sbuf.deleteCharAt(0);
            made.add(StringView.create(sbuf));
            for (String v : made) {
                String what = "view of [" + esc(c) + "] " + v.getClass().getSimpleName();
                Assert.assertEquals(what + " content", c, RepEqualsMatrixTest.contentOf(v));
                Assert.assertEquals(what + " coder", compactCoder(c), v.coder());
                if (v instanceof StringView) {
                    views++;
                } else {
                    copies++;
                }
                String p = plain(c);
                same(what + " append", () -> new StringBuilder().append(p).toString(), () -> new StringBuilder().append(v).toString(), true);
                same(what + " append after x", () -> new StringBuilder("x").append(p).toString(), () -> new StringBuilder("x").append(v).toString(), true);
                same(what + " +", () -> p + "!", () -> v + "!", true);
                same(what + " concat", () -> "x".concat(p), () -> "x".concat(v), true);
                same(what + " join", () -> String.join(",", p, "a"), () -> String.join(",", v, "a"), true);
                same(what + " lazy append", () -> new StringBuilder().append(p + "q").toString(),
                                () -> new StringBuilder().append(ArrayLazyString.create(new String[]{v, "q"})).toString(), true);
                Assert.assertTrue(what + " in a HashSet", new java.util.HashSet<>(List.of(p)).contains(new StringBuilder().append(v).toString()));
            }
        }
        Assert.assertTrue("views " + views + ", copies " + copies, views > 20 && copies > 20);
    }
}
