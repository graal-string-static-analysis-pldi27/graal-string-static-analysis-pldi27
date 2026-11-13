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

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.Function;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.TrivialString;

/**
 * The flat reps ({@link SingleByteString}, and the test-only {@link TrivialString}) behave
 * exactly like a plain {@code String} of the same content, for every override they declare: content, "the result is
 * the receiver" (identity) and the exception (class and message). Every Latin-1 char is checked, for the case mappings
 * under default locales that have special rules (tr, az, lt) and some that do not, and with an explicit locale.
 * Divergences caught include an SBS case mapping that ignores the locale and special casing ({@code "ß".toUpperCase()}
 * giving {@code "ß"}, tr {@code "i"} giving {@code "I"}), a {@code charAt} that throws a plain
 * {@code IndexOutOfBoundsException}, and a TrivialString {@code hashCode()} that is the signed payload for a char above
 * 0x7F.
 */
public class FlatRepJdkParityTest {

    static final Locale[] LOCALES = {Locale.ROOT, Locale.ENGLISH, Locale.GERMAN, Locale.forLanguageTag("tr"), Locale.forLanguageTag("az"),
                    Locale.forLanguageTag("lt"), Locale.forLanguageTag("el"), Locale.forLanguageTag("nl"),
                    // region/script variants of the special-casing languages, and a plain region locale
                    Locale.forLanguageTag("tr-TR"), Locale.forLanguageTag("az-Latn-AZ"), Locale.forLanguageTag("lt-LT"), Locale.forLanguageTag("de-DE")};

    /** The explicit-locale arguments: every default locale above, and null (the JDK's NullPointerException). */
    static final Locale[] EXPLICIT_LOCALES = java.util.Arrays.copyOf(LOCALES, LOCALES.length + 1);

    record Pair(String label, String rep, String plain) {
    }

    /** Every SBS (the whole pool) and every TrivialString payload, each with a fresh plain String of the same content. */
    static List<Pair> pairs() {
        List<Pair> out = new ArrayList<>();
        for (int i = 0; i < 256; i++) {
            SingleByteString s = SingleByteString.create((byte) i);
            out.add(new Pair("SBS[" + i + "]", s, new String(new char[]{(char) i})));
        }
        for (int b = -128; b < 128; b++) {
            TrivialString t = TrivialString.create((byte) b);
            out.add(new Pair("Trivial[" + b + "]", t, new String(new char[]{(char) (byte) b})));
        }
        return out;
    }

    static String contentOf(Object o) {
        if (o == null) {
            return "null";
        }
        CharSequence cs = (CharSequence) o;
        char[] a = new char[cs.length()];
        for (int i = 0; i < a.length; i++) {
            a[i] = cs.charAt(i);
        }
        return new String(a);
    }

    /** The outcome of one call: the result's content and identity, or the exception's class and message. */
    static String outcome(String receiver, Function<String, Object> f) {
        Object r;
        try {
            r = f.apply(receiver);
        } catch (RuntimeException e) {
            return "throws " + e.getClass().getName() + ": " + e.getMessage();
        }
        if (r instanceof CharSequence) {
            return "returns [" + contentOf(r) + "] self=" + (r == receiver);
        }
        return "returns " + r;
    }

    static void check(String op, Function<String, Object> f) {
        for (Pair p : pairs()) {
            Assert.assertEquals(op + " on " + p.label(), outcome(p.plain(), f), outcome(p.rep(), f));
            checkResultClass(op, p, f);
        }
    }

    /**
     * The class of an SBS receiver's String result: the receiver itself, the pool entry (a one-char Latin-1
     * result: SingleByteString.create of that char, the identity contract of the SB factories), or a plain String.
     */
    static void checkResultClass(String op, Pair p, Function<String, Object> f) {
        if (!(p.rep() instanceof SingleByteString)) {
            return;
        }
        Object r;
        try {
            r = f.apply(p.rep());
        } catch (RuntimeException e) {
            return;
        }
        if (!(r instanceof String s) || r == p.rep()) {
            return;
        }
        if (s.length() == 1 && s.charAt(0) <= 0xFF) {
            Assert.assertSame(op + " on " + p.label() + ": a one-char Latin-1 result is the pool entry", SingleByteString.create(s.charAt(0)), r);
        } else {
            Assert.assertSame(op + " on " + p.label() + ": any other result is a plain String", String.class, r.getClass());
        }
    }

    static void checkUnderEveryDefaultLocale(String op, Function<String, Object> f) {
        Locale saved = Locale.getDefault();
        try {
            for (Locale l : LOCALES) {
                Locale.setDefault(l);
                check(op + " (default locale " + l.toLanguageTag() + ")", f);
            }
        } finally {
            Locale.setDefault(saved);
        }
    }

    @Test
    public void toUpperCase() {
        checkUnderEveryDefaultLocale("toUpperCase()", String::toUpperCase);
        for (Locale l : EXPLICIT_LOCALES) {
            check("toUpperCase(" + (l == null ? "null" : l.toLanguageTag()) + ")", s -> s.toUpperCase(l));
        }
    }

    @Test
    public void toLowerCase() {
        checkUnderEveryDefaultLocale("toLowerCase()", String::toLowerCase);
        for (Locale l : EXPLICIT_LOCALES) {
            check("toLowerCase(" + (l == null ? "null" : l.toLanguageTag()) + ")", s -> s.toLowerCase(l));
        }
    }

    /** The named divergence cases, spelled out (all covered by the loops above). */
    @Test
    public void theNamedCases() {
        Locale saved = Locale.getDefault();
        try {
            Locale.setDefault(Locale.ROOT);
            Assert.assertEquals("SS", SingleByteString.create((byte) 0xDF).toUpperCase());
            Locale.setDefault(Locale.forLanguageTag("tr"));
            Assert.assertEquals("İ", SingleByteString.create((byte) 'i').toUpperCase());
            Assert.assertEquals("ı", SingleByteString.create((byte) 'I').toLowerCase());
            Locale.setDefault(Locale.forLanguageTag("lt"));
            Assert.assertEquals(3, SingleByteString.create((byte) 0xCC).toLowerCase().length());
            SingleByteString a = SingleByteString.create((byte) 'A');
            Assert.assertSame("unchanged: the receiver itself, as the JDK", a, a.toUpperCase());
        } finally {
            Locale.setDefault(saved);
        }
        try {
            SingleByteString.create((byte) 'a').charAt(1);
            Assert.fail("charAt(1)");
        } catch (StringIndexOutOfBoundsException e) {
            Assert.assertEquals(outcome("a", s -> s.charAt(1)), "throws " + e.getClass().getName() + ": " + e.getMessage());
        }
    }

    /** The SBS override (index + offset in [0, 1]) against Character.offsetByCodePoints on a plain String. */
    @Test
    public void offsetByCodePoints() {
        int[] vals = {Integer.MIN_VALUE, -2, -1, 0, 1, 2, 3, Integer.MAX_VALUE};
        for (int i : vals) {
            for (int o : vals) {
                check("offsetByCodePoints(" + i + ", " + o + ")", s -> s.offsetByCodePoints(i, o));
            }
        }
    }

    /**
     * Equals against arguments of every kind (plain, flat, value-null reps; 0-2 chars; one-char
     * UTF-16 and two-char strings): the content equality, whichever arm answers (the exact-String arm first). On the JVM
     * the exact arm runs its hosted form (content); the image form (the value/coder aliases) is exercised by the
     * full-path image tests.
     */
    @Test
    public void equalsEveryArgumentKind() {
        List<String> args = new ArrayList<>(FlatRepPremiseTest.stringArguments());
        // one-char UTF-16 strings (U+0100, U+20AC) and length-2 strings of every coder
        for (String c : List.of("\u0100", "\u20ac", "aa", "\u00ff\u00ff", "a\u0100", "\u0100a")) {
            args.add(new String(c.toCharArray()));
        }
        for (int i = 0; i < 256; i++) {
            SingleByteString s = SingleByteString.create((byte) i);
            String plain = new String(new char[]{(char) i});
            for (String a : args) {
                boolean want = contentOf(a).equals(plain);
                Assert.assertEquals("SBS[" + i + "].equals(" + a.getClass().getSimpleName() + " [" + contentOf(a) + "])", want, s.equals(a));
            }
        }
    }

    @Test
    public void charAt() {
        for (int i : new int[]{0, 1, 2, -1, Integer.MIN_VALUE, Integer.MAX_VALUE}) {
            check("charAt(" + i + ")", s -> (int) s.charAt(i));
        }
    }

    @Test
    public void equalsHashCodeToString() {
        check("hashCode()", s -> s.hashCode());
        check("toString()", String::toString);
        check("length()", s -> s.length());
        check("equals(null)", s -> s.equals(null));
        check("equals(Object)", s -> s.equals(new Object()));
        for (int i = 0; i < 256; i += 17) {
            String other = new String(new char[]{(char) i});
            SingleByteString sbs = SingleByteString.create((byte) i);
            check("equals(\"" + i + "\")", s -> s.equals(other));
            check("\"" + i + "\".equals", s -> other.equals(s));
            check("equals(SBS " + i + ")", s -> s.equals(sbs));
        }
        check("equals(\"ab\")", s -> s.equals("ab"));
    }
}
