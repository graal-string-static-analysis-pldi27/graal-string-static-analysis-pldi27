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

import com.oracle.svm.core.stringrep.StringView;

/**
 * The StringView overrides return
 * {@code this} exactly where the JDK's {@code String} returns its receiver, and {@code ""} exactly where it returns the
 * empty literal. Each case compares a view with a fresh plain String of the same content (never interned, so its
 * identity is its own): content, "result is the receiver" and "result is the {@code ""} literal" must all agree.
 * Views over Latin-1 and UTF-16 backings are covered, including a UTF-16 backing whose sub-range holds only Latin-1
 * characters. Also {@code offsetByCodePoints}: the local loop gives the JDK's results and exception classes.
 */
public class StringViewNoOpIdentityTest {

    record Case(String label, String backing, int from, int end) {
        /** Null when the factory gives the compact plain copy (a Latin-1-only range of a UTF-16 backing). */
        StringView view() {
            String made = StringView.create(backing, from, end);
            if (made instanceof StringView v) {
                return v;
            }
            Assert.assertTrue(label + ": the compact copy", made.getClass() == String.class && made.isLatin1() && made.equals(plain()));
            return null;
        }

        String plain() {
            return new String(backing.substring(from, end).toCharArray());
        }
    }

    static List<Case> cases() {
        List<Case> out = new ArrayList<>();
        String[] contents = {"abc", "  abc  ", "abc  ", "  abc", "   ", "", "ABC", "a b", " abc ", "  ",
                        "\t\n", "straße", "Iİiı", "xĀy", " Ā ", "😀z"};
        for (String c : contents) {
            out.add(new Case("whole[" + c + "]", c, 0, c.length()));
            out.add(new Case("inner[" + c + "]", "#" + c + "#", 1, c.length() + 1));
            out.add(new Case("utf16[" + c + "]", "ā" + c + "ā", 1, c.length() + 1));
        }
        return out;
    }

    /** A fresh plain copy of a result's characters (never compares a view through String.equals). */
    static String contentOf(Object o) {
        CharSequence cs = (CharSequence) o;
        char[] a = new char[cs.length()];
        for (int i = 0; i < a.length; i++) {
            a[i] = cs.charAt(i);
        }
        return new String(a);
    }

    static void check(String op, Function<String, Object> f) {
        for (Case c : cases()) {
            String p = c.plain();
            StringView v = c.view();
            if (v == null) {
                continue;
            }
            Object rp = f.apply(p);
            Object rv = f.apply(v);
            String where = op + " on " + c.label();
            Assert.assertEquals(where + ": content", contentOf(rp), contentOf(rv));
            Assert.assertEquals(where + ": result == receiver", rp == p, rv == v);
            Assert.assertEquals(where + ": result == \"\"", rp == "", rv == "");
        }
    }

    @Test
    public void trim() {
        check("trim", String::trim);
    }

    @Test
    public void strip() {
        check("strip", String::strip);
        check("stripLeading", String::stripLeading);
        check("stripTrailing", String::stripTrailing);
    }

    @Test
    public void substringAndSubSequence() {
        check("substring(0)", s -> s.substring(0));
        check("substring(0,len)", s -> s.substring(0, s.length()));
        check("subSequence(0,len)", s -> s.subSequence(0, s.length()));
        check("substring(len)", s -> s.substring(s.length()));
        check("substring(1)", s -> s.isEmpty() ? s : s.substring(1));
        check("substring(0,len-1)", s -> s.isEmpty() ? s : s.substring(0, s.length() - 1));
    }

    @Test
    public void repeat() {
        check("repeat(1)", s -> s.repeat(1));
        check("repeat(0)", s -> s.repeat(0));
        check("repeat(2)", s -> s.repeat(2));
    }

    @Test
    public void caseMapping() {
        for (Locale l : new Locale[]{Locale.ROOT, Locale.forLanguageTag("tr"), Locale.forLanguageTag("lt"), Locale.GERMAN}) {
            check("toUpperCase(" + l + ")", s -> s.toUpperCase(l));
            check("toLowerCase(" + l + ")", s -> s.toLowerCase(l));
        }
        check("toUpperCase()", String::toUpperCase);
        check("toLowerCase()", String::toLowerCase);
        check("toString()", String::toString);
    }

    @Test
    public void exceptionsUnchanged() {
        StringView v = (StringView) StringView.create("abcdef", 1, 4);
        Assert.assertThrows(StringIndexOutOfBoundsException.class, () -> v.substring(0, 4));
        Assert.assertThrows(StringIndexOutOfBoundsException.class, () -> v.substring(-1));
        Assert.assertThrows(IllegalArgumentException.class, () -> v.repeat(-1));
    }

    static String outcome(CharSequence s, int index, int offset) {
        try {
            return "=" + (s instanceof String str ? str.offsetByCodePoints(index, offset) : -99);
        } catch (IndexOutOfBoundsException e) {
            return e.getClass().getName();
        }
    }

    @Test
    public void offsetByCodePointsMatchesTheJdk() {
        for (Case c : cases()) {
            String p = c.plain();
            StringView v = c.view();
            if (v == null) {
                continue;
            }
            for (int index = -1; index <= p.length() + 1; index++) {
                for (int offset = -4; offset <= 4; offset++) {
                    Assert.assertEquals(c.label() + " offsetByCodePoints(" + index + ", " + offset + ")", outcome(p, index, offset), outcome(v, index, offset));
                }
            }
        }
    }
}
