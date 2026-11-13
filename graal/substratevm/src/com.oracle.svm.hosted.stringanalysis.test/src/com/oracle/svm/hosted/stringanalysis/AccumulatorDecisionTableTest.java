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
import java.util.List;
import java.util.function.Consumer;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * The Accumulator View's pass-1 decision table and its runtime premise.
 * <ul>
 * <li>The table: which builder methods keep a builder only growing ({@link AccumulatorWhitelist#accumulatorUsageRow}).</li>
 * <li>The premise, on the real JDK classes: a {@link StringView} over a builder's buffer (the parent's factory
 * {@code StringView.create(StringBuilder|StringBuffer)}, in its sharing regime) keeps its content under every public
 * overload of every growing method (incl. reallocation and Latin-1 → UTF-16 inflation afterwards), and each mutator the
 * table rejects does change it (the rejections are necessary, not just conservative).</li>
 * </ul>
 */
public class AccumulatorDecisionTableTest {

    private static final String[] BUILDERS = {"java.lang.AbstractStringBuilder", "java.lang.StringBuilder", "java.lang.StringBuffer"};
    private static final String[] MUTATORS = {"setLength", "delete", "deleteCharAt", "insert", "replace", "reverse", "setCharAt",
                    "getValue", "getBytes", "putCharsAt", "field:value", "field:count"};

    @Test
    public void growingMethodsAreGrowing() {
        for (String b : BUILDERS) {
            for (String m : AccumulatorWhitelist.W_GROW) {
                Assert.assertEquals(b + "." + m, AccumulatorWhitelist.AccRow.GROWING, AccumulatorWhitelist.accumulatorUsageRow(b, m, UsageRole.RECEIVER));
            }
        }
    }

    @Test
    public void everythingElseOnABuilderRejects() {
        for (String b : BUILDERS) {
            for (String m : MUTATORS) {
                Assert.assertEquals(b + "." + m, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(b, m, UsageRole.RECEIVER));
            }
            // a builder-declared site never counts as a read in another role (the JDK's builder bodies may write it)
            Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(b, "append", UsageRole.PARAMETER));
        }
        // StringWriter has its own table (StringWriterAccumulatorTest); its escape getBuffer rejects
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.io.StringWriter", "getBuffer", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(null, null, UsageRole.RECEIVER));
    }

    @Test
    public void readsOutsideTheBuilder() {
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow("java.lang.String", "equals", UsageRole.PARAMETER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow("org.openjdk.jmh.infra.Blackhole", "consume", UsageRole.PARAMETER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow("java.lang.Object", "getClass", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow("java.lang.String", "equals", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.READ, AccumulatorWhitelist.accumulatorUsageRow(null, null, UsageRole.NONE));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.String", "length", UsageRole.RECEIVER));
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.CharSequence", "chars", UsageRole.RECEIVER));
    }

    @Test
    public void seedableExtractionIsTheParentsToString() {
        Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction("java.lang.StringBuilder", "toString", ""));
        Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction("java.lang.StringBuffer", "toString", null));
        Assert.assertFalse("no parent factory for substring yet", AccumulatorWhitelist.isSeedableExtraction("java.lang.AbstractStringBuilder", "substring", "I,I"));
        Assert.assertFalse(AccumulatorWhitelist.isSeedableExtraction("java.lang.String", "toString", ""));
        Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction("java.io.StringWriter", "toString", ""));
    }

    /**
     * Every public method of the three JDK builder classes is classified (growing / read-only / mutating),
     * in exactly one class; a new JDK method fails here until it is classified in AccumulatorWhitelist. The paper's
     * W_accumulator (minus StringWriter's flush/close) is contained in the pass-1 whitelist.
     */
    @Test
    public void everyPublicBuilderMethodIsClassified() throws ClassNotFoundException {
        java.util.Set<String> seen = new java.util.TreeSet<>();
        for (String c : BUILDERS) {
            for (Method m : Class.forName(c).getDeclaredMethods()) {
                if (!Modifier.isPublic(m.getModifiers())) {
                    continue;
                }
                String n = m.getName();
                seen.add(n);
                int classes = (AccumulatorWhitelist.GROWING_METHODS.contains(n) ? 1 : 0) + (AccumulatorWhitelist.READ_ONLY_METHODS.contains(n) ? 1 : 0) +
                                (AccumulatorWhitelist.MUTATING_METHODS.contains(n) ? 1 : 0);
                Assert.assertEquals("unclassified (or doubly classified) builder method " + c + "." + n, 1, classes);
            }
        }
        // no stale entries: every classified name (but the constructors) is a real public method
        for (java.util.Set<String> set : List.of(AccumulatorWhitelist.GROWING_METHODS, AccumulatorWhitelist.READ_ONLY_METHODS, AccumulatorWhitelist.MUTATING_METHODS)) {
            for (String n : set) {
                Assert.assertTrue("stale entry " + n, n.equals("<init>") || seen.contains(n));
            }
        }
        for (String m : AccumulatorWhitelist.W_ACCUMULATOR) {
            Assert.assertTrue(m, m.equals("flush") || m.equals("close") || AccumulatorWhitelist.W_GROW.contains(m));
        }
        for (String m : AccumulatorWhitelist.MUTATING_METHODS) {
            Assert.assertEquals(m, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.StringBuilder", m, UsageRole.RECEIVER));
        }
    }

    // ------------------------------------------------------------------
    // The runtime premise on the real builder classes.
    // ------------------------------------------------------------------
    private static final String BASE = "abcdef";

    /** A builder whose buffer the factory shares (6 of 8 Latin-1 bytes used: not under the trim threshold). */
    private static Object sharingBuilder(Class<?> c) {
        if (c == StringBuilder.class) {
            return new StringBuilder(8).append(BASE);
        }
        return new StringBuffer(8).append(BASE);
    }

    private static StringView view(Object sb) {
        return (StringView) (sb instanceof StringBuilder b ? StringView.create(b) : StringView.create((StringBuffer) sb));
    }

    private static String content(StringView v) {
        char[] out = new char[v.length()];
        for (int i = 0; i < out.length; i++) {
            out[i] = v.charAt(i);
        }
        return new String(out);
    }

    /**
     * The int arguments of one call, by position: distinct and non-trivial, so a misclassified
     * shrinking mutator really mutates (delete(1,2), deleteCharAt(1), setCharAt(1,_), setLength(1)); every growing /
     * read-only overload stays in bounds (append(char[],1,2), getChars(1,2,dst,3), insert-like (1,2,3) shapes).
     */
    private static final int[] INT_ARGS = {1, 2, 3};

    private static Object[] args(Method m) {
        Object[] args = new Object[m.getParameterCount()];
        int ints = 0;
        for (int i = 0; i < args.length; i++) {
            Class<?> t = m.getParameterTypes()[i];
            args[i] = t == int.class ? INT_ARGS[ints++] : arg(t);
        }
        return args;
    }

    private static Object arg(Class<?> t) {
        if (t == long.class) {
            return 7L;
        }
        if (t == char.class) {
            return 'q';
        }
        if (t == boolean.class) {
            return true;
        }
        if (t == float.class) {
            return 1.5f;
        }
        if (t == double.class) {
            return 2.5d;
        }
        if (t == char[].class) {
            return new char[]{'m', 'n', 'o', 'p', 'r', 's', 't', 'w'};
        }
        if (t == String.class || t == CharSequence.class || t == Object.class) {
            return "uvwx";
        }
        if (t == StringBuffer.class) {
            return new StringBuffer("sb");
        }
        if (t == StringBuilder.class) {
            return new StringBuilder("sb");
        }
        throw new AssertionError("no sample argument for " + t);
    }

    /**
     * Every public overload of every GROWING and READ_ONLY method (incl. appendCodePoint, repeat, trimToSize, indexOf,
     * compareTo, chars/codePoints with the stream consumed), on both builder classes: the view's content never changes.
     */
    @Test
    public void growingOverloadsKeepTheView() throws Exception {
        int checked = 0;
        for (Class<?> c : new Class<?>[]{StringBuilder.class, StringBuffer.class}) {
            for (Method m : c.getMethods()) {
                if (Modifier.isStatic(m.getModifiers()) || m.isBridge() || !AccumulatorWhitelist.W_GROW.contains(m.getName()) || m.getDeclaringClass() == Object.class) {
                    continue;
                }
                Object sb = sharingBuilder(c);
                StringView v = view(sb);
                Object r = m.invoke(sb, args(m));
                if (r instanceof java.util.stream.IntStream st) {
                    st.sum(); // run the lazy reader
                }
                // then grow in place, reallocate and inflate
                appendAll(sb, "x");
                appendAll(sb, "yyyyyyyyyyyyyyyyyyyy");
                appendAll(sb, "Āā");
                Assert.assertEquals(c.getSimpleName() + "." + m, BASE, content(v));
                checked++;
            }
        }
        Assert.assertTrue("overloads checked: " + checked, checked >= 50); // 57 non-bridge overloads on JDK 25
    }

    private static void appendAll(Object sb, String s) {
        if (sb instanceof StringBuilder b) {
            b.append(s);
        } else {
            ((StringBuffer) sb).append(s);
        }
    }

    /** The negative control: each rejected mutator changes a shared view (so the table must exclude it). */
    @Test
    public void mutatorsBreakTheView() {
        List<Consumer<StringBuilder>> ops = new ArrayList<>();
        ops.add(b -> {
            b.setLength(0);
            b.append("zz");
        });
        ops.add(b -> b.insert(0, 'X'));
        ops.add(b -> b.delete(0, 2));
        ops.add(b -> b.deleteCharAt(0));
        ops.add(b -> b.replace(0, 1, "Z"));
        ops.add(b -> b.reverse());
        ops.add(b -> b.setCharAt(0, 'Q'));
        for (int i = 0; i < ops.size(); i++) {
            StringBuilder sb = (StringBuilder) sharingBuilder(StringBuilder.class);
            StringView v = view(sb);
            ops.get(i).accept(sb);
            Assert.assertNotEquals("mutator #" + i, BASE, content(v));
        }
    }

    /**
     * The premise test's sample arguments are strong enough: every overload of each in-place mutator
     * that does not grow the builder (so writes into the shared array) changes the view with exactly the arguments
     * {@link #growingOverloadsKeepTheView} uses. Were one of them moved into W_GROW by mistake, that test would fail.
     */
    @Test
    public void sampleArgumentsMakeTheInPlaceMutatorsVisible() throws Exception {
        java.util.Set<String> covered = new java.util.TreeSet<>();
        for (Class<?> c : new Class<?>[]{StringBuilder.class, StringBuffer.class}) {
            for (Method m : c.getMethods()) {
                if (Modifier.isStatic(m.getModifiers()) || m.isBridge() ||
                                !List.of("delete", "deleteCharAt", "setCharAt", "setLength", "reverse").contains(m.getName())) {
                    continue;
                }
                Object sb = sharingBuilder(c);
                StringView v = view(sb);
                m.invoke(sb, args(m));
                appendAll(sb, "x"); // a shrink shows only after a later in-place append
                Assert.assertNotEquals(c.getSimpleName() + "." + m, BASE, content(v));
                covered.add(c.getSimpleName() + "." + m.getName());
            }
        }
        // StringBuilder inherits setCharAt/setLength from the package-private AbstractStringBuilder, which getMethods() does
        // not list here; StringBuffer overrides all five, so every name is covered with the same sample arguments
        Assert.assertEquals(new java.util.TreeSet<>(List.of("StringBuffer.delete", "StringBuffer.deleteCharAt", "StringBuffer.reverse", "StringBuffer.setCharAt",
                        "StringBuffer.setLength", "StringBuilder.delete", "StringBuilder.deleteCharAt", "StringBuilder.reverse")), covered);
    }

    /**
     * The decision table is keyed by name, so the non-public builder methods that share a W_GROW name
     * are pinned too (audited in labs-openjdk {@code AbstractStringBuilder.java}: {@code compareTo(ASB)} :172 reads,
     * {@code append(ASB)} :671 appends at {@code count}, {@code private repeat(char,int)} :2085 appends at {@code count};
     * {@code StringBuffer.append(ASB)} :348 is the synchronized {@code super.append(asb)}). A new one fails here until it is
     * audited.
     */
    @Test
    public void nonPublicSameNameMethodsAreAudited() throws ClassNotFoundException {
        java.util.Set<String> audited = java.util.Set.of(
                        "java.lang.AbstractStringBuilder.compareTo(java.lang.AbstractStringBuilder)",
                        "java.lang.AbstractStringBuilder.append(java.lang.AbstractStringBuilder)",
                        "java.lang.AbstractStringBuilder.repeat(char,int)",
                        "java.lang.StringBuffer.append(java.lang.AbstractStringBuilder)");
        java.util.Set<String> found = new java.util.TreeSet<>();
        for (String c : BUILDERS) {
            for (Method m : Class.forName(c).getDeclaredMethods()) {
                if (Modifier.isPublic(m.getModifiers()) || m.isSynthetic() || !AccumulatorWhitelist.W_GROW.contains(m.getName())) {
                    continue;
                }
                StringBuilder sig = new StringBuilder(c).append('.').append(m.getName()).append('(');
                for (int i = 0; i < m.getParameterCount(); i++) {
                    sig.append(i == 0 ? "" : ",").append(m.getParameterTypes()[i].getTypeName());
                }
                found.add(sig.append(')').toString());
            }
        }
        Assert.assertEquals(new java.util.TreeSet<>(audited), found);
    }

    /**
     * The factory's trim regime copies (a mostly-empty buffer): a view of such a builder never shares:
     * the copy is an exact {@code String} (the JDK's toString), not a StringView over a copy.
     */
    @Test
    public void underThresholdCopies() {
        StringBuilder sb = new StringBuilder(64).append(BASE);
        String v = StringView.create(sb);
        Assert.assertSame(String.class, v.getClass());
        sb.setLength(0);
        sb.append("zzzzzz");
        Assert.assertEquals(BASE, v);
    }
}
