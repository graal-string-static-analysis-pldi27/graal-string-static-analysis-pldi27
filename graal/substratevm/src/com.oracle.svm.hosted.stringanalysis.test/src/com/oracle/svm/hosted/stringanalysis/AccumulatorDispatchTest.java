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
import java.io.Writer;
import java.lang.reflect.Method;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * A call whose receiver is the tracked accumulator is recorded and classified as the accumulator's own method, whatever
 * the declared owner (CharSequence, Appendable, Object, Writer): the dispatched owner is the declaring class of the
 * declaration the JVM selects on the accumulator's exact class
 * ({@link TerminalBodyKinds#selectedDeclaration}), and the pass-1 tables classify the usage by it. A wider-owner site is
 * labelled by Phase A with String's name ({@code java.lang.String.toString()}), a label pass 1 rejects on.
 */
public class AccumulatorDispatchTest {

    /** Phase A's label of a wider-owner call (what the site's declared owner reads as). */
    private static final String PHASE_A = "java.lang.String";

    private static final List<Class<?>> ACCS = List.of(StringBuilder.class, StringBuffer.class, StringWriter.class);

    private static Method m(Class<?> c, String name, Class<?>... params) {
        try {
            return c.getMethod(name, params);
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
    }

    private static String owner(Class<?> exact, Method declared) {
        return AccumulatorWhitelist.dispatchedOwner(PHASE_A, exact, declared);
    }

    private static AccumulatorWhitelist.AccRow row(Class<?> exact, Method declared) {
        String o = AccumulatorWhitelist.classifyingOwner(PHASE_A, owner(exact, declared));
        return AccumulatorWhitelist.accumulatorUsageRow(o, declared.getName(), UsageRole.RECEIVER);
    }

    private static void expect(Class<?> exact, Method declared, String owner, AccumulatorWhitelist.AccRow r) {
        String what = exact.getSimpleName() + " via " + declared.getDeclaringClass().getSimpleName() + "." + declared.getName();
        Assert.assertEquals(what + " owner", owner, owner(exact, declared));
        Assert.assertEquals(what + " row", r, row(exact, declared));
    }

    @Test
    public void charSequenceCallsAreTheBuildersOwn() {
        for (Class<?> b : List.of(StringBuilder.class, StringBuffer.class)) {
            String n = b.getName();
            expect(b, m(CharSequence.class, "toString"), n, AccumulatorWhitelist.AccRow.GROWING);
            expect(b, m(CharSequence.class, "length"), n, AccumulatorWhitelist.AccRow.GROWING);
            expect(b, m(CharSequence.class, "charAt", int.class), n, AccumulatorWhitelist.AccRow.GROWING);
            expect(b, m(CharSequence.class, "subSequence", int.class, int.class), n, AccumulatorWhitelist.AccRow.GROWING);
            expect(b, m(CharSequence.class, "chars"), n, AccumulatorWhitelist.AccRow.GROWING);
            // the interface default method no class of the builder declares: named by its own class, which no table admits
            expect(b, m(CharSequence.class, "isEmpty"), "java.lang.CharSequence", AccumulatorWhitelist.AccRow.REJECT);
            // Object methods through the interface (javac: invokeinterface CharSequence.hashCode, resolved to Object's)
            expect(b, m(Object.class, "hashCode"), "java.lang.Object", AccumulatorWhitelist.AccRow.READ);
            expect(b, m(Object.class, "equals", Object.class), "java.lang.Object", AccumulatorWhitelist.AccRow.READ);
            Assert.assertTrue("the CharSequence toString on " + n + " is a seedable extraction",
                            AccumulatorWhitelist.isSeedableExtraction(owner(b, m(CharSequence.class, "toString")), "toString", ""));
        }
    }

    @Test
    public void appendableCallsAreGrowing() {
        for (Class<?> a : ACCS) {
            for (Method d : List.of(m(Appendable.class, "append", CharSequence.class), m(Appendable.class, "append", char.class),
                            m(Appendable.class, "append", CharSequence.class, int.class, int.class))) {
                expect(a, d, a.getName(), AccumulatorWhitelist.AccRow.GROWING); // the covariant bridges are selected
            }
            Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction(owner(a, m(Object.class, "toString")), "toString", ""));
        }
    }

    @Test
    public void objectCallsAreTheAccumulatorsOwn() {
        for (Class<?> a : ACCS) {
            expect(a, m(Object.class, "toString"), a.getName(), AccumulatorWhitelist.AccRow.GROWING);
            expect(a, m(Object.class, "hashCode"), "java.lang.Object", AccumulatorWhitelist.AccRow.READ);
            expect(a, m(Object.class, "getClass"), "java.lang.Object", AccumulatorWhitelist.AccRow.READ);
            expect(a, m(Object.class, "equals", Object.class), "java.lang.Object", AccumulatorWhitelist.AccRow.READ);
        }
    }

    @Test
    public void writerCallsAreTheStringWritersOwn() {
        Class<?> w = StringWriter.class;
        String n = w.getName();
        expect(w, m(Writer.class, "write", String.class), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "write", int.class), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "write", char[].class, int.class, int.class), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "write", String.class, int.class, int.class), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "append", char.class), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "flush"), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "close"), n, AccumulatorWhitelist.AccRow.GROWING);
        expect(w, m(Writer.class, "toString"), n, AccumulatorWhitelist.AccRow.GROWING); // Object.toString (Writer declares none)
        // the inherited, non-overridden Writer.write(char[]): Writer's own body (entered by the walk, never a terminal usage)
        expect(w, m(Writer.class, "write", char[].class), "java.io.Writer", AccumulatorWhitelist.AccRow.REJECT);
    }

    @Test
    public void mutatingAndEscapingStayRejected() {
        // a cast back to the accumulator class names a table class: no dispatch, the table rejects as before
        for (String site : List.of("java.lang.StringBuilder", "java.lang.StringBuffer", "java.lang.AbstractStringBuilder", "java.io.StringWriter")) {
            Assert.assertNull(site, AccumulatorWhitelist.dispatchedOwner(site, StringBuilder.class, m(Object.class, "toString")));
        }
        for (String mut : AccumulatorWhitelist.MUTATING_METHODS) {
            Assert.assertEquals(mut, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.StringBuilder", mut, UsageRole.RECEIVER));
            Assert.assertEquals(mut, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.StringBuffer", mut, UsageRole.RECEIVER));
        }
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.io.StringWriter", "getBuffer", UsageRole.RECEIVER));
        // every public method of the builders, reached through Object/CharSequence/Appendable with its own descriptor: the
        // dispatched row equals the row of the builder-declared site (dispatch never widens the tables)
        for (Class<?> b : List.of(StringBuilder.class, StringBuffer.class)) {
            for (Method d : b.getMethods()) {
                if (java.lang.reflect.Modifier.isStatic(d.getModifiers())) {
                    continue;
                }
                String o = owner(b, d);
                Assert.assertNotNull(d.toString(), o);
                AccumulatorWhitelist.AccRow viaDispatch = AccumulatorWhitelist.accumulatorUsageRow(o, d.getName(), UsageRole.RECEIVER);
                AccumulatorWhitelist.AccRow direct = AccumulatorWhitelist.accumulatorUsageRow(b.getName(), d.getName(), UsageRole.RECEIVER);
                if (AccumulatorWhitelist.BUILDER_DECLARING.contains(o)) {
                    Assert.assertEquals(d.toString(), direct, viaDispatch);
                } else {
                    Assert.assertNotEquals("a non-builder owner is never GROWING: " + d, AccumulatorWhitelist.AccRow.GROWING, viaDispatch);
                }
            }
        }
    }

    @Test
    public void mixedClassesAndKnob() {
        Method ts = m(CharSequence.class, "toString");
        String a = owner(StringBuilder.class, ts);
        String b = owner(StringBuffer.class, ts);
        Assert.assertNotEquals(a, b);
        // the receivers of one site from two accumulator classes: no single exact class (the extraction REJECTs)
        Assert.assertNull(AccumulatorHeuristic.exactClassOf(List.of(StringBuilder.class.getName(), StringBuffer.class.getName())));
        // without a dispatched owner the usage is classified by the Phase-A label: a REJECT
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT,
                        AccumulatorWhitelist.accumulatorUsageRow(AccumulatorWhitelist.classifyingOwner(PHASE_A, null), "toString", UsageRole.RECEIVER));
    }
}
