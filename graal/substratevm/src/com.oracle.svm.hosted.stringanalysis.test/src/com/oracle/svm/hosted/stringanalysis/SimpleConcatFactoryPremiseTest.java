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

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.invoke.StringConcatFactory;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * A premise test tying {@link StringAtoms#scfCopiesOperand} (the hand-maintained mirror of
 * {@code StringConcatFactory.makeSimpleConcat}) to the real factory of the running (builder) JDK. A test of the mirror's
 * own outputs alone ({@code MapKeyConcatTest.scfCopyTestMirrorsMakeSimpleConcat}) misses a builder-JDK change that
 * makes some recipe copy its operand: a StringView operand would then ADMIT at an {@code "" + v} site and the image
 * would NPE.
 * <p>
 * Oracle: for a table of (bootstrap, recipe, constants, dynamic MethodType) the test links the real public bootstrap
 * ({@code makeConcatWithConstants} / {@code makeConcat}) on this JVM (mx unittest runs on the builder JDK), invokes the
 * handle with a {@link StringView} operand ({@code value() == null}, every read of the non-copying strategies
 * overridden), and observes the strategy directly: a copy of the operand reads {@code original.value()} and NPEs. A
 * "may copy at run time" strategy (two-reference {@code simpleConcat}, which copies the other operand when one side is
 * empty) is observed over both empty-side assignments. For every exact row the mirror's classification must equal the
 * observed behaviour, and every non-copying invocation must produce the exact expected string (the non-copying
 * strategies read only methods a custom rep supports). For the conservative rows (a {@code \2} recipe tag) only the
 * soundness direction is asserted: JDK copies ⇒ mirror says copying.
 */
public class SimpleConcatFactoryPremiseTest {

    /** The probe: a real value()-null custom rep over "ell" (every read the strategies make is overridden). */
    private static final StringView PROBE = (StringView) StringView.create("hello", 1, 4);

    /** One row of the strategy table: what the analysis sees, and the run the real factory must produce. */
    private static final class Row {
        final String label;
        final String boot;          // the bootstrap name the recogniser passes to scfCopiesOperand
        final String recipe;        // null = makeConcat (its mocked \1-per-argument recipe)
        final Object[] constants;   // makeConcatWithConstants static constants
        final MethodType mt;        // the indy's dynamic method type
        final Object[][] argSets;   // the invocations (a PROBE wherever an operand may be copied)
        final String[] results;     // per argSet: the exact expected result, or null = NPE (a copy read)
        final boolean mirror;       // StringAtoms.scfCopiesOperand's classification of the same inputs
        final boolean conservative; // true: the mirror may say "copies" where the JDK does not (assert oracle ⇒ mirror only)

        Row(String label, String boot, String recipe, Object[] constants, MethodType mt, Object[][] argSets, String[] results, boolean mirror, boolean conservative) {
            this.label = label;
            this.boot = boot;
            this.recipe = recipe;
            this.constants = constants;
            this.mt = mt;
            this.argSets = argSets;
            this.results = results;
            this.mirror = mirror;
            this.conservative = conservative;
        }
    }

    private static final String W = "makeConcatWithConstants";

    private static final Row[] ROWS = new Row[]{
                    // the copying simple strategies (newStringOf; simpleConcat's may-copy on the empty side)
                    new Row("unary \"\"+v: newStringOf", W, "\u0001", new Object[0], MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{null}, true, false),
                    new Row("unary \"\"+o (non-String ref): also newStringOf", W, "\u0001", new Object[0], MethodType.methodType(String.class, Object.class),
                                    new Object[][]{{PROBE}}, new String[]{null}, true, false),
                    new Row("two refs a+b: simpleConcat, copies when the other side is empty", W, "\u0001\u0001", new Object[0],
                                    MethodType.methodType(String.class, String.class, String.class),
                                    new Object[][]{{PROBE, "abc0"}, {"", PROBE}, {PROBE, ""}}, new String[]{"ellabc0", null, null}, true, false),
                    new Row("makeConcat, one reference", "makeConcat", null, new Object[0], MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{null}, true, false),
                    new Row("makeConcat, two references", "makeConcat", null, new Object[0], MethodType.methodType(String.class, String.class, String.class),
                                    new Object[][]{{PROBE, "x"}, {"", PROBE}}, new String[]{"ellx", null}, true, false),
                    // the non-copying strategies (valueOf for primitives; simpleConcat with a non-empty constant; the hidden class)
                    new Row("unary \"\"+i: String.valueOf", W, "\u0001", new Object[0], MethodType.methodType(String.class, int.class),
                                    new Object[][]{{7}}, new String[]{"7"}, false, false),
                    new Row("unary \"\"+J: String.valueOf", W, "\u0001", new Object[0], MethodType.methodType(String.class, long.class),
                                    new Object[][]{{7L}}, new String[]{"7"}, false, false),
                    new Row("suffix v+\"!\": simpleConcat with a constant", W, "\u0001!", new Object[0], MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{"ell!"}, false, false),
                    new Row("prefix \"<\"+v: simpleConcat with a constant", W, "<\u0001", new Object[0], MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{"<ell"}, false, false),
                    new Row("both constants \"<\"+v+\">\": the 1-arg hidden class", W, "<\u0001>", new Object[0], MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{"<ell>"}, false, false),
                    new Row("two refs with an inner constant: the hidden class", W, "\u0001-\u0001", new Object[0], MethodType.methodType(String.class, String.class, String.class),
                                    new Object[][]{{PROBE, "def"}}, new String[]{"ell-def"}, false, false),
                    new Row("a primitive operand: the hidden class", W, "\u0001\u0001", new Object[0], MethodType.methodType(String.class, String.class, int.class),
                                    new Object[][]{{PROBE, 7}}, new String[]{"ell7"}, false, false),
                    new Row("three references: the hidden class", W, "\u0001\u0001\u0001", new Object[0],
                                    MethodType.methodType(String.class, String.class, String.class, String.class),
                                    new Object[][]{{PROBE, "b", "c"}}, new String[]{"ellbc"}, false, false),
                    new Row("makeConcat, three references: the hidden class", "makeConcat", null, new Object[0],
                                    MethodType.methodType(String.class, String.class, String.class, String.class),
                                    new Object[][]{{PROBE, "x", "y"}}, new String[]{"ellxy"}, false, false),
                    new Row("constants only (n=0): no dynamic operand", W, "ab", new Object[0], MethodType.methodType(String.class),
                                    new Object[][]{{}}, new String[]{"ab"}, false, false),
                    // the mirror's documented conservative row: the JDK folds the \2 constant into a non-copying strategy
                    new Row("a \\2 constant: JDK non-copying, mirror conservative", W, "\u0002\u0001", new Object[]{"X"},
                                    MethodType.methodType(String.class, String.class),
                                    new Object[][]{{PROBE}}, new String[]{"Xell"}, true, true)};

    /** Links the real public bootstrap for {@code r} on this JVM (the strategy choice happens here, at link time). */
    private static MethodHandle link(Row r) throws Throwable {
        if ("makeConcat".equals(r.boot)) {
            return StringConcatFactory.makeConcat(MethodHandles.lookup(), "c93probe", r.mt).dynamicInvoker();
        }
        return StringConcatFactory.makeConcatWithConstants(MethodHandles.lookup(), "c93probe", r.mt, r.recipe, r.constants).dynamicInvoker();
    }

    /**
     * Invokes every argSet of {@code r}: each invocation must produce its exact expected result (null = the copy broke
     * it). The copy is observed as either the strategy's own read throwing NPE (the interpreted/JIT-dependent form) or
     * the returned String being broken ({@code value() == null}: the copy ctor ran {@code new String(probe)} and

     * inherited the null value). A broken result is never touched with String methods afterwards — a C2-compiled
     * {@code String.equals} trusts {@code String.value} non-null and would SEGV the JVM, not throw.
     */
    private static boolean jdkCopies(Row r) throws Throwable {
        MethodHandle mh = link(r);
        boolean anyCopy = false;
        for (int i = 0; i < r.argSets.length; i++) {
            Object got;
            try {
                got = mh.invokeWithArguments(java.util.Arrays.asList(r.argSets[i]));
            } catch (NullPointerException e) {
                anyCopy = true;
                Assert.assertNull(r.label + " argSet " + i + ": an unexpected NPE (expected [" + r.results[i] + "])", r.results[i]);
                continue;
            }
            if (((String) got).value() == null) {
                anyCopy = true;
                Assert.assertNull(r.label + " argSet " + i + ": the copy produced a broken (value=null) result where [" + r.results[i] + "] was expected",
                                r.results[i]);
                continue;
            }
            Assert.assertEquals(r.label + " argSet " + i + ": the result must be exact (a non-copying strategy reads only rep-supported methods)",
                            r.results[i], got);
        }
        return anyCopy;
    }

    private static boolean mirror(Row r) {
        boolean[] primitive = new boolean[r.mt.parameterCount()];
        for (int i = 0; i < primitive.length; i++) {
            primitive[i] = r.mt.parameterType(i).isPrimitive();
        }
        return StringAtoms.scfCopiesOperand(r.boot, r.recipe, primitive);
    }

    @Test
    public void probeIsAValueNullRep() {
        Assert.assertNull("the oracle's premise: a custom rep's value() is null", PROBE.value());
        Assert.assertEquals(3, PROBE.length());
        Assert.assertEquals('e', PROBE.charAt(0));
    }

    /** The premise: on every row the mirror agrees with the real factory's strategy (conservative rows: oracle ⇒ mirror). */
    @Test
    public void scfCopiesOperandAgreesWithTheRealFactory() throws Throwable {
        for (Row r : ROWS) {
            boolean jdk = jdkCopies(r);
            boolean mirror = mirror(r);
            if (r.conservative) {
                Assert.assertFalse(r.label + ": UNSOUND — the JDK copies an operand but the mirror says non-copying", jdk && !mirror);
            } else {
                Assert.assertEquals(r.label + ": the mirror diverges from the real StringConcatFactory strategy", mirror, jdk);
            }
        }
    }
}
