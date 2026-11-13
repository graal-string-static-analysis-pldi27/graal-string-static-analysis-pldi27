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

import java.io.IOException;
import java.io.InputStream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.ThreeWayString;

/**
 * The five lazy reps ({@code value == null}) do not override {@code coder()} / {@code isLatin1()}: an override would
 * turn every String-typed call site of them into a virtual call image-wide. Inheriting them is sound because (i) every
 * lazy rep passes the exact coder of its content (the OR of its children's coders) to {@code super(coder)}, and (ii)
 * {@code String.coder()} / {@code String.isLatin1()} read only the inherited {@code coder} field, never the null
 * {@code value}. Pinned:
 * <ol>
 * <li>structurally: the builder JDK's {@code java.lang.String} bodies of {@code coder()} / {@code isLatin1()} touch no
 * field but {@code coder} and invoke no accessor of {@code value};</li>
 * <li>semantically: every lazy rep, built through its real factories with Latin-1, UTF-16, mixed and empty parts,
 * answers {@code coder()} / {@code isLatin1()} exactly as a plain {@code String} of the same content. The inherited body
 * runs on a receiver whose {@code value} is {@code null}, so any {@code value} read would throw.</li>
 * </ol>
 * The {@code coder()} side is also pinned by {@link RepInheritedBodyTest#EXPECTED_INHERITED} (W_lazy admits
 * {@code coder}); {@code isLatin1} is not in {@code LazyConcatWhitelist.SIGNATURES}, so it is pinned only here.
 */
public class LazyRepCoderSemanticsTest {

    static final List<Class<?>> LAZY_REPS = List.of(
                    RopeString.class, ThreeWayString.class, FixedConcat4.class,
                    ArrayLazyString.class, InterleavedStringArray.class);

    /**
     * Leg (i), structural: the String bodies of {@code coder()} and {@code isLatin1()} never read {@code value} and never
     * call {@code value()} / {@code valueRaw()}; the only instance field either touches is {@code coder}, and a
     * {@code getfield coder} must be present (the check is not vacuous).
     */
    @Test
    public void stringCoderAndIsLatin1BodiesNeverTouchValue() throws IOException {
        assertFieldOnlyBody("coder", "()B");
        assertFieldOnlyBody("isLatin1", "()Z");
    }

    static void assertFieldOnlyBody(String name, String descriptor) throws IOException {
        byte[] bytes;
        try (InputStream in = LazyRepCoderSemanticsTest.class.getResourceAsStream("/java/lang/String.class")) {
            Assert.assertNotNull("the class file of java.lang.String is readable", in);
            bytes = in.readAllBytes();
        }
        ClassModel cm = ClassFile.of().parse(bytes);
        for (MethodModel mm : cm.methods()) {
            if (!mm.methodName().stringValue().equals(name) || !mm.methodType().stringValue().equals(descriptor)) {
                continue;
            }
            CodeModel code = mm.code().orElse(null);
            Assert.assertNotNull("java.lang.String." + name + " has no code", code);
            boolean readsCoderField = false;
            for (CodeElement e : code) {
                if (e instanceof FieldInstruction fi) {
                    Assert.assertNotEquals("java.lang.String." + name + " must not touch the value field: " + fi,
                                    "value", fi.name().stringValue());
                    if (fi.opcode() == Opcode.GETFIELD) {
                        Assert.assertEquals("java.lang.String." + name + " reads only the coder instance field: " + fi,
                                        "coder", fi.name().stringValue());
                        readsCoderField = true;
                    }
                } else if (e instanceof InvokeInstruction ii) {
                    Assert.assertNotEquals("java.lang.String." + name + " must not call the value accessor: " + ii,
                                    "value", ii.name().stringValue());
                    Assert.assertNotEquals("java.lang.String." + name + " must not call the raw value accessor: " + ii,
                                    "valueRaw", ii.name().stringValue());
                }
            }
            Assert.assertTrue("java.lang.String." + name + " reads the coder field (the check is not vacuous)", readsCoderField);
            return;
        }
        Assert.fail("no method " + name + descriptor + " in java.lang.String");
    }

    /** The deletion itself: every lazy rep inherits both methods from {@code java.lang.String}. */
    @Test
    public void everyLazyRepInheritsCoderAndIsLatin1() throws NoSuchMethodException {
        for (Class<?> rep : LAZY_REPS) {
            Assert.assertSame(rep + " must inherit coder() (the override is removed, it forced vtable calls)",
                            String.class, RepInheritedBodyTest.implementingClass(rep, String.class.getDeclaredMethod("coder")));
            Assert.assertSame(rep + " must inherit isLatin1() (the override is removed, it forced vtable calls)",
                            String.class, RepInheritedBodyTest.implementingClass(rep, String.class.getDeclaredMethod("isLatin1")));
        }
    }

    /**
     * Leg (ii), semantic: for every lazy rep built through its real factories (the {@code create} statics and the hosted
     * {@link LazyConcatFactory} paths) with Latin-1, UTF-16, mixed and empty parts, {@code coder()} and
     * {@code isLatin1()} equal a plain String's of the same content.
     */
    @Test
    public void lazyRepCoderAndIsLatin1MatchTheFlatString() {
        String l1 = "abc";
        String utf = "a\u0100b";
        String empty = "";
        // rope
        check(l1 + l1, RopeString.create(l1, l1), "rope L1+L1");
        check(l1 + utf, RopeString.create(l1, utf), "rope L1+UTF16 (mixed)");
        check(utf + utf, RopeString.create(utf, utf), "rope UTF16+UTF16");
        check(empty + empty, RopeString.create(empty, empty), "rope empty+empty");
        check(l1 + l1, LazyConcatFactory.rope(l1, l1), "factory rope L1+L1");
        check(l1 + utf, LazyConcatFactory.rope(l1, utf), "factory rope L1+UTF16");
        // three-way
        check(l1 + empty + l1, ThreeWayString.create(l1, empty, l1), "three-way L1+empty+L1");
        check(utf + l1 + utf, ThreeWayString.create(utf, l1, utf), "three-way UTF16+L1+UTF16");
        check(l1 + empty + utf, LazyConcatFactory.threeWay(l1, empty, utf), "factory three-way mixed");
        // fixed4
        check(l1 + l1 + l1 + l1, FixedConcat4.create(l1, l1, l1, l1), "fixed4 L1*4");
        check(l1 + utf + empty + l1, FixedConcat4.create(l1, utf, empty, l1), "fixed4 mixed");
        check(utf + utf + utf + utf, FixedConcat4.create(utf, utf, utf, utf), "fixed4 UTF16*4");
        check(l1 + utf + l1 + utf, LazyConcatFactory.fixed4(l1, utf, l1, utf), "factory fixed4 mixed");
        // array-lazy
        check(String.join("", l1, l1), ArrayLazyString.create(new String[]{l1, l1}), "array-lazy L1");
        check(String.join("", l1, utf, empty), ArrayLazyString.create(new String[]{l1, utf, empty}), "array-lazy mixed");
        check(String.join("", utf, utf), ArrayLazyString.create(new String[]{utf, utf}), "array-lazy UTF16");
        check(String.join("", l1), ArrayLazyString.create(new String[]{l1}), "array-lazy single");
        check("", ArrayLazyString.create(new String[0]), "array-lazy empty array");
        check(String.join("", l1, utf), LazyConcatFactory.arrayLazy(new String[]{l1, utf}), "factory array-lazy mixed");
        // interleaved
        check(String.join(",", l1, l1), InterleavedStringArray.create(new String[]{l1, l1}, ","), "interleaved L1/,");
        check(String.join("\u0100", l1, l1), InterleavedStringArray.create(new String[]{l1, l1}, "\u0100"), "interleaved L1/UTF16-delim");
        check(String.join(",", utf, l1, empty), InterleavedStringArray.create(new String[]{utf, l1, empty}, ","), "interleaved UTF16 mixed");
        check(utf, InterleavedStringArray.create(new String[]{utf}, ","), "interleaved single (no delim)");
        check("", InterleavedStringArray.create(new String[0], ","), "interleaved empty elements");
        check(String.join(",", l1, utf), LazyConcatFactory.interleaved(new String[]{l1, utf}, ","), "factory interleaved mixed");
    }

    /** The content guard first (a mis-built rep must not pass vacuously), then the two answers. */
    static void check(String flat, String rep, String what) {
        RepEq.assertRepEquals(what + ": content", flat, rep.toString());
        Assert.assertEquals(what + ": coder()", flat.coder(), rep.coder());
        Assert.assertEquals(what + ": isLatin1()", flat.isLatin1(), rep.isLatin1());
    }

    /** The test's own non-vacuity: the fixtures really span both coders on this JVM. */
    @Test
    public void theFixturesSpanBothCoders() throws NoSuchMethodException {
        Method coder = String.class.getDeclaredMethod("coder");
        Assert.assertTrue("java.lang.String.coder() must be the public accessor the reps inherit", Modifier.isPublic(coder.getModifiers()));
        Assert.assertEquals(0, "abc".coder());
        Assert.assertEquals(1, "a\u0100b".coder());
        Assert.assertTrue("abc".isLatin1());
        Assert.assertFalse("a\u0100b".isLatin1());
    }

    /**
     * A factory rope with an empty side and a plain other side is a new plain String (the JDK
     * simpleConcat rule: equal content, never the operand itself); with a rep or empty-rep other side it stays a rope.
     */
    @Test
    public void ropeEmptySideIsANewPlainString() {
        String s = new String("abc");
        String utf = new String("a\u0100b");
        String empty = new String("");
        for (String[] ab : new String[][]{{empty, s}, {s, empty}, {"", utf}, {utf, ""}, {empty, empty}}) {
            String r = LazyConcatFactory.rope(ab[0], ab[1]);
            Assert.assertSame("plain String", String.class, r.getClass());
            Assert.assertNotSame("not the left operand", ab[0], r);
            Assert.assertNotSame("not the right operand", ab[1], r);
            check(ab[0] + ab[1], r, "rope-empty " + ab[0].length() + "/" + ab[1].length());
            Assert.assertEquals((ab[0] + ab[1]).hashCode(), r.hashCode());
        }
        String rep = RopeString.create("x", "y");
        Assert.assertSame(RopeString.class, LazyConcatFactory.rope("", rep).getClass());
        Assert.assertSame(RopeString.class, LazyConcatFactory.rope(rep, "").getClass());
        check("xy", LazyConcatFactory.rope("", rep), "rope-empty rep right");
        Assert.assertSame(RopeString.class, LazyConcatFactory.rope("a", "b").getClass());
    }

    /** createOwned keeps the caller's array (no copy), create copies; one null check. */
    @Test
    public void createOwnedDoesNotCopy() throws Exception {
        java.lang.reflect.Field f = ArrayLazyString.class.getDeclaredField("parts");
        f.setAccessible(true);
        String[] mine = {"a", "b", "c"};
        Assert.assertSame("createOwned takes the array", mine, f.get(ArrayLazyString.createOwned(mine)));
        Assert.assertNotSame("create copies", mine, f.get(ArrayLazyString.create(mine)));
        Assert.assertSame("factory arrayLazy hands over", mine, f.get(LazyConcatFactory.arrayLazy(mine)));
        check("abc", ArrayLazyString.createOwned(mine), "createOwned content");
        Assert.assertThrows(NullPointerException.class, () -> ArrayLazyString.createOwned(new String[]{"a", null}));
        Assert.assertThrows(NullPointerException.class, () -> ArrayLazyString.create(new String[]{"a", null}));
        java.lang.reflect.Field e = InterleavedStringArray.class.getDeclaredField("elements");
        e.setAccessible(true);
        String[] mine2 = {"a", "b"};
        Assert.assertSame("factory interleaved hands over", mine2, e.get(LazyConcatFactory.interleaved(mine2, ",")));
    }

    /** Every typed converter equals the JDK string conversion (String.valueOf) on edge values. */
    @Test
    public void typedConvertersEqualTheJdkConversion() {
        for (int i : new int[]{0, -1, 7, 127, -128, 4711, Integer.MIN_VALUE, Integer.MAX_VALUE, (byte) -128, (short) -32768}) {
            Assert.assertEquals(String.valueOf(i), LazyConcatFactory.str(i));
        }
        for (long l : new long[]{0L, Long.MIN_VALUE, Long.MAX_VALUE, -4711L}) {
            Assert.assertEquals(String.valueOf(l), LazyConcatFactory.str(l));
        }
        for (char c : new char[]{'a', '\u0000', '\u0100', '\uffff', '\ud800'}) {
            Assert.assertEquals(String.valueOf(c), LazyConcatFactory.str(c));
            Assert.assertEquals(String.valueOf(c).coder(), LazyConcatFactory.str(c).coder());
        }
        Assert.assertEquals("true", LazyConcatFactory.str(true));
        Assert.assertEquals("false", LazyConcatFactory.str(false));
        for (float f : new float[]{-0.0f, 0.0f, Float.NaN, Float.MIN_VALUE, Float.POSITIVE_INFINITY, 1.1f}) {
            Assert.assertEquals(String.valueOf(f), LazyConcatFactory.str(f));
        }
        for (double d : new double[]{-0.0, Double.NaN, Double.MAX_VALUE, Double.NEGATIVE_INFINITY, 1e-300}) {
            Assert.assertEquals(String.valueOf(d), LazyConcatFactory.str(d));
        }
        Assert.assertEquals("null", LazyConcatFactory.str((String) null));
        Assert.assertEquals("null", LazyConcatFactory.str((Object) null));
        Assert.assertEquals("null", LazyConcatFactory.str((Object) (Integer) null));
        String s = new String("x");
        Assert.assertSame("a String operand is itself", s, LazyConcatFactory.str(s));
        Assert.assertEquals("4711", LazyConcatFactory.str((Object) Integer.valueOf(4711)));
    }

    /**
     * The Object converter is the JDK's {@code StringConcatHelper.stringOf(Object)}, checked
     * against the JDK's own Object-typed indy concat (what javac 9-18 emits): a {@code toString()} that returns null
     * gives "null", {@code toString()} runs exactly once, and an exception from it reaches the caller.
     */
    @Test
    public void objectConverterIsTheJdkStringOf() throws Throwable {
        Object nullToString = new Object() {
            @Override
            public String toString() {
                return null;
            }
        };
        java.lang.invoke.MethodHandle jdk = java.lang.invoke.StringConcatFactory.makeConcatWithConstants(java.lang.invoke.MethodHandles.lookup(), "concat",
                        java.lang.invoke.MethodType.methodType(String.class, Object.class), "\u0001").dynamicInvoker();
        Assert.assertEquals("premise: the JDK's Object-operand concat", "null", (String) jdk.invoke(nullToString));
        Assert.assertEquals("null", LazyConcatFactory.str(nullToString));
        // the parent resolves the converter of every non-String reference operand type to str(Object)
        for (Class<?> type : new Class<?>[]{Object.class, Runnable.class, Integer.class, CharSequence.class, StringBuilder.class}) {
            Assert.assertEquals(type.getName(), LazyConcatFactory.class.getDeclaredMethod("str", Object.class), LazyConcatMint.converterMethod(type));
        }
        int[] calls = {0};
        Object counting = new Object() {
            @Override
            public String toString() {
                calls[0]++;
                return "c" + calls[0];
            }
        };
        Assert.assertEquals("c1", LazyConcatFactory.str(counting));
        Assert.assertEquals("toString exactly once", 1, calls[0]);
        Assert.assertEquals("premise: the JDK calls it once too", "c2", (String) jdk.invoke(counting));
        Object throwing = new Object() {
            @Override
            public String toString() {
                throw new IllegalStateException("boom");
            }
        };
        try {
            LazyConcatFactory.str(throwing);
            Assert.fail("toString's exception must reach the caller");
        } catch (IllegalStateException e) {
            Assert.assertEquals("boom", e.getMessage());
        }
    }
}
