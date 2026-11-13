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

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Function;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

/**
 * The flat-kind premise. A flat (value-carrying) rep may run any inherited {@code java.lang.String} body (it has no
 * admission whitelist), and the IC sends it to the direct {@code String.<m>} else wherever it does not override
 * {@code m}. The walk also enters the inherited bodies that hand {@code this} to walked code
 * ({@code StringTerminalHandList.FLAT_HANDOFF_NAMES}), so downstream sites list the flat kind instead of relying on this
 * premise; it remains the rep class's own correctness guarantee. A flat rep must behave exactly like a plain String with
 * the same content: (1) its inherited state is a plain String's ({@code value()} and {@code coder()} equal, so every
 * inherited body computes the same), and (2) every String method it overrides (the JVM's selection,
 * {@link TerminalBodyKinds#selectedDeclaration}) returns/throws exactly what String's own body does.
 * <p>
 * Automatic coverage: the flat reps are derived ({@link InlineCacheRegistry#isValueCarryingFlatRep}, a class-file
 * criterion) over every rep class ({@link RepPinSupport#repClasses()}), their instances come from
 * {@link RepEqualsMatrixTest#MAKERS} (a maker per rep is enforced there), the overridden methods are enumerated by
 * reflection, and the arguments are generated per parameter type: a new override whose parameter type has no generator
 * fails {@link #everyFlatOverrideIsContentEquivalent} until one is added here.
 */
public class FlatRepPremiseTest {

    /** The derived partition is the pinned one (flat = SBS + TrivialString; value-null = VALUE_NULL_REPS). */
    @Test
    public void flatPartitionIsDerivedFromTheConstructors() {
        Set<String> flat = new TreeSet<>();
        Set<String> valueNull = new TreeSet<>();
        for (Class<?> rep : RepPinSupport.repClasses()) {
            (InlineCacheRegistry.isValueCarryingFlatRep(rep) ? flat : valueNull).add(rep.getSimpleName());
        }
        Assert.assertEquals(Set.of("SingleByteString", "TrivialString"), flat);
        Set<String> expectedNull = new TreeSet<>();
        for (Class<?> c : RepInheritedBodyTest.VALUE_NULL_REPS) {
            expectedNull.add(c.getSimpleName());
        }
        Assert.assertEquals(expectedNull, valueNull);
        Assert.assertFalse("String itself is not a rep", InlineCacheRegistry.isValueCarryingFlatRep(String.class));
    }

    /** Positive control: the class-file criterion agrees with the instances (value() null exactly on value-null reps). */
    @Test
    public void flatCriterionMatchesTheInstances() {
        int seen = 0;
        for (Class<?> rep : RepPinSupport.repClasses()) {
            for (String s : instancesOf(rep, CONTENTS)) {
                seen++;
                boolean flat = InlineCacheRegistry.isValueCarryingFlatRep(rep);
                Assert.assertEquals(rep.getSimpleName() + "[" + s.length() + "] value() non-null iff flat", flat, s.value() != null);
            }
        }
        Assert.assertTrue(seen > 100);
    }

    /** Contents for the flat reps: every 1-char value of a byte (Latin-1 and the UTF-16 sign-extended range), plus a few others. */
    static final List<String> CONTENTS = new ArrayList<>();

    static {
        for (int c = 0; c <= 0x17F; c++) {
            CONTENTS.add(String.valueOf((char) c));
        }
        for (int c = 0xFF80; c <= 0xFFFF; c++) {
            CONTENTS.add(String.valueOf((char) c));
        }
        CONTENTS.addAll(List.of("", "ab", "€", "a€"));
    }

    static List<String> instancesOf(Class<?> rep, List<String> contents) {
        Function<String, List<String>> maker = RepEqualsMatrixTest.MAKERS.get(rep);
        Assert.assertNotNull("a maker for " + rep, maker);
        List<String> out = new ArrayList<>();
        for (String c : contents) {
            for (String s : maker.apply(new String(c.toCharArray()))) {
                if (c.isEmpty()) { // a rep is never empty; the empty content is a plain String
                    Assert.assertSame(String.class, s.getClass());
                    continue;
                }
                Assert.assertSame(rep, s.getClass());
                out.add(s);
            }
        }
        return out;
    }

    /** (1) The inherited state: value() and coder() of a flat rep are exactly the plain String's. */
    @Test
    public void flatRepsCarryThePlainState() {
        int n = 0;
        for (Class<?> rep : flatReps()) {
            for (String s : instancesOf(rep, CONTENTS)) {
                String plain = RepEqualsMatrixTest.contentOf(s);
                Assert.assertArrayEquals(rep.getSimpleName() + " value of [" + plain + "]", plain.value(), s.value());
                Assert.assertEquals(rep.getSimpleName() + " coder of [" + plain + "]", plain.coder(), s.coder());
                n++;
            }
        }
        Assert.assertTrue("non-vacuous: " + n, n >= 256 + 128);
    }

    static List<Class<?>> flatReps() {
        List<Class<?>> out = new ArrayList<>();
        for (Class<?> rep : RepPinSupport.repClasses()) {
            if (InlineCacheRegistry.isValueCarryingFlatRep(rep)) {
                out.add(rep);
            }
        }
        return out;
    }

    /** Every String instance method {@code rep} overrides (JVM selection: the selected declaration is not String's). */
    static List<Method> overriddenStringMethods(Class<?> rep) {
        List<Method> out = new ArrayList<>();
        for (Method m : String.class.getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers())) {
                continue;
            }
            Method d = TerminalBodyKinds.selectedDeclaration(rep, m);
            if (d != null && d.getDeclaringClass() != String.class) {
                out.add(m);
            }
        }
        out.sort((a, b) -> TerminalBodyKinds.nameAndDescriptor(a).compareTo(TerminalBodyKinds.nameAndDescriptor(b)));
        return out;
    }

    /** The argument values per parameter type; null = no generator (the test fails, naming the method). */
    static List<Object> argumentsOf(Class<?> t, List<String> stringArgs) {
        if (t == int.class) {
            return List.of(Integer.MIN_VALUE, -1, 0, 1, 2, Integer.MAX_VALUE); // MIN/MAX (offsetByCodePoints overflow)
        }
        if (t == char.class) {
            return List.of('a', 'A', 'i', 'I', 'ß', 'é', '€');
        }
        if (t == Locale.class) {
            return Arrays.asList(Locale.ROOT, Locale.ENGLISH, Locale.forLanguageTag("tr"), Locale.forLanguageTag("az"), Locale.forLanguageTag("lt"),
                            Locale.forLanguageTag("el"), null);
        }
        if (t == Object.class || t == String.class || t == CharSequence.class) {
            List<Object> out = new ArrayList<>(stringArgs);
            out.add(null);
            if (t == Object.class) {
                out.add(new Object());
                out.add(Integer.valueOf(97));
            }
            if (t == CharSequence.class) {
                out.add(new StringBuilder("a"));
            }
            return out;
        }
        return null;
    }

    /** String-typed arguments of every kind: plain, flat and value-null reps, for short contents. */
    static List<String> stringArguments() {
        List<String> out = new ArrayList<>();
        List<String> contents = List.of("", "a", "A", "b", "é", "ÿ", "€", "ab", "a€");
        for (String c : contents) {
            out.add(new String(c.toCharArray()));
        }
        for (Class<?> rep : List.of(SingleByteString.class, com.oracle.svm.core.stringrep.TrivialString.class, StringView.class, RopeString.class, ThreeWayString.class,
                        FixedConcat4.class, ArrayLazyString.class, InterleavedStringArray.class)) {
            List<String> made = instancesOf(rep, contents);
            out.addAll(made.subList(0, Math.min(made.size(), 12)));
        }
        return out;
    }

    record Outcome(String kind, Object value) {
    }

    /** The comparable outcome of a call: a thrown exception (class + message), or the result (String by content, plus "is the receiver"). */
    static Outcome outcome(Method m, Object receiver, Object[] args) {
        try {
            Object r = m.invoke(receiver, args);
            if (r instanceof String s) {
                return new Outcome(r == receiver ? "this" : "string", RepEqualsMatrixTest.contentOf(s));
            }
            if (r != null && r.getClass().isArray()) {
                return new Outcome("array", Arrays.deepToString(new Object[]{r}));
            }
            return new Outcome("value", r);
        } catch (InvocationTargetException e) {
            Throwable t = e.getCause();
            return new Outcome("throws", t.getClass().getName() + ": " + t.getMessage());
        } catch (IllegalAccessException e) {
            throw new AssertionError(m + ": " + e);
        }
    }

    /**
     * (2) Every flat rep × every String method it overrides × every receiver content (all 1-byte values, Latin-1 and
     * UTF-16) × the generated arguments, under three default locales (the no-arg case mappings read it): the rep's
     * outcome equals the plain String's of the same content.
     */
    @Test
    public void everyFlatOverrideIsContentEquivalent() {
        List<String> stringArgs = stringArguments();
        Map<String, Integer> cellsPerMethod = new TreeMap<>();
        List<String> wrong = new ArrayList<>();
        List<String> noGenerator = new ArrayList<>();
        Locale saved = Locale.getDefault();
        try {
            for (Locale dflt : List.of(Locale.ROOT, Locale.forLanguageTag("tr"), Locale.forLanguageTag("lt"))) {
                Locale.setDefault(dflt);
                for (Class<?> rep : flatReps()) {
                    List<Method> overridden = overriddenStringMethods(rep);
                    Assert.assertFalse(rep + " overrides something (non-vacuous)", overridden.isEmpty());
                    for (Method m : overridden) {
                        m.setAccessible(true);
                        List<List<Object>> argLists = new ArrayList<>();
                        argLists.add(new ArrayList<>());
                        for (Class<?> p : m.getParameterTypes()) {
                            List<Object> vals = argumentsOf(p, stringArgs);
                            if (vals == null) {
                                noGenerator.add(rep.getSimpleName() + "." + TerminalBodyKinds.nameAndDescriptor(m) + " param " + p.getName());
                                argLists.clear();
                                break;
                            }
                            List<List<Object>> next = new ArrayList<>();
                            for (List<Object> prefix : argLists) {
                                for (Object v : vals) {
                                    List<Object> l = new ArrayList<>(prefix);
                                    l.add(v);
                                    next.add(l);
                                }
                            }
                            argLists = next;
                        }
                        String key = rep.getSimpleName() + "." + TerminalBodyKinds.nameAndDescriptor(m);
                        for (String s : instancesOf(rep, CONTENTS)) {
                            String plain = RepEqualsMatrixTest.contentOf(s);
                            for (List<Object> args : argLists) {
                                Object[] a = args.toArray();
                                Outcome got = outcome(m, s, a);
                                // the stock String.equals with a rep argument is answered by the REDIRECT mirror
                                Outcome want = m.getName().equals("equals") && a.length == 1 ? new Outcome("value", RepEq.eq(plain, a[0])) : outcome(m, plain, a);
                                cellsPerMethod.merge(key, 1, Integer::sum);
                                if (!Objects.equals(got, want)) {
                                    wrong.add(dflt + " " + key + " on [" + plain + "] args " + Arrays.toString(a) + ": rep " + got + " vs String " + want);
                                }
                            }
                        }
                    }
                }
            }
        } finally {
            Locale.setDefault(saved);
        }
        Assert.assertEquals("overridden methods with an argument type this test cannot generate", List.of(), noGenerator);
        Assert.assertEquals("non-content-equivalent cells (first 20 of " + wrong.size() + "): " + wrong.subList(0, Math.min(20, wrong.size())), 0, wrong.size());
        /* The overrides today (a moved set is fine, it is enumerated; this only shows the matrix is not vacuous). */
        Assert.assertTrue("cells " + cellsPerMethod, cellsPerMethod.keySet().containsAll(Set.of("SingleByteString.equals(Ljava/lang/Object;)Z",
                        "SingleByteString.charAt(I)C", "SingleByteString.toUpperCase()Ljava/lang/String;", "TrivialString.hashCode()I",
                        // the this-free hand-off overrides
                        "SingleByteString.toUpperCase(Ljava/util/Locale;)Ljava/lang/String;", "SingleByteString.toLowerCase(Ljava/util/Locale;)Ljava/lang/String;",
                        "SingleByteString.toLowerCase()Ljava/lang/String;", "SingleByteString.offsetByCodePoints(II)I")));
        for (Map.Entry<String, Integer> e : cellsPerMethod.entrySet()) {
            Assert.assertTrue(e.getKey() + " cells " + e.getValue(), e.getValue() >= 128);
        }
    }
}
