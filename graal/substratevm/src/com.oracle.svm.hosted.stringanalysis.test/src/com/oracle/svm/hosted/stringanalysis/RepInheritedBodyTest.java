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
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

/**
 * The whitelisted String methods
 * whose runtime body, for a rep receiver, is the inherited {@code java.lang.String} body are exactly
 * {@link #EXPECTED_INHERITED}: StringView's {@code coder()} and {@code isLatin1()} (they read the inherited
 * {@code coder} field, which super(coder) set) and {@code contentEquals(StringBuffer)} (its body calls the overridden
 * {@code contentEquals(CharSequence)} on {@code this}: a gap closed by emitting no direct call inside java.lang.String). Every
 * other admitted (rep, method) pair runs the rep's own override. A whitelist addition that a rep does not override,
 * or a rep that stops overriding a whitelisted method, moves this pin.
 * <p>
 * The five lazy reps' {@code coder()} pairs are in the pin: they do not override {@code coder()} / {@code isLatin1()}
 * (an override makes every String-typed {@code coder()} call site virtual); each passes the exact OR of its children's
 * coders to {@code super(coder)}, so the inherited field-only bodies are correct. {@code LazyRepCoderSemanticsTest}
 * pins that {@code String.coder()} and {@code String.isLatin1()} never touch {@code value} and that every lazy rep
 * answers like a flat String of the same content. W_lazy does not admit {@code isLatin1()}, so only the
 * {@code coder()} pairs appear here.
 * <p>
 * Domain: every representation whitelist the verdict layer applies ({@link HandListLeakWhitelistTest#repWhitelists()};
 * W_lazy per built variant) and every non-private instance method declared by {@code java.lang.String} (bridges
 * included: SV's own {@code compareTo(Object)} bridge counts as an override). The flat reps (SingleByteString, TrivialString) have no
 * whitelist and a real {@code value[]}: their inherited bodies are correct and out of scope.
 */
public class RepInheritedBodyTest {

    static final Set<String> EXPECTED_INHERITED = Set.of(
                    "StringView.coder()", "StringView.isLatin1()", "StringView.contentEquals(Ljava/lang/StringBuffer;)",
                    // the lazy reps' coder() pairs — no overrides (see the class javadoc); the
                    // inherited body reads only the coder field that super(coder) set to the OR of the children's coders
                    "RopeString.coder()", "ThreeWayString.coder()", "FixedConcat4.coder()",
                    "ArrayLazyString.coder()", "InterleavedStringArray.coder()",
                    // no rep overrides toString(); String.toString is field-free (pinned in ElseDirectPremiseTest).
                    // Only W_SV admits toString, so only the StringView pair appears.
                    "StringView.toString()");

    /**
     * The class whose declaration of {@code m} runs for a receiver of class {@code rep}: the production JVM-rule
     * selection ({@link TerminalBodyKinds#implementingClass}; a name/params walk of its own would count a same-signature
     * package-private rep method as an override of String's package-private one).
     */
    static Class<?> implementingClass(Class<?> rep, Method m) {
        Class<?> c = TerminalBodyKinds.implementingClass(rep, m);
        if (c == null) {
            throw new AssertionError("no implementation of " + m + " for " + rep);
        }
        return c;
    }

    static Set<String> inheritedWhitelistedPairs(List<HandListLeakWhitelistTest.RepWhitelist> whitelists) {
        Set<String> out = new TreeSet<>();
        for (HandListLeakWhitelistTest.RepWhitelist w : whitelists) {
            Class<?> rep = w.representation();
            if (rep == null || w.label().contains("[null->")) {
                // W_lazy with an unknown variant admits no rep: LazyConcatHeuristic.apply REJECTs a concat whose
                // variant is null ("too few dynamic operands for any lazy variant") after the whitelist walk
                continue;
            }
            for (Method m : String.class.getDeclaredMethods()) {
                if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers())) {
                    continue;
                }
                String sig = RepPinSupport.signature(m);
                if (!w.whitelist().admits(m.getName(), StringTerminalHandList.STRING, sig)) {
                    continue;
                }
                if (!RepPinSupport.isRep(implementingClass(rep, m))) {
                    out.add(RepPinSupport.label(rep, m.getName(), sig));
                }
            }
        }
        return out;
    }

    /**
     * Rep-aware {@code compareTo}: every {@code value == null} rep overrides
     * {@code compareTo(String)} — the five lazy reps (a shared charAt/length body,
     * {@code RepCompareTo}), StringView with its own offset-aware override. The builder JDK's
     * {@code String.compareTo} argument-side deflection ({@code anotherString.value() == null} →
     * {@code -anotherString.compareTo(this)}) and the lazy compareTo receiver rule
     * ({@code LazyConcatWhitelist.isWhitelisted}) rely on it: an inherited body would read the null
     * {@code value()} and NPE. The flat reps ({@code SingleByteString}, {@code TrivialString}) keep a real
     * {@code value[]} and inherit correctly, on the receiver and the argument side.
     */
    static final List<Class<?>> VALUE_NULL_REPS = List.of(
                    RopeString.class, ThreeWayString.class, FixedConcat4.class,
                    ArrayLazyString.class, InterleavedStringArray.class, StringView.class);

    @Test
    public void theInheritedWhitelistedPairsAreExactlyThePinnedOnes() {
        RepPinSupport.repClasses();
        Assert.assertEquals(new TreeSet<>(EXPECTED_INHERITED), inheritedWhitelistedPairs(HandListLeakWhitelistTest.repWhitelists()));
    }

    /**
     * The totality invariant of the rep-aware {@code compareTo} (see {@link #VALUE_NULL_REPS}) — every
     * {@code value == null} rep declares its own {@code compareTo(String)} (the javac-generated
     * {@code compareTo(Object)} bridge of {@code Comparable<String>} then dispatches to it). A rep that stops
     * overriding moves this pin and re-appears in {@link #theInheritedWhitelistedPairsAreExactlyThePinnedOnes}.
     */
    @Test
    public void everyValueNullRepOverridesCompareTo() throws NoSuchMethodException {
        for (Class<?> rep : VALUE_NULL_REPS) {
            Assert.assertSame(rep + " must override compareTo(String)",
                            rep, implementingClass(rep, String.class.getDeclaredMethod("compareTo", String.class)));
        }
    }

    /**
     * Every {@code value == null} rep overrides every whole-string and ranged copy variant of {@code String} (the
     * inherited bodies read {@code value()}), including the protected {@code getBytes(byte[],int,byte)}. No runtime
     * check backs this: a rep that stops overriding a copy variant fails here.
     */
    @Test
    public void everyValueNullRepOverridesEveryCopyVariant() throws NoSuchMethodException {
        Method[] copies = {
                        String.class.getDeclaredMethod("toCharArray"),
                        String.class.getDeclaredMethod("getChars", int.class, int.class, char[].class, int.class),
                        String.class.getDeclaredMethod("getBytes"),
                        String.class.getDeclaredMethod("getBytes", String.class),
                        String.class.getDeclaredMethod("getBytes", java.nio.charset.Charset.class),
                        String.class.getDeclaredMethod("getBytes", int.class, int.class, byte[].class, int.class),
                        String.class.getDeclaredMethod("getBytes", byte[].class, int.class, byte.class),
                        String.class.getDeclaredMethod("getBytes", byte[].class, int.class, int.class, byte.class, int.class)};
        for (Class<?> rep : VALUE_NULL_REPS) {
            for (Method m : copies) {
                Assert.assertSame(rep.getSimpleName() + " must override " + m, rep, implementingClass(rep, m));
            }
        }
    }

    /** Positive control: the admitted domain is not empty for any rep whitelist (a key-format drift would empty it). */
    @Test
    public void everyRepWhitelistAdmitsSomeStringMethod() {
        for (HandListLeakWhitelistTest.RepWhitelist w : HandListLeakWhitelistTest.repWhitelists()) {
            if (w.representation() == null) {
                continue;
            }
            int admitted = 0;
            for (Method m : String.class.getDeclaredMethods()) {
                if (!Modifier.isStatic(m.getModifiers()) && w.whitelist().admits(m.getName(), StringTerminalHandList.STRING, RepPinSupport.signature(m))) {
                    admitted++;
                }
            }
            Assert.assertTrue(w.label() + " admits no String instance method", admitted >= 5);
        }
    }
}
