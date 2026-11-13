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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The leak rule. A hand-list entry marked as leaking {@code this} other than by its
 * return value ({@link StringTerminalHandList.Entry#isLeakMarked()}) must not be whitelisted by any representation
 * whose runtime body for that method is the inherited default body. The opaque-terminal premise (the listed bodies are
 * never walked) holds only then. No body is walked: for every leak-marked entry and every representation heuristic's
 * whitelist (W_view incl. the verdict-layer {@code isWhitelistedUsage}, W_lazy per variant, W_accumulator) the test
 * asserts "not whitelisted, or the representation class declares its own override of that exact signature, and that
 * override does not call the String method by {@code invokespecial} (a {@code super.m()} call runs the default body)".
 * A later whitelist addition, or a rep that stops overriding, fails the build. SINGLE_BYTE is exempt: it is a flat rep
 * (a real {@code value[]}) with no whitelist, so a default body runs on a real String.
 */
public class HandListLeakWhitelistTest {

    /** A whitelist predicate over (name, declaring class, signature) and the representation it admits. */
    interface Whitelist {
        boolean admits(String name, String declaringClass, String signature);
    }

    /**
     * One (whitelist, representation class) pair; a null class = the whitelist admits no representation class.
     * {@code control} is an admitted non-leak usage {@code {name, declaringClass, signature}} (a positive control: a
     * key-format drift in the row's whitelist fails the build instead of passing silently).
     */
    record RepWhitelist(String label, Whitelist whitelist, Class<?> representation, String[] control) {
    }

    private static final String[] VIEW_CONTROL = {"length", StringTerminalHandList.STRING, ""};
    private static final String[] LAZY_CONTROL = {"charAt", StringTerminalHandList.STRING, "I"};

    /** Every representation heuristic's whitelist, with the representation class that runs when it admits. */
    static List<RepWhitelist> repWhitelists() {
        List<RepWhitelist> out = new ArrayList<>();
        // W_view: the Phase-A form and the verdict-layer form (+ the compareTo(Object) bridge)
        out.add(new RepWhitelist("W_view.isWhitelisted", StringViewWhitelist::isWhitelisted, StringView.class, VIEW_CONTROL));
        out.add(new RepWhitelist("W_view.isWhitelistedUsage", StringViewWhitelist::isWhitelistedUsage, StringView.class, VIEW_CONTROL));
        // W_lazy, per variant: the variant's own representation (LazyConcatHeuristic.builtRepresentation)
        Map<String, Class<?>> lazy = new LinkedHashMap<>();
        lazy.put("ROPE", RopeString.class);
        lazy.put("THREE_WAY", ThreeWayString.class);
        lazy.put("FIXED4", FixedConcat4.class);
        lazy.put("ARRAY_LAZY", ArrayLazyString.class);
        lazy.put("INTERLEAVED", InterleavedStringArray.class);
        for (Map.Entry<String, Class<?>> e : lazy.entrySet()) {
            String variant = e.getKey();
            out.add(new RepWhitelist("W_lazy[" + variant + "]", (n, d, s) -> LazyConcatWhitelist.isWhitelisted(n, d, s, variant), e.getValue(), LAZY_CONTROL));
        }
        // W_lazy with an unknown variant (null) may build any lazy rep: every one of them must override
        for (Map.Entry<String, Class<?>> e : lazy.entrySet()) {
            out.add(new RepWhitelist("W_lazy[null->" + e.getKey() + "]", (n, d, s) -> LazyConcatWhitelist.isWhitelisted(n, d, s, null), e.getValue(), LAZY_CONTROL));
        }
        // The accumulator's representation-bearing path: the EXTRACTED string is validated with W_view
        // isWhitelistedUsage (AccumulatorHeuristic.validateExtractedString) and becomes a STRING_VIEW
        // ACCUMULATOR_VIEW decision, i.e. a StringView (StringView.create(StringBuilder)).
        out.add(new RepWhitelist("W_accumulator.extraction(W_view)", StringViewWhitelist::isWhitelistedUsage, StringView.class, VIEW_CONTROL));
        // W_accumulator proper, as the heuristic applies it (AccumulatorHeuristic.collectAccumulatorUsages): builder
        // types only. Builders are not custom representations, so an admitted leak entry has no rep that could
        // override it. For the String entries this row is vacuous by construction; it guards builder-declared entries.
        out.add(new RepWhitelist("W_accumulator", (n, d, s) -> AccumulatorWhitelist.isAccumulatorType(d) && AccumulatorWhitelist.isWhitelisted(n), null,
                        new String[]{"append", "java.lang.StringBuilder", "Ljava/lang/String;"}));
        return out;
    }

    /** The leak rule's check; returns one message per violation (empty = the rule holds). */
    static List<String> violations(List<StringTerminalHandList.Entry> entries, List<RepWhitelist> whitelists) {
        List<String> out = new ArrayList<>();
        for (StringTerminalHandList.Entry e : entries) {
            if (!e.isLeakMarked()) {
                continue;
            }
            for (RepWhitelist w : whitelists) {
                if (!w.whitelist().admits(e.name(), e.declaringClass(), e.signature())) {
                    continue;
                }
                if (w.representation() == null || !overridesWithoutDefaultBody(w.representation(), e)) {
                    out.add(w.label() + " admits leak-marked " + e.declaringClass() + "." + e.name() + "(" + e.signature() + ") [" + e.leak() + "] but " +
                                    (w.representation() == null ? "admits no representation that overrides it"
                                                    : w.representation().getName() + " runs the default body (no own override, or a super call)"));
                }
            }
        }
        return out;
    }

    /** The rep class declares a non-static, non-synthetic, non-bridge method of exactly that name and signature. */
    static boolean declaresOwnOverride(Class<?> rep, StringTerminalHandList.Entry e) {
        try {
            Method m = rep.getDeclaredMethod(e.name(), parameterTypes(e.signature()));
            return !Modifier.isStatic(m.getModifiers()) && !m.isSynthetic() && !m.isBridge();
        } catch (NoSuchMethodException ex) {
            return false;
        }
    }

    /**
     * The rep's own override exists and does not run the default body, i.e. its bytecode has no
     * {@code invokespecial java/lang/String.<same name>} (any descriptor: a {@code super.m(...)} call of an overload
     * runs a default body with {@code this} = the rep as well). Direct calls only; the reps extend String directly.
     */
    static boolean overridesWithoutDefaultBody(Class<?> rep, StringTerminalHandList.Entry e) {
        if (!declaresOwnOverride(rep, e)) {
            return false;
        }
        return !callsStringSuper(rep, e);
    }

    private static MetaAccessProvider metaAccess;

    static boolean callsStringSuper(Class<?> rep, StringTerminalHandList.Entry e) {
        Method m;
        try {
            m = rep.getDeclaredMethod(e.name(), parameterTypes(e.signature()));
        } catch (NoSuchMethodException ex) {
            return false;
        }
        if (metaAccess == null) {
            metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        }
        ResolvedJavaMethod rm = metaAccess.lookupJavaMethod(m);
        byte[] code = rm.getCode();
        Assert.assertNotNull("no bytecode for " + m, code);
        BytecodeStream s = new BytecodeStream(code);
        while (s.currentBC() != Bytecodes.END) {
            if (s.currentBC() == Bytecodes.INVOKESPECIAL) {
                JavaMethod t = rm.getConstantPool().lookupMethod(s.readCPI(), Bytecodes.INVOKESPECIAL, rm);
                if (t != null && "Ljava/lang/String;".equals(t.getDeclaringClass().getName()) && e.name().equals(t.getName())) {
                    return true;
                }
            }
            s.next();
        }
        return false;
    }

    static Class<?>[] parameterTypes(String signature) {
        if (signature.isEmpty()) {
            return new Class<?>[0];
        }
        String[] parts = signature.split(",");
        Class<?>[] out = new Class<?>[parts.length];
        for (int i = 0; i < parts.length; i++) {
            out[i] = typeOf(parts[i]);
        }
        return out;
    }

    private static Class<?> typeOf(String d) {
        switch (d) {
            case "Z":
                return boolean.class;
            case "B":
                return byte.class;
            case "C":
                return char.class;
            case "S":
                return short.class;
            case "I":
                return int.class;
            case "J":
                return long.class;
            case "F":
                return float.class;
            case "D":
                return double.class;
            default:
                try {
                    if (d.startsWith("[")) {
                        return Class.forName(d.replace('/', '.'), false, HandListLeakWhitelistTest.class.getClassLoader());
                    }
                    if (d.startsWith("L") && d.endsWith(";")) {
                        return Class.forName(d.substring(1, d.length() - 1).replace('/', '.'), false, HandListLeakWhitelistTest.class.getClassLoader());
                    }
                } catch (ClassNotFoundException ex) {
                    throw new AssertionError("hand-list signature names a missing class: " + d, ex);
                }
                throw new AssertionError("not a field descriptor: " + d);
        }
    }

    /** The rule itself: no leak-marked entry is whitelisted onto a representation that runs its default body. */
    @Test
    public void leakMarkedEntriesAreNeverWhitelistedOntoADefaultBody() {
        List<String> v = violations(StringTerminalHandList.STRING_ENTRIES, repWhitelists());
        Assert.assertTrue("the §4.2 leak rule is violated:\n  " + String.join("\n  ", v), v.isEmpty());
    }

    /** Every entry names a real public instance method of its declaring class on this JDK (the list tracks the JDK). */
    @Test
    public void everyEntryExistsOnThisJdk() throws ClassNotFoundException {
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            Class<?> c = Class.forName(e.declaringClass());
            Method m;
            try {
                m = c.getDeclaredMethod(e.name(), parameterTypes(e.signature()));
            } catch (NoSuchMethodException ex) {
                throw new AssertionError("hand-list entry does not exist on this JDK: " + e, ex);
            }
            Assert.assertTrue("not public: " + e, Modifier.isPublic(m.getModifiers()));
            Assert.assertFalse("static: " + e, Modifier.isStatic(m.getModifiers()));
            Assert.assertFalse("synthetic/bridge: " + e, m.isSynthetic() || m.isBridge());
        }
    }

    /**
     * The list's leak marks are pinned, including the conservative additions {@code intern},
     * {@code splitWithDelimiters}, {@code matches}, {@code compareToIgnoreCase}, {@code equals} and
     * {@code offsetByCodePoints}. A changed mark must be a deliberate, reviewed edit.
     */
    @Test
    public void leakMarkedSetIsTheDesignTable() {
        List<String> got = new ArrayList<>();
        for (StringTerminalHandList.Entry e : StringTerminalHandList.leakMarked()) {
            got.add(e.name() + "(" + e.signature() + ")");
        }
        Assert.assertEquals(List.of(
                        "intern()",
                        "toLowerCase()", "toLowerCase(Ljava/util/Locale;)", "toUpperCase()", "toUpperCase(Ljava/util/Locale;)",
                        "replaceAll(Ljava/lang/String;,Ljava/lang/String;)", "replaceFirst(Ljava/lang/String;,Ljava/lang/String;)",
                        "split(Ljava/lang/String;)", "split(Ljava/lang/String;,I)", "describeConstable()", "splitWithDelimiters(Ljava/lang/String;,I)",
                        "transform(Ljava/util/function/Function;)", "formatted([Ljava/lang/Object;)",
                        "matches(Ljava/lang/String;)", "compareToIgnoreCase(Ljava/lang/String;)", "equals(Ljava/lang/Object;)", "offsetByCodePoints(I,I)"), got);
        Assert.assertEquals(17, got.size());
    }

    /** Every whitelist row admits its positive control (so the rows are not vacuous by a format drift). */
    @Test
    public void everyWhitelistRowAdmitsItsPositiveControl() {
        for (RepWhitelist w : repWhitelists()) {
            String[] c = w.control();
            Assert.assertTrue(w.label() + " does not admit its control " + String.join("|", c), w.whitelist().admits(c[0], c[1], c[2]));
        }
    }

    /** A class that overrides nothing (the checker's negative fixture). */
    static final class NoOverrides {
    }

    /**
     * Non-vacuity: the override branch is exercised today (W_view admits the leak-marked {@code toLowerCase} /
     * {@code toUpperCase}, which StringView overrides), and the checker reports a violation
     * when a whitelist admits a leak-marked entry onto a class without its own override.
     */
    @Test
    public void theCheckIsNotVacuous() {
        StringTerminalHandList.Entry lower = new StringTerminalHandList.Entry(StringTerminalHandList.STRING, "toLowerCase", "", true, StringTerminalHandList.Leak.STORE);
        Assert.assertTrue(StringViewWhitelist.isWhitelistedUsage(lower.name(), lower.declaringClass(), lower.signature()));
        Assert.assertTrue(declaresOwnOverride(StringView.class, lower));
        Assert.assertFalse(declaresOwnOverride(RopeString.class, lower));
        // an override that calls the String super body counts as the default body. SingleByteString's case mappings
        // do not call super (own this-free bodies); its charAt(I) does (index != 0)
        StringTerminalHandList.Entry upper = new StringTerminalHandList.Entry(StringTerminalHandList.STRING, "toUpperCase", "", true, StringTerminalHandList.Leak.STORE);
        Assert.assertTrue(declaresOwnOverride(SingleByteString.class, upper));
        Assert.assertFalse(callsStringSuper(SingleByteString.class, upper));
        Assert.assertTrue(overridesWithoutDefaultBody(SingleByteString.class, upper));
        StringTerminalHandList.Entry charAt = new StringTerminalHandList.Entry(StringTerminalHandList.STRING, "charAt", "I", false, StringTerminalHandList.Leak.STORE);
        Assert.assertTrue(declaresOwnOverride(SingleByteString.class, charAt));
        Assert.assertTrue(callsStringSuper(SingleByteString.class, charAt));
        Assert.assertFalse(overridesWithoutDefaultBody(SingleByteString.class, charAt));
        Assert.assertTrue(overridesWithoutDefaultBody(StringView.class, upper));
        RepWhitelist admitAll = new RepWhitelist("admit-all-onto-NoOverrides", (n, d, s) -> true, NoOverrides.class, VIEW_CONTROL);
        List<String> v = violations(StringTerminalHandList.STRING_ENTRIES, List.of(admitAll));
        Assert.assertEquals(StringTerminalHandList.leakMarked().size(), v.size());
        RepWhitelist admitAllNoRep = new RepWhitelist("admit-all-no-rep", (n, d, s) -> true, null, VIEW_CONTROL);
        Assert.assertEquals(StringTerminalHandList.leakMarked().size(), violations(StringTerminalHandList.STRING_ENTRIES, List.of(admitAllNoRep)).size());
        RepWhitelist admitAllSingleByte = new RepWhitelist("admit-all-onto-SingleByte", (n, d, s) -> true, SingleByteString.class, VIEW_CONTROL);
        Assert.assertTrue(violations(List.of(upper), List.of(admitAllSingleByte)).isEmpty());
        Assert.assertTrue(violations(List.of(charAt), List.of(admitAllSingleByte)).size() == 1);
        // an entry without a leak mark is out of the rule's domain
        StringTerminalHandList.Entry sub = new StringTerminalHandList.Entry(StringTerminalHandList.STRING, "substring", "I", true, StringTerminalHandList.Leak.NONE);
        Assert.assertTrue(violations(List.of(sub), List.of(admitAll)).isEmpty());
    }
}
