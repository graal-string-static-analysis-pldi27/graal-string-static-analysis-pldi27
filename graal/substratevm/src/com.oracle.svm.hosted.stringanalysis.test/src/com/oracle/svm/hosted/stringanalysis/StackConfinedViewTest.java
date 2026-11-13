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
import java.io.StringWriter;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * The stack-confined accumulator view.
 * <ul>
 * <li>the variant rule ({@link AccumulatorHeuristic#accVariant}) and the conservative
 * leak-mark half of "stored";</li>
 * <li>every heap-escape route sets the confinement flag before any branch or return (a bytecode pin; the end-to-end
 * flag rows are in {@code StringAtomEndToEndTest});</li>
 * <li>the profile line (the variant word on the existing 4-token line), the loader and the parent's factory choice;</li>
 * <li>the runtime: {@code createSkipCheck} shares at any occupancy, the torn snapshot still copies, and the
 * copy branch of every builder factory returns an exact {@code java.lang.String} equal to the JDK's {@code toString}
 * (coder included: the builder JDK's {@code String.equals} compares the coders).</li>
 * </ul>
 */
public class StackConfinedViewTest {

    // ---- the variant ----

    @Test
    public void variantTruthTable() {
        Assert.assertEquals("ACCUMULATOR_VIEW_SHARED", AccumulatorHeuristic.accVariant(false));
        Assert.assertEquals("ACCUMULATOR_VIEW", AccumulatorHeuristic.accVariant(true));
        Assert.assertEquals(AccumulatorHeuristic.ACCUMULATOR_VIEW_SHARED, StringRepresentationReplacementPlugin.ACCUMULATOR_VIEW_SHARED);
    }

    /** "Stored" also covers a leak-marked hand-list terminal outside W_view; a W_view entry or an unmarked one is not. */
    @Test
    public void leakMarkedTerminalsOutsideTheWhitelistCountAsStored() {
        int outside = 0;
        for (StringTerminalHandList.Entry e : StringTerminalHandList.leakMarked()) {
            boolean w = StringViewWhitelist.isWhitelistedUsage(e.name(), e.declaringClass(), e.signature());
            Assert.assertEquals(e.toString(), !w, AccumulatorHeuristic.isLeakMarkedOutsideWhitelist(e.declaringClass(), e.name(), e.signature()));
            outside += w ? 0 : 1;
        }
        Assert.assertTrue("not vacuous: some leak-marked terminal is outside W_view", outside > 0);
        Assert.assertTrue(AccumulatorHeuristic.isLeakMarkedOutsideWhitelist("java.lang.String", "intern", ""));
        Assert.assertFalse("not leak-marked", AccumulatorHeuristic.isLeakMarkedOutsideWhitelist("java.lang.String", "length", ""));
        Assert.assertFalse("another owner", AccumulatorHeuristic.isLeakMarkedOutsideWhitelist("java.lang.Object", "intern", ""));
    }

    // ---- the flag's setters: every heap-escape route marks before any branch or return ----

    private static final String RT = "com/oracle/svm/hosted/stringanalysis/RecursiveTracking";
    private static final String JME = "com/oracle/svm/hosted/stringanalysis/JdkModelEngine";
    private static final String CFE = "com/oracle/svm/hosted/stringanalysis/ClosedFieldEscape";
    private static final String TLM = "com/oracle/svm/hosted/stringanalysis/ThreadLocalModel";

    /**
     * The routes ({@code RecursiveTracking}: escape, escapeIntoStatic, escapeInto (also commitEscape, ThreadLocal.set, the
     * arraycopy/clone continuations and the model stores), buildTimeEscape; {@code ClosedFieldEscape.escapeIntoKey};
     * {@code ThreadLocalModel.vmtlEscape}; the model's own escapeInto): each calls {@code markStored} before its first branch, return or throw, so no early return skips it.
     */
    @Test
    public void everyEscapeRouteMarksBeforeAnyEarlyReturn() throws IOException {
        Map<String, Integer> seen = new TreeMap<>();
        check(RT, Set.of("escape", "escapeIntoStatic", "escapeInto", "buildTimeEscape"), seen);
        check(CFE, Set.of("escapeIntoKey"), seen);
        check(TLM, Set.of("vmtlEscape"), seen);
        check(JME, Set.of("escapeInto"), seen);
        Assert.assertEquals("every route method found once: " + seen,
                        "{ClosedFieldEscape.escapeIntoKey=1, JdkModelEngine.escapeInto=1, RecursiveTracking.buildTimeEscape=1, RecursiveTracking.escape=1, " +
                                        "RecursiveTracking.escapeInto=1, RecursiveTracking.escapeIntoStatic=1, ThreadLocalModel.vmtlEscape=1}",
                        seen.toString());
    }

    private static void check(String owner, Set<String> names, Map<String, Integer> seen) throws IOException {
        for (MethodModel m : ClassFile.of().parse(classBytes(owner)).methods()) {
            String name = m.methodName().stringValue();
            if (!names.contains(name)) {
                continue;
            }
            seen.merge(owner.substring(owner.lastIndexOf('/') + 1) + "." + name, 1, Integer::sum);
            boolean marked = false;
            for (CodeElement e : m.code().map(c -> c.elementList()).orElse(List.of())) {
                if (e instanceof InvokeInstruction i && i.owner().asInternalName().equals(RT) && i.name().equalsString("markStored")) {
                    marked = true;
                    break;
                }
                Assert.assertFalse(name + ": a branch/return/throw before markStored: " + e,
                                e instanceof BranchInstruction || e instanceof ReturnInstruction || e instanceof ThrowInstruction || e instanceof TableSwitchInstruction ||
                                                e instanceof LookupSwitchInstruction);
            }
            Assert.assertTrue(name + " calls markStored", marked);
        }
    }

    private static byte[] classBytes(String internalName) throws IOException {
        try (InputStream in = StackConfinedViewTest.class.getResourceAsStream("/" + internalName + ".class")) {
            Assert.assertNotNull(internalName, in);
            return in.readAllBytes();
        }
    }

    // ---- profile, loader, parent ----

    @Test
    public void theSharedVariantRidesTheFourTokenLine() throws Exception {
        Path tmp = Files.createTempFile("scv", ".txt");
        try {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex x = graph.newVertex();
            x.setSourceLocation("W#bench()Ljava/lang/String;@14");
            SugVertex y = graph.newVertex();
            y.setSourceLocation("W#other()Ljava/lang/String;@3");
            List<InstrumentationDecision> ds = new ArrayList<>();
            ds.add(new InstrumentationDecision(x, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW_SHARED", "java.lang.StringBuffer"));
            ds.add(new InstrumentationDecision(y, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW", "java.lang.StringBuilder"));
            StringAnalysisFeature.dumpProfile(ds, tmp.toString());
            List<String> lines = Files.readAllLines(tmp);
            Assert.assertTrue(lines.toString(), lines.contains("W#bench()Ljava/lang/String;@14 STRING_VIEW ACCUMULATOR_VIEW_SHARED java.lang.StringBuffer"));
            RepresentationProfile p = RepresentationProfileLoader.load(tmp.toString());
            ProfileEntry e = p.getEntry("W#bench()Ljava/lang/String;@14", OptimizationType.STRING_VIEW);
            Assert.assertEquals("ACCUMULATOR_VIEW_SHARED", e.getVariant());
            Assert.assertEquals("java.lang.StringBuffer", e.getAccumulatorClass());
            Assert.assertEquals("ACCUMULATOR_VIEW", p.getEntry("W#other()Ljava/lang/String;@3", OptimizationType.STRING_VIEW).getVariant());
            for (List<String> bad : List.of(
                            List.of("K#m()V@1 STRING_VIEW ACCUMULATOR_VIEW_SHARED java.lang.StringBuilder extra"), // five tokens
                            List.of("K#m()V@1 LAZY_CONCAT ACCUMULATOR_VIEW_SHARED java.lang.StringBuilder"), // another type
                            List.of("K#m()V@1 STRING_VIEW ACCUMULATOR_VIEW java.lang.StringBuilder", "K#m()V@1 STRING_VIEW ACCUMULATOR_VIEW_SHARED java.lang.StringBuilder"))) {
                Files.write(tmp, bad);
                try {
                    RepresentationProfileLoader.load(tmp.toString());
                    Assert.fail("refused: " + bad);
                } catch (IllegalArgumentException expected) {
                    // refused
                }
            }
        } finally {
            Files.deleteIfExists(tmp);
        }
    }

    /**
     * Two decisions at one profile key (two SUG vertices can share a {@code class#method@bci} key) that
     * differ only in the variant: the stored {@code ACCUMULATOR_VIEW} wins over {@code ACCUMULATOR_VIEW_SHARED} in
     * either order, and the key keeps its position; other conflicts keep the first (unchanged).
     */
    @Test
    public void aStoredDecisionWinsOverSharedAtOneKey() throws Exception {
        Assert.assertTrue(StringAnalysisFeature.storedAccumulatorWins("ACCUMULATOR_VIEW_SHARED", "ACCUMULATOR_VIEW"));
        Assert.assertFalse(StringAnalysisFeature.storedAccumulatorWins("ACCUMULATOR_VIEW", "ACCUMULATOR_VIEW_SHARED"));
        Assert.assertFalse(StringAnalysisFeature.storedAccumulatorWins("ACCUMULATOR_VIEW_SHARED", null));
        Assert.assertFalse(StringAnalysisFeature.storedAccumulatorWins(null, "ACCUMULATOR_VIEW"));
        for (boolean sharedFirst : new boolean[]{true, false}) {
            Path tmp = Files.createTempFile("scv-dup", ".txt");
            try {
                StringUtilizationGraph graph = new StringUtilizationGraph();
                SugVertex a = graph.newVertex();
                a.setSourceLocation("W#a()V@1");
                SugVertex x = graph.newVertex();
                x.setSourceLocation("W#dup()Ljava/lang/String;@9");
                SugVertex y = graph.newVertex();
                y.setSourceLocation("W#dup()Ljava/lang/String;@9");
                InstrumentationDecision shared = new InstrumentationDecision(sharedFirst ? x : y, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW_SHARED", "java.lang.StringBuilder");
                InstrumentationDecision stored = new InstrumentationDecision(sharedFirst ? y : x, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW", "java.lang.StringBuilder");
                List<InstrumentationDecision> ds = new ArrayList<>();
                ds.add(new InstrumentationDecision(a, OptimizationType.STRING_VIEW, null));
                ds.add(sharedFirst ? shared : stored);
                ds.add(sharedFirst ? stored : shared);
                StringAnalysisFeature.dumpProfile(ds, tmp.toString());
                List<String> lines = Files.readAllLines(tmp);
                Assert.assertEquals("sharedFirst " + sharedFirst, List.of("W#a()V@1 STRING_VIEW", "W#dup()Ljava/lang/String;@9 STRING_VIEW ACCUMULATOR_VIEW java.lang.StringBuilder"), lines);
                Assert.assertEquals("ACCUMULATOR_VIEW", RepresentationProfileLoader.load(tmp.toString()).getEntry("W#dup()Ljava/lang/String;@9", OptimizationType.STRING_VIEW).getVariant());
            } finally {
                Files.deleteIfExists(tmp);
            }
        }
    }

    /**
     * Every derived string a {@code StringView} can hand out (a view sharing its backing, or itself) must
     * keep the same atom's walk going at the call's result ({@code RecursiveTracking.stringTerminal} continues iff the
     * hand list says {@code returnsThis}), or a store of {@code s.substring(1)} / {@code s.trim()} would not mark the
     * extraction stored and a shared view would be retained (memory). Pinned conservatively: every public
     * String/CharSequence-returning instance method StringView declares overrides a {@code String} method and is a
     * {@code returnsThis} hand-list entry; a new override must be listed (or exempted here with its reason). The
     * StringView-returning factories ({@code create}, {@code createView}) are static and not terminals.
     */
    @Test
    public void everyStringViewOverrideReturningAStringContinuesAtItsResult() {
        List<String> seen = new ArrayList<>();
        for (Method m : StringView.class.getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers()) || !Modifier.isPublic(m.getModifiers()) || m.isSynthetic() || m.isBridge() ||
                            !(m.getReturnType() == String.class || m.getReturnType() == CharSequence.class)) {
                continue;
            }
            String sig = String.join(",", Arrays.stream(m.getParameterTypes()).map(Class::descriptorString).toList());
            String what = m.getName() + "(" + sig + ")";
            try {
                Assert.assertEquals(what + " overrides String's", m.getReturnType(), String.class.getMethod(m.getName(), m.getParameterTypes()).getReturnType());
            } catch (NoSuchMethodException e) {
                Assert.fail(what + ": not a String method");
            }
            Assert.assertTrue(what + ": a StringView result must continue the walk (hand-list returnsThis)",
                            StringAtoms.continuesAtResult("java.lang.String", m.getName(), sig, m.getReturnType().getName()));
            seen.add(what);
        }
        Assert.assertTrue("not vacuous: " + seen, seen.containsAll(List.of("substring(I)", "substring(I,I)", "subSequence(I,I)", "trim()", "strip()", "stripLeading()",
                        "stripTrailing()", "repeat(I)", "toUpperCase()", "toLowerCase(Ljava/util/Locale;)")));
        Assert.assertTrue("String.toString (not overridden: returns this)", StringAtoms.continuesAtResult("java.lang.String", "toString", "", "java.lang.String"));
    }

    @Test
    public void theParentPicksTheFactoryByVariant() throws ReflectiveOperationException {
        Assert.assertTrue(StringRepresentationReplacementPlugin.isAccumulatorVariant("ACCUMULATOR_VIEW"));
        Assert.assertTrue(StringRepresentationReplacementPlugin.isAccumulatorVariant("ACCUMULATOR_VIEW_SHARED"));
        Assert.assertFalse(StringRepresentationReplacementPlugin.isAccumulatorVariant(null));
        Assert.assertFalse(StringRepresentationReplacementPlugin.isAccumulatorVariant("ROPE"));
        Assert.assertEquals("create", StringRepresentationReplacementPlugin.accumulatorFactoryName("ACCUMULATOR_VIEW"));
        Assert.assertEquals("createSkipCheck", StringRepresentationReplacementPlugin.accumulatorFactoryName("ACCUMULATOR_VIEW_SHARED"));
        for (Class<?> acc : StringRepresentationReplacementPlugin.ACCUMULATOR_CLASSES) {
            for (String name : List.of("create", "createSkipCheck")) {
                Method f = StringView.class.getDeclaredMethod(name, acc);
                Assert.assertSame(String.class, f.getReturnType());
                Assert.assertTrue(Modifier.isStatic(f.getModifiers()) && Modifier.isPublic(f.getModifiers()));
                Assert.assertFalse("inlining parity A9: a plain static factory", forceInline(f));
            }
        }
        Assert.assertTrue("the snapshot stays @ForceInline", forceInline(StringView.class.getDeclaredMethod("ofBuilderSnapshot", byte[].class, byte.class, int.class, boolean.class,
                        boolean.class)));
    }

    private static boolean forceInline(Method m) {
        return Arrays.stream(m.getDeclaredAnnotations()).anyMatch(a -> a.annotationType().getSimpleName().equals("ForceInline"));
    }

    // ---- the runtime ----

    private static byte[] latin1(int capacity, String content) {
        byte[] v = new byte[capacity];
        byte[] c = content.getBytes(StandardCharsets.ISO_8859_1);
        System.arraycopy(c, 0, v, 0, c.length);
        return v;
    }

    /** SkipCheck (trim=false) shares an 8 KB array holding 10 chars: a later write at >= count is invisible, a write below it shows (the share). */
    @Test
    public void skipCheckSharesAtAnyOccupancy() {
        byte[] v = latin1(8192, "0123456789");
        String s = StringView.ofBuilderSnapshot(v, (byte) 0, 10, true, false);
        Assert.assertSame(StringView.class, s.getClass());
        RepEq.assertRepEquals("0123456789", s);
        v[10] = 'x';
        v[4000] = 'y';
        RepEq.assertRepEquals("an only-growing builder's later appends are invisible", "0123456789", s);
        v[0] = 'Z';
        Assert.assertEquals("the array is shared, not copied", 'Z', s.charAt(0));
        byte[] w = latin1(8192, "0123456789");
        String t = StringView.ofBuilderSnapshot(w, (byte) 0, 10, true, true);
        Assert.assertSame("the trimmed form copies (an exact String)", String.class, t.getClass());
        w[0] = 'Z';
        Assert.assertEquals("0123456789", t);
        Assert.assertSame("the 4-arg form is trim=true", String.class, StringView.ofBuilderSnapshot(latin1(8192, "ab"), (byte) 0, 2, true).getClass());
    }

    /** A torn snapshot (count past the array) copies whatever trim says; the copy is an exact, zero-padded String. */
    @Test
    public void tornSnapshotCopiesEvenWhenSkippingTheCheck() {
        for (boolean trim : new boolean[]{false, true}) {
            String s = StringView.ofBuilderSnapshot(latin1(4, "abcd"), (byte) 0, 6, true, trim);
            Assert.assertSame(String.class, s.getClass());
            Assert.assertEquals("abcd\0\0", s);
            byte[] u = new byte[6]; // a UTF-16 coder paired with a short array (JDK 25 writes coder before value)
            u[0] = 'a';
            String t = StringView.ofBuilderSnapshot(u, (byte) 1, 4, false, trim);
            Assert.assertSame(String.class, t.getClass());
            Assert.assertEquals(4, t.length());
        }
    }

    /**
     * An empty snapshot is the literal {@code ""} whatever the trim, the coder or the capacity (also a capacity-0 array,
     * which must not become an empty view); a torn snapshot gives one exact String
     * (the content padded with zeros) on every copy case, even at trim false.
     */
    @Test
    public void emptyIsTheLiteralAndTornCopiesOnce() {
        for (boolean trim : new boolean[]{false, true}) {
            for (byte coder = 0; coder <= 1; coder++) {
                for (int cap : new int[]{0, 1, 16, 8192}) {
                    Assert.assertSame("", StringView.ofBuilderSnapshot(new byte[cap], coder, 0, true, trim));
                    Assert.assertSame("", StringView.ofBuilderSnapshot(new byte[cap], coder, 0, false, trim));
                }
            }
        }
        Assert.assertEquals("ab\0", StringView.ofBuilderSnapshot(latin1(2, "ab"), (byte) 0, 3, false, false));
        byte[] u = utf16(1, "\u20ac"); // one UTF-16 char, count 2: torn
        for (boolean ml1 : new boolean[]{false, true}) {
            String t = StringView.ofBuilderSnapshot(u, (byte) 1, 2, ml1, false);
            Assert.assertSame(String.class, t.getClass());
            Assert.assertEquals("\u20ac\0", t);
        }
        String c = StringView.ofBuilderSnapshot(utf16(1, "a"), (byte) 1, 2, true, false);
        Assert.assertEquals("a\0", c);
    }

    /** The copy branch is the JDK's toString rule: empty = "", Latin-1 copy, UTF-16 compressed only with maybeLatin1. */
    @Test
    public void copyBranchIsTheJdkToStringRule() {
        Assert.assertSame("", StringView.ofBuilderSnapshot(new byte[16], (byte) 0, 0, true, true));
        Assert.assertSame("", StringView.ofBuilderSnapshot(new byte[16], (byte) 1, 0, true, true));
        byte[] latinOnlyUtf16 = utf16(64, "ab");
        String c = StringView.ofBuilderSnapshot(latinOnlyUtf16, (byte) 1, 2, true, true);
        Assert.assertSame(String.class, c.getClass());
        Assert.assertEquals("maybeLatin1: the compact copy (coder LATIN1, equal to the literal)", "ab", c);
        String u = StringView.ofBuilderSnapshot(utf16(64, "a€"), (byte) 1, 2, false, true);
        Assert.assertSame(String.class, u.getClass());
        Assert.assertEquals("a€", u);
        String u2 = StringView.ofBuilderSnapshot(utf16(64, "a€"), (byte) 1, 2, true, true);
        Assert.assertSame(String.class, u2.getClass());
        Assert.assertEquals("a€", u2);
    }

    private static byte[] utf16(int capacityChars, String content) {
        byte[] b = content.getBytes(java.nio.ByteOrder.nativeOrder() == java.nio.ByteOrder.BIG_ENDIAN ? StandardCharsets.UTF_16BE : StandardCharsets.UTF_16LE);
        return Arrays.copyOf(b, capacityChars * 2);
    }

    /**
     * For all three builder kinds and both factories: the copy branch (under half full) is an exact
     * {@code String} equal to the JDK's {@code toString} (coders included), SkipCheck shares instead; above half full both
     * share. Latin-1, UTF-16, and a UTF-16 builder whose JDK {@code maybeLatin1} is set (a deleted non-Latin-1 char).
     */
    @Test
    public void builderFactoriesCopyToAnExactStringAndSkipCheckShares() {
        for (String content : List.of("abc", "ab€d", "")) {
            for (int kind = 0; kind < 3; kind++) {
                for (boolean full : new boolean[]{false, true}) {
                    int cap = full ? Math.max(1, content.length()) : 256;
                    Object b = builder(kind, cap, content);
                    String jdk = b.toString();
                    String plain = create(kind, b, false);
                    String skip = create(kind, b, true);
                    String what = "kind " + kind + " full " + full + " '" + content + "'";
                    RepEq.assertRepEquals(what, jdk, plain);
                    RepEq.assertRepEquals(what, plain, jdk);
                    RepEq.assertRepEquals(what, jdk, skip);
                    if (content.isEmpty()) {
                        // both factories give the literal "" (the JDK's toString identity), at any capacity
                        Assert.assertSame(what, "", plain);
                        Assert.assertSame(what, "", skip);
                        continue;
                    }
                    Assert.assertSame(what, full ? StringView.class : String.class, plain.getClass());
                    Assert.assertSame(what, StringView.class, skip.getClass());
                }
            }
        }
        StringBuilder m = new StringBuilder(256);
        m.append("ab€");
        m.deleteCharAt(2); // JDK: maybeLatin1 set, the builder stays UTF-16
        String c = StringView.create(m);
        Assert.assertSame(String.class, c.getClass());
        Assert.assertEquals("compressed like the JDK's toString", m.toString(), c);
        Assert.assertEquals("ab", c);
        String sc = StringView.createSkipCheck(m);
        Assert.assertEquals("ab", sc);
        Assert.assertSame("the shared path's Latin-1-only scan also gives the compact copy", String.class, sc.getClass());
    }

    private static Object builder(int kind, int cap, String content) {
        switch (kind) {
            case 0:
                return new StringBuilder(cap).append(content);
            case 1:
                return new StringBuffer(cap).append(content);
            default:
                StringWriter w = new StringWriter(cap);
                w.write(content);
                return w;
        }
    }

    private static String create(int kind, Object b, boolean skip) {
        switch (kind) {
            case 0:
                return skip ? StringView.createSkipCheck((StringBuilder) b) : StringView.create((StringBuilder) b);
            case 1:
                return skip ? StringView.createSkipCheck((StringBuffer) b) : StringView.create((StringBuffer) b);
            default:
                return skip ? StringView.createSkipCheck((StringWriter) b) : StringView.create((StringWriter) b);
        }
    }
}
