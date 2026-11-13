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
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * Kind-level terminal-body IC entries ({@link TerminalBodyKinds}): the premises the child's kind rule relies on, pinned against
 * the real rep classes, the real whitelists and the real {@code java.lang.String} bytecode, so that a rep, whitelist or
 * JDK-body change fails here instead of silently making a marked entry incomplete.
 */
public class KindTerminalPremiseTest {

    static final List<String> NON_FLAT_KINDS = List.of("ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED", "SV");

    /** The kind partition is total over the registry: every registry kind is flat or has a whitelist. */
    @Test
    public void everyRegistryKindIsFlatOrWhitelisted() {
        Set<String> nonFlat = new TreeSet<>();
        for (String k : InlineCacheRegistry.REP_CLASSES.keySet()) {
            if (TerminalBodyKinds.isFlat(k)) {
                Assert.assertNull(TerminalBodyKinds.whitelistOf(k));
            } else {
                Assert.assertNotNull(k, TerminalBodyKinds.whitelistOf(k));
                nonFlat.add(k);
            }
        }
        Assert.assertEquals(new TreeSet<>(NON_FLAT_KINDS), nonFlat);
        Assert.assertEquals(Set.of("SBS"), new TreeSet<>(InlineCacheRegistry.REP_CLASSES.keySet()).stream().filter(TerminalBodyKinds::isFlat).collect(java.util.stream.Collectors.toSet()));
        for (String k : NON_FLAT_KINDS) {
            Assert.assertTrue(k + " is value-null (RepInheritedBodyTest.VALUE_NULL_REPS)", RepInheritedBodyTest.VALUE_NULL_REPS.contains(InlineCacheRegistry.getRepClass(k)));
        }
    }

    /**
     * E_K (the String bodies a non-flat kind runs as {@code this}) derived by the child mechanically equals the pinned
     * inherited-whitelisted pairs of {@link RepInheritedBodyTest#EXPECTED_INHERITED} (two independent derivations).
     */
    @Test
    public void entryBodiesAreTheInheritedWhitelistedPairs() throws NoSuchMethodException {
        Set<String> derived = new TreeSet<>();
        for (String k : NON_FLAT_KINDS) {
            Class<?> rep = InlineCacheRegistry.getRepClass(k);
            for (String nd : TerminalBodyKinds.entryBodies(k)) {
                Method m = stringMethod(nd);
                derived.add(rep.getSimpleName() + "." + m.getName() + "(" + TerminalBodyKinds.usageSignature(m) + ")");
            }
        }
        Assert.assertEquals(new TreeSet<>(RepInheritedBodyTest.EXPECTED_INHERITED), derived);
    }

    /**
     * Closure: an E_K body passes {@code this} nowhere outside E_K and the rep's own overrides. Every invoke in an E_K
     * body is an instance call into {@code java.lang.String}/{@code Object}/{@code CharSequence} that K either
     * overrides (it dispatches into the rep's own body) or that is itself in E_K. No static or foreign call appears
     * (a JDK change adding one fails here: the kind rule would then miss the callee's sites).
     */
    @Test
    public void entryBodiesAreClosed() throws IOException {
        ClassModel string = parse(String.class);
        Map<String, String> violations = new TreeMap<>();
        int bodies = 0;
        int invokes = 0;
        for (String k : NON_FLAT_KINDS) {
            Class<?> rep = InlineCacheRegistry.getRepClass(k);
            Set<String> e = TerminalBodyKinds.entryBodies(k);
            for (MethodModel mm : string.methods()) {
                String nd = mm.methodName().stringValue() + mm.methodType().stringValue();
                if (!e.contains(nd) || mm.code().isEmpty()) {
                    continue;
                }
                bodies++;
                for (CodeElement ce : mm.code().get()) {
                    if (ce instanceof InvokeInstruction inv) {
                        invokes++;
                        String owner = inv.owner().asInternalName();
                        String target = inv.name().stringValue() + inv.type().stringValue();
                        boolean ok = false;
                        if (inv.opcode() == Opcode.INVOKEVIRTUAL || inv.opcode() == Opcode.INVOKEINTERFACE) {
                            if (owner.equals("java/lang/String") || owner.equals("java/lang/Object") || owner.equals("java/lang/CharSequence")) {
                                Method tm = findInstanceMethod(owner, target);
                                ok = tm != null && (RepPinSupport.isRep(TerminalBodyKinds.implementingClass(rep, tm)) || e.contains(target));
                            }
                        }
                        if (!ok) {
                            violations.put(k + " " + nd, inv.opcode() + " " + owner + "." + target);
                        }
                    }
                }
            }
        }
        Assert.assertTrue("E_K bodies leaving E_K ∪ overrides: " + violations, violations.isEmpty());
        // non-vacuity: the 5 lazy coder() bodies + SV's coder/isLatin1/contentEquals(StringBuffer)/toString (no
        // invoke, aload_0; areturn); contentEquals(StringBuffer) calls this.contentEquals(CharSequence)
        Assert.assertEquals(9, bodies);
        Assert.assertTrue("no invoke scanned", invokes >= 1);
    }

    /** No value-null rep calls a String body through super (only the flat reps do, value-carrying). */
    @Test
    public void noValueNullRepCallsSuperIntoString() throws IOException {
        Set<String> hits = new TreeSet<>();
        for (String k : NON_FLAT_KINDS) {
            Class<?> rep = InlineCacheRegistry.getRepClass(k);
            for (MethodModel mm : parse(rep).methods()) {
                if (mm.code().isEmpty()) {
                    continue;
                }
                for (CodeElement ce : mm.code().get()) {
                    if (ce instanceof InvokeInstruction inv && inv.opcode() == Opcode.INVOKESPECIAL && inv.owner().asInternalName().equals("java/lang/String") &&
                                    !inv.name().stringValue().equals("<init>")) {
                        hits.add(rep.getSimpleName() + "#" + mm.methodName().stringValue() + " -> String." + inv.name().stringValue());
                    }
                }
            }
        }
        Assert.assertTrue("super calls into String bodies from value-null reps: " + hits, hits.isEmpty());
    }

    /**
     * The argument channels: every String target whose argument slot is a walk terminal and whose body runs with the rep
     * argument (equals; the compareTo bridge, which passes it to its internal REDIRECT site) is a deflection body
     * of the kind rule, and so are the REDIRECT targets mCSE and mCSC; the stock {@code compareTo(String)} is not
     * one (a rep argument reaches it only after mCSC's deflection); every other non-receiver slot is entered
     * (walked, so the walk's own tags carry it); the receiver slot of a stringy instance target is the terminal the kind
     * rule covers.
     */
    @Test
    public void argumentTerminalsAreDeflectionBodies() {
        int terminals = 0;
        int cmpTerminals = 0;
        for (Method m : String.class.getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers())) {
                continue;
            }
            String desc = TerminalBodyKinds.nameAndDescriptor(m).substring(m.getName().length());
            boolean eq = StringAtoms.equalsArgRow(true, 1, StringAtoms.isStringEquals(false, "java.lang.String", m.getName(), desc), true) == StringAtoms.EqArgRow.TERMINAL;
            boolean cmp = StringAtoms.isStringCompareTo(false, "java.lang.String", m.getName(), desc);
            StringAtoms.CmpArgRow row = StringAtoms.compareToArgRow(true, 1, cmp && "(Ljava/lang/String;)I".equals(desc), cmp && "(Ljava/lang/Object;)I".equals(desc), true);
            if (eq || row == StringAtoms.CmpArgRow.BRIDGE) {
                terminals++;
                Assert.assertTrue(m + " is an argument terminal but not a deflection body", TerminalBodyKinds.isDeflectionBody("java.lang.String", m.getName(), desc));
            } else if (row == StringAtoms.CmpArgRow.TERMINAL) {
                cmpTerminals++;
                Assert.assertFalse(m + ": the stock compareTo body never runs with a rep argument (REDIRECT -> mCSC)", TerminalBodyKinds.isDeflectionBody("java.lang.String", m.getName(), desc));
            }
        }
        Assert.assertEquals("equals(Object), compareTo(Object)", 2, terminals);
        Assert.assertEquals("compareTo(String)", 1, cmpTerminals);
        Assert.assertTrue(TerminalBodyKinds.isDeflectionBody("java.lang.String", "maybeCustomStringEquals", "(Ljava/lang/Object;)Z"));
        Assert.assertTrue(TerminalBodyKinds.isDeflectionBody("java.lang.String", "maybeCustomStringCompareTo", "(Ljava/lang/String;)I"));
        for (int slot = 1; slot < 4; slot++) {
            Assert.assertEquals(StringAtoms.SlotRow.ENTER, StringAtoms.invokeSlotRow(slot, true, false));
        }
        Assert.assertEquals(StringAtoms.SlotRow.TERMINAL, StringAtoms.invokeSlotRow(0, true, false));
        Assert.assertEquals(StringAtoms.SlotRow.CONCAT_OPERAND, StringAtoms.invokeSlotRow(1, false, true));
    }

    /** Lazy reps never reach the concat machinery: a lazy candidate used as a concat operand is rejected. */
    @Test
    public void lazyCandidateAsConcatOperandRejects() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex inner = concat(graph, "C.java:1", 2);
        SugVertex outer = concat(graph, "C.java:2", 1);
        graph.addEdge(inner, outer, SugEdgeType.CONCAT_LEFT, 1);
        SugVertex length = graph.newVertex();
        length.setNodeType(SugNodeType.STRING_METHOD_CALL);
        length.setMethodName("length");
        length.setDeclaringClass("java.lang.String");
        length.setSourceLocation("C.java:99");
        graph.addEdge(outer, length, SugEdgeType.DATAFLOW, 0);
        LazyConcatHeuristic h = new LazyConcatHeuristic();
        List<InstrumentationDecision> decisions = h.apply(graph);
        for (InstrumentationDecision d : decisions) {
            Assert.assertNotSame("the inner concat (a concat operand) must not be admitted", inner, d.getCandidate());
        }
        Assert.assertTrue(h.getRejections().toString(), h.getRejections().stream().anyMatch(r -> r.contains("concat expression @ C.java:2")));
    }

    private static SugVertex concat(StringUtilizationGraph graph, String loc, int literalOperands) {
        SugVertex c = graph.newVertex();
        c.setNodeType(SugNodeType.CONCAT_EXPRESSION);
        c.setSourceLocation(loc);
        c.setEnclosingClassName("TestUserClass");
        for (int i = 0; i < literalOperands; i++) {
            SugVertex op = graph.newVertex();
            op.setNodeType(SugNodeType.STRING_LITERAL);
            op.setLiteralText("o" + i);
            graph.addEdge(op, c, i == 0 ? SugEdgeType.CONCAT_LEFT : SugEdgeType.CONCAT_RIGHT, i);
        }
        return c;
    }

    /**
     * The Set overload lists exactly the given non-flat concat-operand kinds in the concat group and
     * leaves the other groups as the boolean overload does.
     */
    @Test
    public void kindSetConcatOperandKinds() {
        String substring = "java.lang.String#substring(I)Ljava/lang/String;@3";
        String coder = "java.lang.String#coder()B@4";
        String prepend = "java.lang.StringConcatHelper#prepend(JB[BLjava/lang/String;)J@2";
        String hidden = "java.lang.String$$StringConcat/0x1#concat(I)Ljava/lang/String;@3";
        List<String> admitted = List.of("ARRAY_LAZY", "FIXED4", "INTERLEAVED", "ROPE", "SBS", "SV", "THREE_WAY");
        Set<String> operandKinds = Set.of("SV", "ARRAY_LAZY");
        Assert.assertEquals(Set.of("ARRAY_LAZY", "SBS", "SV"), TerminalBodyKinds.kindSet(prepend, admitted, operandKinds));
        Assert.assertEquals(Set.of("ARRAY_LAZY", "SBS", "SV"), TerminalBodyKinds.kindSet(hidden, admitted, operandKinds));
        Assert.assertEquals(Set.of("SBS"), TerminalBodyKinds.kindSet(prepend, admitted, Set.of()));
        // every lazy rep that can be an operand (not ROPE) is listed when given
        Set<String> lazyKinds = Set.of("THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED");
        Assert.assertEquals(Set.of("ARRAY_LAZY", "FIXED4", "INTERLEAVED", "SBS", "THREE_WAY"), TerminalBodyKinds.kindSet(prepend, admitted, lazyKinds));
        // the other groups do not depend on the concat-operand kinds
        for (String key : List.of(substring, coder)) {
            Assert.assertEquals(key, TerminalBodyKinds.kindSet(key, admitted, false), TerminalBodyKinds.kindSet(key, admitted, operandKinds));
            Assert.assertEquals(key, TerminalBodyKinds.kindSet(key, admitted, false), TerminalBodyKinds.kindSet(key, admitted, lazyKinds));
        }
        // the boolean overload is the Set overload with {SV} / {}
        Assert.assertEquals(TerminalBodyKinds.kindSet(prepend, admitted, Set.of("SV")), TerminalBodyKinds.kindSet(prepend, admitted, true));
        Assert.assertEquals(TerminalBodyKinds.kindSet(prepend, admitted, Set.of()), TerminalBodyKinds.kindSet(prepend, admitted, false));
    }

    /** The rule itself on representative keys (LS / SV / all images). */
    @Test
    public void kindSetRule() {
        String substring = "java.lang.String#substring(I)Ljava/lang/String;@3";
        String coder = "java.lang.String#coder()B@4";
        String mcse = "java.lang.String#maybeCustomStringEquals(Ljava/lang/Object;)Z@30";
        String prepend = "java.lang.StringConcatHelper#prepend(JB[BLjava/lang/String;)J@2";
        String invoke = "java.lang.invoke.MethodType#toString()Ljava/lang/String;@10";
        List<String> ls = List.of("ARRAY_LAZY", "ROPE");
        Assert.assertEquals(Set.of(), TerminalBodyKinds.kindSet(substring, ls, false));
        Assert.assertEquals(Set.of("ARRAY_LAZY", "ROPE"), TerminalBodyKinds.kindSet(coder, ls, false));
        Assert.assertEquals(Set.of("ARRAY_LAZY", "ROPE"), TerminalBodyKinds.kindSet(mcse, ls, false));
        Assert.assertEquals(Set.of(), TerminalBodyKinds.kindSet(prepend, ls, false));
        // the concat group is the concat machinery only; the rest of java.lang.invoke is ordinary walked code
        Assert.assertNull(TerminalBodyKinds.kindSet(invoke, ls, false));
        Assert.assertNull(TerminalBodyKinds.kindSet("java.lang.invoke.InnerClassLambdaMetafactory#sanitizedTargetClassName(Ljava/lang/Class;)Ljava/lang/String;@17", List.of("SV"), true));
        Assert.assertFalse(StringAnalysisPolicy.isTerminalBodyClass("java.lang.invoke.InnerClassLambdaMetafactory"));
        Assert.assertFalse(StringAnalysisPolicy.isTerminalBodyClass("java.lang.invoke.MethodType"));
        Assert.assertTrue(StringAnalysisPolicy.isTerminalBodyClass("java.lang.invoke.StringConcatFactory$InlineHiddenClassStrategy"));
        Assert.assertTrue(StringAnalysisPolicy.isTerminalBodyClass("java.lang.StringConcatHelper"));
        Assert.assertEquals(Set.of("SV"), TerminalBodyKinds.kindSet("java.lang.invoke.StringConcatFactory$InlineHiddenClassStrategy#m()V@1", List.of("SV"), true));
        List<String> sv = List.of("SV");
        Assert.assertEquals(Set.of(), TerminalBodyKinds.kindSet(substring, sv, true));
        Assert.assertEquals(Set.of("SV"), TerminalBodyKinds.kindSet(prepend, sv, true));
        Assert.assertEquals(Set.of(), TerminalBodyKinds.kindSet(prepend, sv, false));
        Assert.assertEquals(Set.of("SV"), TerminalBodyKinds.kindSet(coder, sv, false));
        List<String> all = List.of("ROPE", "SBS", "SV");
        Assert.assertEquals(Set.of("SBS"), TerminalBodyKinds.kindSet(substring, all, true));
        Assert.assertEquals(Set.of("SBS", "SV"), TerminalBodyKinds.kindSet(prepend, all, true));
        Assert.assertEquals(Set.of("ROPE", "SBS", "SV"), TerminalBodyKinds.kindSet(mcse, all, true));
        // the hidden concat classes are concat machinery (their keys are per-build, so they never match a parent site)
        Assert.assertEquals(Set.of("SBS", "SV"), TerminalBodyKinds.kindSet("java.lang.String$$StringConcat/0x1#concat(I)Ljava/lang/String;@3", all, true));
        // not covered: String's nested classes, rep bodies, user code
        Assert.assertNull(TerminalBodyKinds.kindSet("java.lang.String$CaseInsensitiveComparator#compare(Ljava/lang/String;Ljava/lang/String;)I@3", all, true));
        Assert.assertNull(TerminalBodyKinds.kindSet("com.oracle.svm.core.stringrep.RopeString#length()I@1", all, true));
        Assert.assertNull(TerminalBodyKinds.kindSet("U#m()V@4", all, true));
        // the marker round trip
        Assert.assertEquals("KT:UNKNOWN", TerminalBodyKinds.markedVariant("UNKNOWN", Set.of(), Set.of()));
        Assert.assertEquals("KT:EXACT,SV,SBS", TerminalBodyKinds.markedVariant("EXACT,SV", Set.of("SV"), new TreeSet<>(Set.of("SBS", "SV"))));
        Assert.assertEquals("EXACT,SV", TerminalBodyKinds.stripMarker("KT:EXACT,SV"));
        Assert.assertNull(TerminalBodyKinds.stripMarker("EXACT,SV"));
    }

    private static Method stringMethod(String nameAndDescriptor) {
        for (Method m : String.class.getDeclaredMethods()) {
            if (TerminalBodyKinds.nameAndDescriptor(m).equals(nameAndDescriptor)) {
                return m;
            }
        }
        throw new AssertionError("no String method " + nameAndDescriptor);
    }

    private static Method findInstanceMethod(String owner, String nameAndDescriptor) {
        Class<?> c = switch (owner) {
            case "java/lang/String" -> String.class;
            case "java/lang/Object" -> Object.class;
            default -> CharSequence.class;
        };
        for (Class<?> k = c; k != null; k = k.getSuperclass()) {
            for (Method m : k.getDeclaredMethods()) {
                if (!Modifier.isStatic(m.getModifiers()) && TerminalBodyKinds.nameAndDescriptor(m).equals(nameAndDescriptor)) {
                    return m;
                }
            }
        }
        return null;
    }

    private static ClassModel parse(Class<?> c) throws IOException {
        try (InputStream in = c.getResourceAsStream(c.getSimpleName() + ".class")) {
            Assert.assertNotNull("class bytes of " + c, in);
            return ClassFile.of().parse(in.readAllBytes());
        }
    }
}
