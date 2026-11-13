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

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.io.InputStream;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

/**
 * The compareTo mirror: the site-keyed compareTo-argument row, the REDIRECT rule at compareTo
 * vertices (user sites and the bridge's internal site), the cross-rep compareTo conflict, the JDK premise (the stock
 * {@code String.compareTo} body without a rep check; the invented {@code maybeCustomStringCompareTo}) and the run-time
 * matrix of {@code maybeCustomStringCompareTo} over every receiver and argument kind.
 */
public class CompareToMirrorTest {

    // ---- the child's argument row (StringAtoms.compareToArgRow) ----

    @Test
    public void compareToArgRowTable() {
        // compareTo(String): TERMINAL at a Phase-A site, NO_SITE without one
        Assert.assertEquals(StringAtoms.CmpArgRow.TERMINAL, StringAtoms.compareToArgRow(true, 1, true, false, true));
        Assert.assertEquals(StringAtoms.CmpArgRow.NO_SITE, StringAtoms.compareToArgRow(true, 1, true, false, false));
        // the bridge: always BRIDGE (its internal site decides), whatever the call's own site
        Assert.assertEquals(StringAtoms.CmpArgRow.BRIDGE, StringAtoms.compareToArgRow(true, 1, false, true, true));
        Assert.assertEquals(StringAtoms.CmpArgRow.BRIDGE, StringAtoms.compareToArgRow(true, 1, false, true, false));
        // not an argument row: the receiver slot, another slot, a container atom, another target
        Assert.assertEquals(StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(true, 0, true, false, true));
        Assert.assertEquals(StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(true, 2, true, false, true));
        Assert.assertEquals(StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(false, 1, true, false, true));
        Assert.assertEquals(StringAtoms.CmpArgRow.NONE, StringAtoms.compareToArgRow(true, 1, false, false, true));
    }

    @Test
    public void noSiteRefusalIsAppendedLast() {
        RTrackRefusal[] all = RTrackRefusal.values();
        Assert.assertEquals("HIDDEN_SINK and MIRROR_ARG_NO_SITE are appended after it", RTrackRefusal.COMPARETO_ARG_NO_SITE, all[all.length - 3]);
        Assert.assertFalse(RTrackRefusal.COMPARETO_ARG_NO_SITE.budgetClass);
        Assert.assertEquals(TransferFacts.IncompleteReason.UNTRACKABLE_CONTAINER, RTrackRefusal.COMPARETO_ARG_NO_SITE.verdictReason());
    }

    // ---- the REDIRECT rule at compareTo vertices (EqualsMatrixHeuristic) ----

    private static SugVertex cmpVertex(StringUtilizationGraph graph, String signature, SugNodeType type, String enclosing, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(type);
        v.setMethodName("compareTo");
        v.setMethodSignature(signature);
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName(enclosing);
        v.setSourceLocation(loc);
        return v;
    }

    private static SugVertex substring(StringUtilizationGraph graph, String loc) {
        SugVertex v = graph.newVertex();
        v.setNodeType(SugNodeType.STRING_METHOD_CALL);
        v.setMethodName("substring");
        v.setDeclaringClass("java.lang.String");
        v.setEnclosingClassName("TestUserClass");
        v.setLength(5);
        v.setSourceLocation(loc);
        return v;
    }

    @Test
    public void compareToStringVertexPredicate() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        Assert.assertTrue(EqualsMatrixHeuristic.isCompareToStringCall(cmpVertex(g, "Ljava/lang/String;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@1")));
        // the bridge's internal call (a JDK_LIBRARY_CALL inside java.lang.String)
        Assert.assertTrue(EqualsMatrixHeuristic.isCompareToStringCall(cmpVertex(g, "Ljava/lang/String;", SugNodeType.JDK_LIBRARY_CALL, "java.lang.String",
                        "java.lang.String#compareTo(Ljava/lang/Object;)I@5")));
        Assert.assertFalse("the bridge's own call vertex", EqualsMatrixHeuristic.isCompareToStringCall(cmpVertex(g, "Ljava/lang/Object;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@2")));
        SugVertex other = cmpVertex(g, "Ljava/lang/String;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@3");
        other.setDeclaringClass("U");
        Assert.assertFalse("a user compareTo(String)", EqualsMatrixHeuristic.isCompareToStringCall(other));
        Assert.assertFalse("not an equals vertex", EqualsMatrixHeuristic.isEqualsObjectCall(cmpVertex(g, "Ljava/lang/String;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@4")));
    }

    /**
     * The child grants the argument terminal only at a vertex the REDIRECT rule marks
     * ({@code RecursiveTracking}'s direct crossing and {@code JdkModelEngine}'s internal sites; the real-IR rows are in
     * {@code StringAtomEndToEndTest}).
     */
    @Test
    public void redirectableArgSitePredicate() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex cmp = cmpVertex(g, "Ljava/lang/String;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@1");
        Assert.assertTrue(EqualsMatrixHeuristic.redirectableArgSite(cmp, true));
        Assert.assertFalse("not an equals site", EqualsMatrixHeuristic.redirectableArgSite(cmp, false));
        Assert.assertTrue("the bridge's internal call", EqualsMatrixHeuristic.redirectableArgSite(
                        cmpVertex(g, "Ljava/lang/String;", SugNodeType.JDK_LIBRARY_CALL, "java.lang.String", "java.lang.String#compareTo(Ljava/lang/Object;)I@5"), true));
        Assert.assertFalse("a Comparable.compareTo(Object) vertex", EqualsMatrixHeuristic.redirectableArgSite(
                        cmpVertex(g, "Ljava/lang/Object;", SugNodeType.STRING_METHOD_CALL, "U", "U#m@2"), true));
        Assert.assertFalse("no vertex", EqualsMatrixHeuristic.redirectableArgSite(null, true));
        Assert.assertFalse("no vertex", EqualsMatrixHeuristic.redirectableArgSite(null, false));
        SugVertex eq = g.newVertex();
        eq.setNodeType(SugNodeType.STRING_METHOD_CALL);
        eq.setMethodName("equals");
        eq.setDeclaringClass("java.lang.String");
        eq.setMethodSignature("Ljava/lang/Object;");
        Assert.assertTrue(EqualsMatrixHeuristic.redirectableArgSite(eq, false));
        Assert.assertFalse("not a compareTo site", EqualsMatrixHeuristic.redirectableArgSite(eq, true));
        SugVertex objectsEquals = g.newVertex();
        objectsEquals.setNodeType(SugNodeType.STRING_METHOD_CALL);
        objectsEquals.setMethodName("equals");
        objectsEquals.setDeclaringClass("java.lang.String");
        objectsEquals.setMethodSignature("(Ljava/lang/Object;)");
        Assert.assertFalse("the static Objects.equals vertex is never REDIRECTed", EqualsMatrixHeuristic.redirectableArgSite(objectsEquals, false));
        SugVertex concat = cmpVertex(g, "Ljava/lang/String;", SugNodeType.CONCAT_EXPRESSION, "U", "U#m@3");
        Assert.assertFalse("not a call vertex", EqualsMatrixHeuristic.redirectableArgSite(concat, true));
    }

    private static List<InstrumentationDecision> redirect(SugNodeType type, String enclosing, boolean receiver, boolean argument, boolean admitted) {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex sub = substring(g, "S#m@1");
        SugVertex c = cmpVertex(g, "Ljava/lang/String;", type, enclosing, "C#m@2");
        if (receiver) {
            g.addEdge(sub, c, SugEdgeType.QUALIFIER, -1);
        }
        if (argument) {
            g.addEdge(sub, c, SugEdgeType.PARAMETER, 1);
        }
        UsageSourceBuilder.build(g);
        Set<SugVertex> custom = new HashSet<>();
        if (admitted) {
            custom.add(sub);
        }
        return new EqualsMatrixHeuristic().apply(g, custom);
    }

    @Test
    public void admittedRepArgumentRedirectsCompareTo() {
        List<InstrumentationDecision> d = redirect(SugNodeType.STRING_METHOD_CALL, "TestUserClass", false, true, true);
        Assert.assertEquals(1, d.size());
        Assert.assertEquals(OptimizationType.EQUALS_MATRIX, d.get(0).getType());
        Assert.assertEquals(EqualsMatrixHeuristic.VARIANT_REDIRECT, d.get(0).getVariant());
        // the bridge's internal site: image-wide, like HashMap#getNode for equals
        d = redirect(SugNodeType.JDK_LIBRARY_CALL, "java.lang.String", false, true, true);
        Assert.assertEquals(1, d.size());
        Assert.assertEquals(EqualsMatrixHeuristic.VARIANT_REDIRECT, d.get(0).getVariant());
    }

    @Test
    public void receiverOnlyOrNotAdmittedIsFastPath() {
        Assert.assertTrue("a rep receiver runs its own compareTo", redirect(SugNodeType.STRING_METHOD_CALL, "TestUserClass", true, false, true).isEmpty());
        Assert.assertTrue("a REJECTed candidate is a plain String", redirect(SugNodeType.STRING_METHOD_CALL, "TestUserClass", false, true, false).isEmpty());
    }

    // ---- the cross-rep compareTo conflict (HeuristicOrchestrator) ----

    private static HeuristicOrchestrator conflict(String recvVariant, OptimizationType recvType, String argVariant, OptimizationType argType, List<SugVertex> out) {
        StringUtilizationGraph g = new StringUtilizationGraph();
        SugVertex recv = substring(g, "R.java:1");
        SugVertex arg = g.newVertex();
        if (argType == OptimizationType.LAZY_CONCAT) {
            arg.setNodeType(SugNodeType.CONCAT_EXPRESSION);
            arg.setLength(10);
            arg.setEnclosingClassName("TestUserClass");
            arg.setSourceLocation("A.java:1");
        } else {
            arg = substring(g, "A.java:1");
        }
        SugVertex c = cmpVertex(g, "Ljava/lang/String;", SugNodeType.STRING_METHOD_CALL, "TestUserClass", "K.java:1");
        g.addEdge(recv, c, SugEdgeType.QUALIFIER, -1);
        g.addEdge(arg, c, SugEdgeType.PARAMETER, 1);
        UsageSourceBuilder.build(g);
        InstrumentationDecision rd = new InstrumentationDecision(recv, recvType, recvVariant);
        InstrumentationDecision ad = new InstrumentationDecision(arg, argType, argVariant);
        List<InstrumentationDecision> sv = new ArrayList<>();
        List<InstrumentationDecision> lc = new ArrayList<>();
        (recvType == OptimizationType.STRING_VIEW ? sv : lc).add(rd);
        (argType == OptimizationType.STRING_VIEW ? sv : lc).add(ad);
        HeuristicOrchestrator o = new HeuristicOrchestrator(g);
        o.run(Collections.emptyList(), sv, lc, Collections.emptyList(), Collections.emptyList());
        out.add(recv);
        out.add(arg);
        return o;
    }

    @Test
    public void differentRepsAtACompareToSiteConflict() {
        List<SugVertex> vs = new ArrayList<>();
        HeuristicOrchestrator o = conflict(null, OptimizationType.STRING_VIEW, "ROPE", OptimizationType.LAZY_CONCAT, vs);
        Assert.assertEquals(1, o.getValidatedDecisions().size());
        Assert.assertEquals(OptimizationType.STRING_VIEW, o.getValidatedDecisions().get(0).getType());
        Assert.assertEquals(1, o.getConflicts().size());
        Assert.assertTrue(o.getConflicts().get(0), o.getConflicts().get(0).startsWith("REJECT V" + vs.get(1).getId() + " (concat @ A.java:1): cross-rep compareTo conflict at K.java:1 ("));
    }

    @Test
    public void sameRepAtACompareToSiteIsNoConflict() {
        HeuristicOrchestrator o = conflict(null, OptimizationType.STRING_VIEW, null, OptimizationType.STRING_VIEW, new ArrayList<>());
        Assert.assertEquals(2, o.getValidatedDecisions().size());
        Assert.assertTrue(o.getConflicts().isEmpty());
    }

    // ---- the JDK premise (the builder JDK's String) ----

    private static ClassModel stringClass() throws Exception {
        try (InputStream in = Object.class.getResourceAsStream("/java/lang/String.class")) {
            return ClassFile.of().parse(in.readAllBytes());
        }
    }

    private static MethodModel method(ClassModel cm, String name, String desc) {
        for (MethodModel m : cm.methods()) {
            if (m.methodName().equalsString(name) && m.methodType().equalsString(desc)) {
                return m;
            }
        }
        throw new AssertionError("no " + name + desc);
    }

    private static List<CodeElement> code(MethodModel m) {
        return m.findAttribute(Attributes.code()).map(c -> ((CodeModel) c).elementList()).orElseThrow();
    }

    /**
     * The stock body: {@code compareTo(String)} reads both {@code value()}s and dispatches on the coder; no null test (no
     * deflection {@code if (v2 == null) return -anotherString.compareTo(this)} in the body) and no call back into
     * {@code compareTo}.
     */
    @Test
    public void stockCompareToHasNoRepCheck() throws Exception {
        List<String> calls = new ArrayList<>();
        for (CodeElement e : code(method(stringClass(), "compareTo", "(Ljava/lang/String;)I"))) {
            if (e instanceof BranchInstruction br) {
                Assert.assertFalse("a null test in String.compareTo: " + br.opcode(), br.opcode() == Opcode.IFNULL || br.opcode() == Opcode.IFNONNULL);
            }
            if (e instanceof InvokeInstruction inv) {
                calls.add(inv.owner().asInternalName() + "." + inv.name().stringValue());
            }
        }
        Assert.assertFalse("String.compareTo calls compareTo: " + calls, calls.contains("java/lang/String.compareTo"));
        Assert.assertTrue(calls.toString(), calls.contains("java/lang/String.value") && calls.contains("java/lang/StringLatin1.compareTo"));
    }

    /**
     * The invented {@code maybeCustomStringCompareTo(String)}: {@code @ForceInline}, public, non-final (a value-null rep
     * overrides it), and its body deflects every argument whose class is not {@code String} to
     * {@code -another.compareTo(this)}, else calls {@code compareTo(another)} virtually.
     */
    @Test
    public void maybeCustomStringCompareToShape() throws Exception {
        Method m = String.class.getDeclaredMethod("maybeCustomStringCompareTo", String.class);
        Assert.assertTrue(Modifier.isPublic(m.getModifiers()) && !Modifier.isFinal(m.getModifiers()) && !Modifier.isStatic(m.getModifiers()));
        MethodModel mm = method(stringClass(), "maybeCustomStringCompareTo", "(Ljava/lang/String;)I");
        boolean forceInline = mm.findAttribute(Attributes.runtimeVisibleAnnotations()).map(a -> a.annotations().stream().anyMatch(an -> an.className().equalsString(
                        "Ljdk/internal/vm/annotation/ForceInline;"))).orElse(false);
        Assert.assertTrue("@ForceInline", forceInline);
        List<String> ops = new ArrayList<>();
        for (CodeElement e : code(mm)) {
            if (e instanceof InvokeInstruction inv) {
                ops.add(inv.opcode() + " " + inv.owner().asInternalName() + "." + inv.name().stringValue());
            } else if (e instanceof java.lang.classfile.Instruction ins) {
                ops.add(ins.opcode().toString());
            }
        }
        Assert.assertEquals(Arrays.asList("ALOAD_1", "INVOKEVIRTUAL java/lang/Object.getClass", "LDC", "IF_ACMPEQ", "ALOAD_1", "ALOAD_0",
                        "INVOKEVIRTUAL java/lang/String.compareTo", "INEG", "IRETURN", "ALOAD_0", "ALOAD_1", "INVOKEVIRTUAL java/lang/String.compareTo", "IRETURN"), ops);
    }

    /** Every value-null rep overrides mCSC (the inherited deflection would run the stock body on a flat argument). */
    @Test
    public void everyValueNullRepOverridesMaybeCustomStringCompareTo() throws Exception {
        Method mcsc = String.class.getDeclaredMethod("maybeCustomStringCompareTo", String.class);
        int valueNull = 0;
        for (Class<?> rep : RepPinSupport.repClasses()) {
            boolean flat = InlineCacheRegistry.isValueCarryingFlatRep(rep);
            Class<?> impl = TerminalBodyKinds.implementingClass(rep, mcsc);
            if (flat) {
                Assert.assertSame(rep + " (flat) inherits mCSC", String.class, impl);
            } else {
                valueNull++;
                Assert.assertSame(rep + " must override mCSC", rep, impl);
                Assert.assertTrue(InlineCacheRegistry.repOverrides(rep, "maybeCustomStringCompareTo"));
            }
        }
        Assert.assertEquals(6, valueNull);
    }

    // ---- the run-time matrix (JVM): mCSC and every rep's own compareTo are the JVM result for every pair ----

    @Test
    public void maybeCustomStringCompareToMatrix() {
        List<RepEqualsMatrixTest.Inst> all = RepEqualsMatrixTest.instances();
        int pairs = 0;
        int deflected = 0;
        for (RepEqualsMatrixTest.Inst r : all) {
            for (RepEqualsMatrixTest.Inst a : all) {
                int expected = r.content().compareTo(a.content());
                Assert.assertEquals(r.label() + ".mCSC(" + a.label() + ")", expected, r.s().maybeCustomStringCompareTo(a.s()));
                if (r.s().getClass() != String.class && !InlineCacheRegistry.isValueCarryingFlatRep(r.s().getClass())) {
                    // the IC chain's arm: the rep's own compareTo, for every argument class
                    Assert.assertEquals(r.label() + ".compareTo(" + a.label() + ")", expected, r.s().compareTo(a.s()));
                }
                deflected += a.s().getClass() != String.class ? 1 : 0;
                pairs++;
            }
        }
        Assert.assertTrue("vacuous matrix", pairs > 1000 && deflected > 500);
        try {
            "a".maybeCustomStringCompareTo(null);
            Assert.fail("a null argument must throw NullPointerException, as String.compareTo does");
        } catch (NullPointerException expected) {
            // as stock
        }
    }

    /**
     * The hazard the REDIRECT removes (not executed: on HotSpot the C2 {@code String.compareTo} intrinsic dereferences the
     * null array without a check, a VM crash rather than an NPE): a plain receiver's stock body reads the argument's
     * {@code value()}, null for a value-null rep. mCSC deflects before it.
     */
    @Test
    public void maybeCustomStringCompareToDeflectsAValueNullRep() {
        String rope = com.oracle.svm.core.stringrep.RopeString.create("ab", "c");
        Assert.assertFalse("a value-null rep", InlineCacheRegistry.isValueCarryingFlatRep(rope.getClass()));
        Assert.assertEquals(0, "abc".maybeCustomStringCompareTo(rope));
        Assert.assertEquals(-1, "abb".maybeCustomStringCompareTo(rope));
        Assert.assertEquals(1, "abcd".maybeCustomStringCompareTo(rope));
    }
}
