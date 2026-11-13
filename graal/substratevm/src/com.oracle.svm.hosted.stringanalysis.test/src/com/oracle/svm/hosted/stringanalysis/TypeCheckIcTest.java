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
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.LogicConstantNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ShortCircuitOrNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.MetaAccessProvider;

/**
 * The type-check IC: the child's variant rule (observations, depth cut,
 * kind-terminal, flat closure), the line format and the loader, the parent's decision function (mode x list cap x variant x kind x
 * terminal-body site), the emitted condition shapes, the model-body exclusion and the knob defaults.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.spi"})
public class TypeCheckIcTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    private static InlineCacheProfilingHeuristic.RepFacts facts(boolean any, boolean cut, Set<String> exact, Set<String> custom) {
        return new InlineCacheProfilingHeuristic.RepFacts(any, cut, exact, custom);
    }

    @Test
    public void variantIsTheIcReceiverRule() {
        Assert.assertEquals("no observation", "UNKNOWN", TypeCheckSites.variant(facts(false, false, Set.of(), Set.of()), null, false).text());
        Assert.assertEquals("plain Strings only", "EXACT_STRING", TypeCheckSites.variant(facts(true, false, Set.of("EXACT"), Set.of()), null, false).text());
        Assert.assertEquals("a rep only", "SV", TypeCheckSites.variant(facts(true, false, Set.of(), Set.of("SV")), null, false).text());
        Assert.assertEquals("EXACT,SV", TypeCheckSites.variant(facts(true, false, Set.of("EXACT"), Set.of("SV")), null, false).text());
        Assert.assertEquals("a depth cut", InlineCacheProfilingHeuristic.UNPROVEN, TypeCheckSites.variant(facts(true, true, Set.of("EXACT"), Set.of("SV")), null, false).text());
    }

    @Test
    public void ktAndFlatClosure() {
        Assert.assertEquals("KT, no admitted kind", "KT:UNKNOWN", TypeCheckSites.variant(facts(false, false, Set.of(), Set.of()), Set.of(), false).text());
        Assert.assertEquals("KT kinds united", "KT:EXACT,SV,SBS", TypeCheckSites.variant(facts(true, false, Set.of("EXACT"), Set.of("SV")), Set.of("SBS"), false).text());
        Assert.assertEquals("KT keeps UNPROVEN", "KT:UNPROVEN", TypeCheckSites.variant(facts(true, true, Set.of(), Set.of()), Set.of("SBS"), false).text());
        TypeCheckSites.Variant v = TypeCheckSites.variant(facts(false, false, Set.of(), Set.of()), null, true);
        Assert.assertEquals("the flat closure lists SBS at a rep-free site", "EXACT,SBS", v.text());
        Assert.assertTrue(v.flatClosureAdded());
        v = TypeCheckSites.variant(facts(true, false, Set.of(), Set.of("SBS")), null, true);
        Assert.assertEquals("already listed", "SBS", v.text());
        Assert.assertFalse(v.flatClosureAdded());
        Assert.assertEquals("UNPROVEN stays", InlineCacheProfilingHeuristic.UNPROVEN, TypeCheckSites.variant(facts(true, true, Set.of(), Set.of()), null, true).text());
        Assert.assertEquals("KT + closure", "KT:EXACT,SBS", TypeCheckSites.variant(facts(false, false, Set.of(), Set.of()), Set.of(), true).text());
    }

    @Test
    public void repNamesAndLineShape() {
        Assert.assertEquals(List.of(), TypeCheckSites.repNames("UNKNOWN"));
        Assert.assertEquals(List.of(), TypeCheckSites.repNames("KT:EXACT_STRING"));
        Assert.assertEquals(List.of("SV", "SBS"), TypeCheckSites.repNames("KT:EXACT,SV,SBS"));
        Assert.assertNull(TypeCheckSites.repNames("UNPROVEN"));
        Assert.assertNull(TypeCheckSites.repNames("KT:UNPROVEN"));
        Assert.assertNull(TypeCheckSites.repNames("SV,,SBS"));
        Assert.assertTrue(TypeCheckLines.isLine("a.B#m()V@3 TYPE_CHECK CAST UNKNOWN".split(" ")));
        Assert.assertTrue(TypeCheckLines.isLine("a.B#m()V@3 TYPE_CHECK INST KT:UNPROVEN".split(" ")));
        Assert.assertFalse("kind token", TypeCheckLines.isLine("a.B#m()V@3 TYPE_CHECK CHECKCAST UNKNOWN".split(" ")));
        Assert.assertFalse("key", TypeCheckLines.isLine("a.B#m()V TYPE_CHECK CAST UNKNOWN".split(" ")));
        Assert.assertFalse("arity", TypeCheckLines.isLine("a.B#m()V@3 TYPE_CHECK CAST".split(" ")));
    }

    @Test
    public void exclusions() {
        Assert.assertEquals("hidden", TypeCheckSites.exclusion("p.C", true, false, false));
        Assert.assertEquals("rep", TypeCheckSites.exclusion("com.oracle.svm.core.stringrep.StringView", false, false, false));
        Assert.assertEquals("string-nested", TypeCheckSites.exclusion("java.lang.String$CaseInsensitiveComparator", false, false, false));
        Assert.assertEquals("custom-graph", TypeCheckSites.exclusion("p.C", false, true, false));
        Assert.assertEquals("model-body", TypeCheckSites.exclusion("p.C", false, false, true));
        Assert.assertNull(TypeCheckSites.exclusion("java.lang.String", false, false, false));
        Assert.assertTrue("a model entry", JdkModels.modelBodyMethod("java.util.ArrayList", "java.util.ArrayList#add(Ljava/lang/Object;)Z"));
        Assert.assertTrue("a closed class", JdkModels.modelBodyMethod("java.util.HashMap$Node", "java.util.HashMap$Node#getKey()Ljava/lang/Object;"));
        Assert.assertFalse("String bodies are walked or KT", JdkModels.modelBodyMethod("java.lang.String", "java.lang.String#equals(Ljava/lang/Object;)Z"));
        Assert.assertFalse("user code", JdkModels.modelBodyMethod("p.C", "p.C#m()V"));
    }

    private static String ex(String cls, String mid, boolean inlined, boolean nonOutermost) {
        return TypeCheckSites.exclusion(cls, mid, false, false, false, inlined, nonOutermost);
    }

    /** compute's method-level site classification (inlined / non-outermost, terminal bodies). */
    @Test
    public void siteClassification() {
        Assert.assertNull("user code", ex("p.C", "p.C#conv(Ljava/lang/Object;)Ljava/lang/String;", false, false));
        Assert.assertEquals("B-1: inlined before the analysis anywhere", "inlined", ex("p.C", "p.C#conv(Ljava/lang/Object;)Ljava/lang/String;", true, false));
        Assert.assertEquals("B-1: a check seen at a non-outermost position", "non-outermost", ex("p.C", "p.C#conv(Ljava/lang/Object;)Ljava/lang/String;", false, true));
        Assert.assertEquals("the class exclusions come first", "model-body",
                        TypeCheckSites.exclusion("java.util.ArrayList", "java.util.ArrayList#add(Ljava/lang/Object;)Z", false, false, true, true, true));
        Assert.assertEquals("hidden", TypeCheckSites.exclusion("p.C", "p.C#m()V", true, false, false, true, false));
        // terminal bodies: a line only in a deflection body
        Assert.assertNull("equals deflects its argument", ex("java.lang.String", "java.lang.String#equals(Ljava/lang/Object;)Z", false, false));
        Assert.assertNull("compareTo(Object)", ex("java.lang.String", "java.lang.String#compareTo(Ljava/lang/Object;)I", false, false));
        Assert.assertNull("mCSE", ex("java.lang.String", "java.lang.String#maybeCustomStringEquals(Ljava/lang/Object;)Z", false, false));
        Assert.assertEquals("m-1: contentEquals checks its argument", "terminal-non-deflection",
                        ex("java.lang.String", "java.lang.String#contentEquals(Ljava/lang/CharSequence;)Z", false, false));
        Assert.assertEquals("compareTo(String) is no deflection body", "terminal-non-deflection", ex("java.lang.String", "java.lang.String#compareTo(Ljava/lang/String;)I", false, false));
        Assert.assertEquals("a CharSequence default body", "terminal-non-deflection", ex("java.lang.CharSequence", "java.lang.CharSequence#compare(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)I",
                        false, false));
        Assert.assertEquals("the concat machinery", "terminal-non-deflection", ex("java.lang.StringConcatHelper", "java.lang.StringConcatHelper#stringOf(Ljava/lang/Object;)Ljava/lang/String;", false,
                        false));
        Assert.assertEquals("inlined wins over the terminal rule", "inlined", ex("java.lang.String", "java.lang.String#equals(Ljava/lang/Object;)Z", true, false));
    }

    /**
     * The inlined exclusion is per key. Two candidates sharing a method id (the same FQN in two loaders), one of
     * them inlined: neither gets a line; an unrelated candidate keeps its classification.
     */
    @Test
    public void inlinedExclusionIsPerKey() {
        record C(String mid, boolean inlined) {
        }
        String shared = "p.C#conv(Ljava/lang/Object;)Ljava/lang/String;";
        String other = "p.D#conv(Ljava/lang/Object;)Ljava/lang/String;";
        List<C> cands = List.of(new C(shared, false), new C(shared, true), new C(other, false));
        Set<String> inlined = TypeCheckSites.inlinedMids(cands, C::mid, C::inlined);
        Assert.assertEquals(Set.of(shared), inlined);
        for (C c : cands) {
            String why = ex("p.C", c.mid(), inlined.contains(c.mid()), false);
            Assert.assertEquals(c.toString(), c.mid().equals(shared) ? "inlined" : null, why);
        }
    }

    /**
     * The String type-check sites of String's and CharSequence's own methods in this JDK. Every one
     * outside an argument-deflection body gets no line, so a new
     * {@code checkcast}/{@code instanceof String} in a String body is stock by construction.
     */
    @Test
    public void terminalBodySitesOutsideDeflectionBodiesGetNoLine() {
        java.util.Map<String, String> outcome = new java.util.TreeMap<>();
        Set<String> kept = new java.util.TreeSet<>();
        for (Class<?> c : List.of(String.class, CharSequence.class)) {
            jdk.vm.ci.meta.ResolvedJavaType t = META.lookupJavaType(c);
            List<jdk.vm.ci.meta.ResolvedJavaMethod> ms = new java.util.ArrayList<>(List.of(t.getDeclaredMethods(false)));
            ms.addAll(List.of(t.getDeclaredConstructors(false)));
            for (jdk.vm.ci.meta.ResolvedJavaMethod m : ms) {
                java.util.Map<Integer, Integer> bc = TypeCheckSites.stringTypeCheckBcis(m);
                if (bc.isEmpty()) {
                    continue;
                }
                String mid = TypeCheckSites.methodId(m);
                String why = ex(c.getName(), mid, false, false);
                outcome.put(mid + bc.keySet(), String.valueOf(why));
                boolean deflection = TerminalBodyKinds.isDeflectionBody(c.getName(), m.getName(), m.getSignature().toMethodDescriptor());
                Assert.assertEquals(mid, deflection ? null : "terminal-non-deflection", why);
                if (why == null) {
                    // every check kept in a deflection body is on an argument (the kind-terminal kind set covers the
                    // receiver and the deflection arguments, not other values): the value checked is a parameter load
                    for (int bci : bc.keySet()) {
                        int slot = loadedParameterSlotBefore(m, bci);
                        Assert.assertTrue(mid + "@" + bci + ": the checked value is an argument (slot " + slot + ")", slot >= (m.isStatic() ? 0 : 1) && slot < parameterSlots(m));
                        kept.add(mid.substring(mid.indexOf('#') + 1, mid.indexOf('(')) + mid.substring(mid.indexOf('('), mid.indexOf(')') + 1) + "@" + bci);
                    }
                }
            }
        }
        System.out.println("[typecheck] terminal-body String checks: " + outcome);
        Assert.assertEquals("the sites kept in deflection bodies (a new one must be reviewed)",
                        Set.of("compareTo(Ljava/lang/Object;)@2", "equals(Ljava/lang/Object;)@8", "equals(Ljava/lang/Object;)@15",
                                        "maybeCustomStringEquals(Ljava/lang/Object;)@8", "maybeCustomStringEquals(Ljava/lang/Object;)@15"),
                        kept);
        for (String six : List.of("contentEquals(Ljava/lang/CharSequence;)Z", "split(CIZ)", "indent(I)", "stripIndent()", "outdent(", "objectMaybeCustomStringEquals(")) {
            Assert.assertTrue("site present and excluded: " + six + " in " + outcome,
                            outcome.entrySet().stream().anyMatch(e -> e.getKey().contains("#" + six) && e.getValue().equals("terminal-non-deflection")));
        }
    }

    /** The local slot an {@code aload} immediately before {@code bci} loads, else -1. */
    private static int loadedParameterSlotBefore(jdk.vm.ci.meta.ResolvedJavaMethod m, int bci) {
        jdk.graal.compiler.bytecode.BytecodeStream s = new jdk.graal.compiler.bytecode.BytecodeStream(m.getCode());
        int prevOp = -1;
        int prevSlot = -1;
        while (s.currentBC() != jdk.graal.compiler.bytecode.Bytecodes.END && s.currentBCI() < bci) {
            prevOp = s.currentBC();
            prevSlot = prevOp == jdk.graal.compiler.bytecode.Bytecodes.ALOAD ? s.readLocalIndex() : -1;
            s.next();
        }
        if (s.currentBCI() != bci) {
            return -1;
        }
        return switch (prevOp) {
            case jdk.graal.compiler.bytecode.Bytecodes.ALOAD_0 -> 0;
            case jdk.graal.compiler.bytecode.Bytecodes.ALOAD_1 -> 1;
            case jdk.graal.compiler.bytecode.Bytecodes.ALOAD_2 -> 2;
            case jdk.graal.compiler.bytecode.Bytecodes.ALOAD_3 -> 3;
            case jdk.graal.compiler.bytecode.Bytecodes.ALOAD -> prevSlot;
            default -> -1;
        };
    }

    private static int parameterSlots(jdk.vm.ci.meta.ResolvedJavaMethod m) {
        int slots = m.isStatic() ? 0 : 1;
        for (int i = 0; i < m.getSignature().getParameterCount(false); i++) {
            slots += m.getSignature().getParameterKind(i).getSlotCount();
        }
        return slots;
    }

    /** The flat closure is on only when the profile records an undelivered hand-off. */
    @Test
    public void flatClosureOnlyForUndeliveredHandOffs() {
        Assert.assertFalse("delivered, none undelivered", TypeCheckSites.flatClosure(List.of()));
        Assert.assertFalse(TypeCheckSites.flatClosure(null));
        Assert.assertTrue("an undelivered hand-off recorded", TypeCheckSites.flatClosure(List.of("# FLAT_HANDOFF_UNDELIVERED toLowerCase() 1")));
        Assert.assertEquals("closure on: every non-UNPROVEN line lists SBS", "EXACT,SBS",
                        TypeCheckSites.variant(facts(true, false, Set.of("EXACT"), Set.of()), null, true).text());
    }

    /** An observation at a non-outermost position records its method (excluded) and keys nothing. */
    @Test
    public void nonOutermostObservationIsRecorded() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        jdk.vm.ci.meta.ResolvedJavaMethod outer = META.lookupJavaMethod(TypeCheckIcTest.class.getDeclaredMethod("holder", Object.class));
        jdk.vm.ci.meta.ResolvedJavaMethod inner = META.lookupJavaMethod(TypeCheckIcTest.class.getDeclaredMethod("conv", Object.class));
        StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(outer).trackNodeSourcePosition(true).build();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
        TypeReference str = TypeReference.createTrusted(g.getAssumptions(), META.lookupJavaType(String.class));
        InstanceOfNode own = g.addWithoutUnique((InstanceOfNode) InstanceOfNode.create(str, p));
        own.setNodeSourcePosition(new jdk.graal.compiler.graph.NodeSourcePosition(null, outer, 0));
        InstanceOfNode copy = g.addWithoutUnique((InstanceOfNode) InstanceOfNode.create(str, p));
        copy.setNodeSourcePosition(new jdk.graal.compiler.graph.NodeSourcePosition(new jdk.graal.compiler.graph.NodeSourcePosition(null, outer, 1), inner, 1));
        TypeCheckSites.NON_OUTERMOST_OBSERVED.clear();
        Assert.assertEquals(SiteKeys.profileKey(outer, 0), TypeCheckSites.observationKey(own, p));
        Assert.assertTrue(TypeCheckSites.NON_OUTERMOST_OBSERVED.isEmpty());
        Assert.assertNull("an inlined copy keys nothing", TypeCheckSites.observationKey(copy, p));
        Assert.assertEquals("the inlined method is recorded", Set.of(TypeCheckSites.methodId(inner)), TypeCheckSites.NON_OUTERMOST_OBSERVED);
        Assert.assertEquals(SiteKeys.profileKey(inner, 0).replace("@0", ""), TypeCheckSites.methodId(inner));
        TypeCheckSites.NON_OUTERMOST_OBSERVED.clear();
    }

    static String conv(Object o) {
        return (String) o;
    }

    private static Path profile(String... lines) throws IOException {
        Path p = Files.createTempFile("c98tc", ".txt");
        Files.write(p, List.of(lines));
        p.toFile().deleteOnExit();
        return p;
    }

    @Test
    public void loader() throws IOException {
        String k = "p.C#m(Ljava/lang/Object;)V@5";
        RepresentationProfile rp = RepresentationProfileLoader.load(profile("# FLAT_HANDOFF_UNDELIVERED toLowerCase() 3", k + " TYPE_CHECK CAST EXACT,SV", k + " TYPE_CHECK CAST EXACT,SV",
                        "p.C#m(Ljava/lang/Object;)V@9 TYPE_CHECK INST UNKNOWN").toString());
        Assert.assertEquals("CAST EXACT,SV", rp.getTypeCheck(k));
        Assert.assertEquals("INST UNKNOWN", rp.getTypeCheck("p.C#m(Ljava/lang/Object;)V@9"));
        Assert.assertNull(rp.getTypeCheck("p.C#m(Ljava/lang/Object;)V@7"));
        Assert.assertTrue("TYPE_CHECK lines are not decisions", rp.getAllEntries().isEmpty());
        Assert.assertTrue("TYPE_CHECK lines do not make an image admit a rep", rp.admitsNoRep());
        try {
            RepresentationProfileLoader.load(profile(k + " TYPE_CHECK CAST SV", k + " TYPE_CHECK CAST UNKNOWN").toString());
            Assert.fail("a conflicting duplicate");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("Conflicting TYPE_CHECK"));
        }
        try {
            RepresentationProfileLoader.load(profile(k + " TYPE_CHECK CAST").toString());
            Assert.fail("a malformed line");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("Invalid TYPE_CHECK"));
        }
    }

    private static TypeCheckIcNodePlugin.Decision d(int mode, int cap, String line, boolean cast, boolean terminal) {
        return TypeCheckIcNodePlugin.decide(mode, cap, line, cast, terminal);
    }

    @Test
    public void parentDecision() {
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_OFF, d(0, 2, "CAST UNKNOWN", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_NO_LINE, d(1, 2, null, true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_EXACT, d(1, 0, "CAST UNKNOWN", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_EXACT, d(2, 0, "INST EXACT_STRING", false, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_KIND_MISMATCH, d(1, 0, "CAST UNKNOWN", false, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_KIND_MISMATCH, d(1, 0, "INST UNKNOWN", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_UNPROVEN, d(1, 2, "CAST UNPROVEN", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_UNPROVEN, d(1, 2, "CAST KT:UNPROVEN", true, true));
        Assert.assertEquals("list cap 0: rep-free sites only", TypeCheckIcNodePlugin.Decision.STOCK_LIST_CAP, d(1, 0, "CAST EXACT,SV", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_LIST, d(1, 1, "CAST EXACT,SV", true, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_LIST_CAP, d(1, 1, "INST SV,SBS", false, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_LIST, d(1, 2, "INST SV,SBS", false, false));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.STOCK_UNKNOWN_REP, d(1, 2, "CAST EXACT,NOPE", true, false));
        Assert.assertEquals("terminal body: only KT lines", TypeCheckIcNodePlugin.Decision.STOCK_KT_ONLY, d(1, 2, "CAST UNKNOWN", true, true));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_EXACT, d(1, 2, "CAST KT:UNKNOWN", true, true));
        Assert.assertEquals(TypeCheckIcNodePlugin.Decision.LOWER_LIST, d(1, 2, "INST KT:EXACT,SV,SBS", false, true));
        Assert.assertEquals("a marked line outside a terminal body is read stripped (the IC siteVariant rule)", TypeCheckIcNodePlugin.Decision.LOWER_EXACT,
                        d(1, 2, "CAST KT:UNKNOWN", true, false));
        Assert.assertEquals(List.of("SV", "SBS"), TypeCheckIcNodePlugin.lineReps("INST KT:EXACT,SV,SBS"));
    }

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    @Test
    public void emittedConditionShapes() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(TypeCheckIcTest.class.getDeclaredMethod("holder", Object.class))).build();
        ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object())));
        LogicNode cast = g.addOrUniqueWithInputs(TypeCheckIcNodePlugin.exactCondition(META, p, List.of(), true));
        Assert.assertTrue(cast instanceof InstanceOfNode);
        InstanceOfNode ion = (InstanceOfNode) cast;
        Assert.assertTrue("exact String", ion.type().isExact() && ion.type().getType().equals(META.lookupJavaType(String.class)));
        Assert.assertTrue("a cast passes null", ion.allowsNull());
        LogicNode inst = g.addOrUniqueWithInputs(TypeCheckIcNodePlugin.exactCondition(META, p, List.of(), false));
        Assert.assertFalse("instanceof is false on null", ((InstanceOfNode) inst).allowsNull());
        LogicNode list = g.addOrUniqueWithInputs(TypeCheckIcNodePlugin.exactCondition(META, p, List.of(StringView.class, SingleByteString.class), true));
        Assert.assertTrue(list instanceof ShortCircuitOrNode);
        ShortCircuitOrNode outer = (ShortCircuitOrNode) list;
        Assert.assertTrue(outer.getY() instanceof InstanceOfNode y && y.type().isExact() && y.type().getType().equals(META.lookupJavaType(SingleByteString.class)) && !y.allowsNull());
        Assert.assertTrue(outer.getX() instanceof ShortCircuitOrNode inner && inner.getX() == cast && inner.getY() instanceof InstanceOfNode sv &&
                        sv.type().getType().equals(META.lookupJavaType(StringView.class)));
        Assert.assertEquals("k + 1 hub compares, no range check", 4, g.getNodes().filter(InstanceOfNode.class).count());
        ConstantNode nul = ConstantNode.forConstant(JavaConstant.NULL_POINTER, META, g);
        Assert.assertTrue("cast of null: stock (passes)", TypeCheckIcNodePlugin.exactCondition(META, nul, List.of(), true) instanceof LogicConstantNode c && c.getValue());
        Assert.assertTrue("instanceof of null: stock (false)", TypeCheckIcNodePlugin.exactCondition(META, nul, List.of(), false) instanceof LogicConstantNode c && !c.getValue());
        Assert.assertNotNull(TypeReference.createExactTrusted(META.lookupJavaType(String.class)));
    }

    @Test
    public void knobDefaults() {
        if (System.getProperty("svm.stringanalysis.typecheck.ic") == null) {
            Assert.assertEquals("default 1", 1, TypeCheckSites.MODE);
            Assert.assertEquals(TypeCheckSites.MODE, TypeCheckIcNodePlugin.MODE);
        }
        if (System.getProperty("svm.stringanalysis.typecheck.ic.list") == null) {
            Assert.assertEquals("default 2", 2, TypeCheckIcNodePlugin.LIST_CAP);
        }
        Assert.assertEquals("the shared no-proof token", InlineCacheProfilingHeuristic.UNPROVEN, TypeCheckLines.UNPROVEN);
        Assert.assertEquals(TypeCheckLines.MODE, TypeCheckSites.MODE);
        Assert.assertTrue(TypeCheckIcNodePlugin.summary().startsWith("[string-analysis] typecheck-ic: mode=" + TypeCheckIcNodePlugin.MODE + " list=" + TypeCheckIcNodePlugin.LIST_CAP));
    }
}
