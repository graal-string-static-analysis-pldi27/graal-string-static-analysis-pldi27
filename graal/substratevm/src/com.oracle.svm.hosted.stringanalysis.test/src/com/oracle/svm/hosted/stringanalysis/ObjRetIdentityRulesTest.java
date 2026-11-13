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

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.annotation.ElementType;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The pure parts of the object-identity rules (the reverse navigation index and its NEST_EXPOSED / metadata split, the
 * recursive class-metadata scan, the harmless class-uses graph walk on hand-built graphs, NO_MEMBER_BIRTH in the guard
 * order), the named verdicts of the pending kinds, and the truth tables of the two exceptions (self slot,
 * INLINED_ONLY).
 */
@AddExports({"java.base/jdk.internal.reflect", "jdk.graal.compiler/jdk.graal.compiler.bytecode", "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug", "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.java", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.debug", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.gc", "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.loop",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.util", "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual",
                "jdk.graal.compiler/jdk.graal.compiler.options", "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.graal.compiler/jdk.graal.compiler.phases.util", "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.common",
                "jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.meta", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class ObjRetIdentityRulesTest {
    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    static Object sink;

    // ------------------------------------------------------------------ knobs and guard order
    @Test
    public void knobDefaultsAreTheRevertIdentity() {
        // rule U delivers by default; objret=0 disables it
        Assert.assertEquals(1, RecursiveTracking.OBJRET);
        Assert.assertTrue(RecursiveTracking.OBJRET_DELIVER);
        Assert.assertTrue(RecursiveTracking.OBJRET_ON);
    }

    @Test
    public void noMemberBirthSitsRightAfterTheBirthCounts() {
        Assert.assertEquals(ObjRetRules.GuardFailN.TOO_MANY_BIRTHS.ordinal() + 1, ObjRetRules.GuardFailN.NO_MEMBER_BIRTH.ordinal());
        Assert.assertEquals(ObjRetRules.GuardFailN.NO_MEMBER_BIRTH.ordinal() + 1, ObjRetRules.GuardFailN.UNFRAMED_METHOD.ordinal());
        Assert.assertEquals(ObjRetRules.GuardFailN.NO_MEMBER_BIRTH, ObjRetRules.guard(false, false, false, 2, true, 1, true, true, true, true, true, 1, 1, true, true, 1));
        Assert.assertEquals(ObjRetRules.GuardFailN.TOO_MANY_BIRTHS, ObjRetRules.guard(false, false, false, ObjRetRules.MAX_BIRTHS + 1, true, 0, false, false, false, false, false, 0, 0, false, false,
                        0));
        Assert.assertEquals(ObjRetRules.GuardFailN.NO_BIRTH, ObjRetRules.guard(false, false, false, 0, true, 0, false, false, false, false, false, 0, 0, false, false, 0));
        Assert.assertNull(ObjRetRules.guard(false, false, false, 2, false, 0, false, false, false, false, false, 0, 0, false, false, 0));
    }

    // ------------------------------------------------------------------ the named verdicts of the 38 pending kinds
    @Test
    public void namedPendingVerdictsCoverTheAllowListExactly() {
        Assert.assertEquals(38, ObjIdRules.PENDING_ALLOW.size());
        Assert.assertEquals(ObjIdRules.PENDING_ALLOW.keySet(), ObjIdRules.PENDING_NAMED.keySet());
        for (Map.Entry<String, String> e : ObjIdRules.PENDING_NAMED.entrySet()) {
            String v = e.getValue();
            Assert.assertTrue(e.getKey(), v.startsWith("HOLDS: ") || v.startsWith("HOLDS-WITH-CONDITION: "));
            boolean names = false;
            for (String p : ObjIdRules.NAMED_PREMISES) {
                names |= v.contains(p);
            }
            Assert.assertTrue("the condition names its premise: " + e.getKey(), names);
        }
        // rows whose verdict rests on a changed argument
        Assert.assertTrue(ObjIdRules.PENDING_NAMED.get("field java.lang.ThreadGroup.groups").contains("changed argument"));
        Assert.assertTrue(ObjIdRules.PENDING_NAMED.get("static sun.security.jca.Providers.providerList").contains("changed argument"));
        String classes = ObjIdRules.PENDING_NAMED.get("field com.oracle.svm.core.code.ImageCodeInfo.classes");
        for (String p : new String[]{"G1-N", "G2", "G3", "G5-N", "M-1"}) {
            Assert.assertTrue(p, classes.contains(p));
        }
        Assert.assertTrue(ObjIdRules.PENDING_NAMED.get("field com.oracle.svm.core.jni.access.JNIAccessibleMember.hidingSubclasses").contains("membership-only"));
    }

    // ------------------------------------------------------------------ the self-slot truth table (all 2^7 rows)
    @Test
    public void selfSlotTruthTable() {
        int trues = 0;
        for (int bits = 0; bits < 128; bits++) {
            String holder = (bits & 1) != 0 ? ObjRetRules.COMPANION_TYPE : "com.oracle.svm.core.hub.DynamicHub";
            String field = (bits & 2) != 0 ? ObjRetRules.NEST_HOST_FIELD : "declaringClass";
            boolean own = (bits & 4) != 0;
            boolean sole = (bits & 8) != 0;
            boolean pending = (bits & 16) != 0;
            boolean readers = (bits & 32) != 0;
            boolean build = (bits & 64) != 0;
            boolean d = ObjRetRules.selfSlotDiscount(holder, field, own, sole, pending, readers, build);
            Assert.assertEquals("bits=" + bits, bits == 127, d);
            trues += d ? 1 : 0;
        }
        Assert.assertEquals("only the all-true row discounts", 1, trues);
        // the other hub-internal slots never discount (another class's nestHost is 'own=false'; declaringClass, arrayHub, componentType)
        for (String f : new String[]{"declaringClass", "arrayHub", "superHub", "classLoader"}) {
            Assert.assertFalse(f, ObjRetRules.selfSlotDiscount(ObjRetRules.COMPANION_TYPE, f, true, true, true, true, true));
        }
        Assert.assertFalse(ObjRetRules.selfSlotDiscount("com.oracle.svm.core.hub.DynamicHub", "componentType", true, true, true, true, true));
        Assert.assertTrue(ObjRetRules.companionReaderAudited("com.oracle.svm.core.monitor.MultiThreadedMonitorSupport"));
        Assert.assertTrue("DynamicHub substitutes java.lang.Class in the analysis universe", ObjRetRules.companionReaderAudited("java.lang.Class"));
        Assert.assertTrue(ObjRetRules.companionReaderAudited("com.oracle.svm.core.hub.DynamicHub$ReflectionDataAccessors"));
        Assert.assertFalse(ObjRetRules.companionReaderAudited("java.lang.String"));
        Assert.assertFalse(ObjRetRules.companionReaderAudited("com.oracle.svm.core.hub.DynamicHubSupport"));
    }

    // ------------------------------------------------------------------ the INLINED_ONLY truth table
    /** A hand-built caller table: method -> cause (null = framed), excluded, callers (null = index failed). */
    static final class Table implements ObjRetRules.InlinedFacts<String> {
        final Map<String, ObjRetRules.UnframedCause> cause = new HashMap<>();
        final Set<String> excluded = new HashSet<>();
        final Map<String, List<String>> callers = new HashMap<>();
        boolean throwOn;

        Table m(String name, ObjRetRules.UnframedCause c, String... cs) {
            cause.put(name, c);
            callers.put(name, cs == null ? null : List.of(cs));
            return this;
        }

        @Override
        public ObjRetRules.UnframedCause causeOf(String m) {
            if (throwOn && m.equals("boom")) {
                throw new IllegalStateException("unreadable");
            }
            return cause.get(m);
        }

        @Override
        public boolean excluded(String m) {
            return excluded.contains(m);
        }

        @Override
        public Collection<String> callers(String m) {
            return callers.get(m);
        }
    }

    private static final ObjRetRules.UnframedCause IO = ObjRetRules.UnframedCause.INLINED_ONLY;

    @Test
    public void inlinedOnlyTruthTable() {
        // framed callers only
        Table t = new Table().m("x", IO, "f1", "f2").m("f1", null).m("f2", null);
        Assert.assertTrue(ObjRetRules.inlinedOnlyOk("x", t));
        // inlined-framed: an INLINED_ONLY caller whose own callers are framed
        t = new Table().m("x", IO, "y").m("y", IO, "f").m("f", null);
        Assert.assertTrue(ObjRetRules.inlinedOnlyOk("x", t));
        // inlined-unframed: the INLINED_ONLY caller's caller has another unframed cause
        t = new Table().m("x", IO, "y").m("y", IO, "n").m("n", ObjRetRules.UnframedCause.NATIVE);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // a caller with another unframed cause (every one fails closed)
        for (ObjRetRules.UnframedCause c : ObjRetRules.UnframedCause.values()) {
            if (c == IO) {
                continue;
            }
            t = new Table().m("x", IO, "f", "c").m("f", null).m("c", c);
            Assert.assertFalse(c.name(), ObjRetRules.inlinedOnlyOk("x", t));
        }
        // a cycle
        t = new Table().m("x", IO, "y").m("y", IO, "x");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // depth: 3 levels pass, the 4th level does not
        t = new Table().m("x", IO, "a").m("a", IO, "b").m("b", IO, "f").m("f", null);
        Assert.assertTrue("x > a > b > framed: depth 3", ObjRetRules.inlinedOnlyOk("x", t));
        t = new Table().m("x", IO, "a").m("a", IO, "b").m("b", IO, "c").m("c", IO, "f").m("f", null);
        Assert.assertFalse("depth 4: the bound", ObjRetRules.inlinedOnlyOk("x", t));
        // unreadable (the index failed) and empty callers
        t = new Table().m("x", IO, (String[]) null);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        t = new Table().m("x", IO);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // x itself not INLINED_ONLY / framed / excluded
        t = new Table().m("x", ObjRetRules.UnframedCause.INTRINSIC, "f").m("f", null);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        t = new Table().m("x", null, "f").m("f", null);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        t = new Table().m("x", IO, "f").m("f", null);
        t.excluded.add("x");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // an excluded inlined-only caller
        t = new Table().m("x", IO, "y").m("y", IO, "f").m("f", null);
        t.excluded.add("y");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // an exception during the scan
        t = new Table().m("x", IO, "f", "boom").m("f", null).m("boom", null);
        t.throwOn = true;
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
    }

    // ------------------------------------------------------------------ the reverse navigation index on real classes
    static class Outer {
        static class Inner {
        }

        Supplier<Object> lambda() {
            return () -> "x";
        }
    }

    private static Map<Class<?>, List<Map.Entry<Class<?>, ObjRetRules.NavLink>>> index(Class<?>... types) {
        Map<Class<?>, List<Map.Entry<Class<?>, ObjRetRules.NavLink>>> links = new HashMap<>();
        for (Class<?> k : types) {
            ObjRetRules.navLinksOf(k, k, c -> c, (target, from, kind) -> links.computeIfAbsent(target, x -> new ArrayList<>()).add(new AbstractMap.SimpleEntry<>(from, kind)));
        }
        return links;
    }

    private static boolean has(Map<Class<?>, List<Map.Entry<Class<?>, ObjRetRules.NavLink>>> links, Class<?> target, Class<?> from, ObjRetRules.NavLink k) {
        for (Map.Entry<Class<?>, ObjRetRules.NavLink> e : links.getOrDefault(target, List.of())) {
            if (e.getKey() == from && e.getValue() == k) {
                return true;
            }
        }
        return false;
    }

    @Test
    public void reverseIndexOnRealClasses() {
        Class<?> lambdaClass = new Outer().lambda().getClass();
        Assert.assertTrue(lambdaClass.isHidden());
        Class<?> host = Outer.class.getNestHost(); // the test class (the top-level nest host)
        Map<Class<?>, List<Map.Entry<Class<?>, ObjRetRules.NavLink>>> links = index(Outer.class, Outer.Inner.class, lambdaClass, Outer.Inner[][].class);
        // pre-11-style DECLARING (InnerClasses), the nest host of a member, the hidden nestmate's nest host
        Assert.assertTrue(has(links, Outer.class, Outer.Inner.class, ObjRetRules.NavLink.DECLARING));
        Assert.assertTrue(has(links, host, Outer.Inner.class, ObjRetRules.NavLink.NEST_HOST));
        Assert.assertTrue("a lambda class leads to its nest host", has(links, host, lambdaClass, ObjRetRules.NavLink.NEST_HOST));
        Assert.assertTrue(has(links, Outer.Inner.class, Outer.class, ObjRetRules.NavLink.MEMBER_LIST));
        // every component level of an array (no dimension bound)
        Assert.assertTrue(has(links, Outer.Inner[].class, Outer.Inner[][].class, ObjRetRules.NavLink.COMPONENT));
        Assert.assertTrue(has(links, Outer.Inner.class, Outer.Inner[][].class, ObjRetRules.NavLink.COMPONENT));
        // NEST_EXPOSED: hub-data links only (the nest host from a nested class / a lambda)
        List<Map.Entry<Class<?>, Class<?>>> exposedHost = List.of(new AbstractMap.SimpleEntry<>(host, host));
        Assert.assertNotNull(ObjRetRules.nestExposed(links, exposedHost));
        List<Map.Entry<Class<?>, Class<?>>> exposedInner = List.of(new AbstractMap.SimpleEntry<>(Outer.Inner.class, Outer.Inner.class));
        Assert.assertNull("Inner has only metadata (MEMBER_LIST / NEST_MEMBER) and COMPONENT links into it", ObjRetRules.nestExposed(links, exposedInner));
        // the link kinds partition: hub data (NEST_EXPOSED), metadata (REGISTERED via the linked registrations), COMPONENT (CONE_ARRAY)
        for (ObjRetRules.NavLink k : ObjRetRules.NavLink.values()) {
            int n = (ObjRetRules.hubNavLink(k) ? 1 : 0) + (ObjRetRules.metadataNavLink(k) ? 1 : 0) + (k == ObjRetRules.NavLink.COMPONENT ? 1 : 0);
            Assert.assertEquals(k.name(), 1, n);
        }
    }

    // ------------------------------------------------------------------ the recursive class-metadata scan
    @Retention(RetentionPolicy.RUNTIME)
    @interface Leaf {
        Class<?> value();
    }

    @Retention(RetentionPolicy.RUNTIME)
    @interface Outerann {
        Leaf nested();

        Leaf[] many();

        Class<?>[] classes() default {};
    }

    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.TYPE_USE})
    @interface TypeAnn {
        Class<?> value();
    }

    static final class M1 {
    }

    static final class M2 {
    }

    static final class M3 {
    }

    static final class M4 {
    }

    static final class M5 {
    }

    @Outerann(nested = @Leaf(M1.class), many = {@Leaf(M2.class), @Leaf(M3.class)}, classes = {M4.class})
    static class Annotated implements @TypeAnn(M5.class) Runnable {
        @Override
        public void run() {
        }
    }

    static final class P1 {
    }

    static final class P2 {
    }

    @SuppressWarnings("unused")
    static void annotatedParams(@Leaf(P1.class) Object a, List<@TypeAnn(P2.class) String> b) {
    }

    @Test
    public void metadataScanIsRecursive() throws NoSuchMethodException {
        Set<Class<?>> out = new HashSet<>();
        ObjRetRules.classMetadataClasses(Annotated.class, out);
        for (Class<?> k : new Class<?>[]{Outerann.class, Leaf.class, M1.class, M2.class, M3.class, M4.class, TypeAnn.class, M5.class}) {
            Assert.assertTrue(k.getSimpleName(), out.contains(k));
        }
        Set<Class<?>> ex = new HashSet<>();
        ObjRetRules.executableMetadataClasses(ObjRetIdentityRulesTest.class.getDeclaredMethod("annotatedParams", Object.class, List.class), ex);
        Assert.assertTrue("parameter annotation", ex.contains(P1.class));
        Assert.assertTrue("type annotation inside a type argument", ex.contains(P2.class));
        // a real JDK class without Class-valued annotations: no exception, only annotation types
        Set<Class<?>> jdk = new HashSet<>();
        ObjRetRules.classMetadataClasses(java.util.ArrayList.class, jdk);
        for (Class<?> k : jdk) {
            Assert.assertTrue(k.getName(), k.isAnnotation());
        }
    }

    // ------------------------------------------------------------------ the harmless class-uses graph walk on hand-built graphs
    @SuppressWarnings("unused")
    static Object holder(Class<?> c) {
        return c;
    }

    private static StructuredGraph newGraph() throws NoSuchMethodException {
        DebugContext debug = new DebugContext.Builder(OPTIONS).build();
        return new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(ObjRetIdentityRulesTest.class.getDeclaredMethod("holder", Class.class))).build();
    }

    private static ParameterNode classParam(StructuredGraph g) {
        return g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(jdk.graal.compiler.core.common.type.TypeReference.createTrustedWithoutAssumptions(
                        META.lookupJavaType(Class.class))))));
    }

    private static InvokeNode call(StructuredGraph g, java.lang.reflect.Method m, ValueNode... args) {
        ResolvedJavaMethod rm = META.lookupJavaMethod(m);
        MethodCallTargetNode ct = g.add(new MethodCallTargetNode(InvokeKind.Virtual, rm, args, StampPair.createSingle(StampFactory.object()), null));
        InvokeNode inv = g.add(new InvokeNode(ct, 0));
        g.start().setNext(inv);
        return inv;
    }

    @Test
    public void np5GraphWalk() throws Exception {
        // observations: a null check and a getName receiver
        StructuredGraph g = newGraph();
        ParameterNode p = classParam(g);
        g.addOrUniqueWithInputs(IsNullNode.create(p));
        call(g, Class.class.getMethod("getName"), p);
        Assert.assertTrue(ObjRetRules.harmlessClassUses(p, null));
        // a navigation API receiver is harmful
        g = newGraph();
        p = classParam(g);
        call(g, Class.class.getMethod("getSuperclass"), p);
        String[] why = new String[1];
        Assert.assertFalse(ObjRetRules.harmlessClassUses(p, why));
        Assert.assertTrue(why[0], why[0].startsWith("call:java.lang.Class.getSuperclass#0"));
        // a Return and a store are harmful; a Pi is followed (its use decides)
        g = newGraph();
        p = classParam(g);
        g.start().setNext(g.add(new ReturnNode(p)));
        Assert.assertFalse(ObjRetRules.harmlessClassUses(p, why));
        Assert.assertEquals("node:ReturnNode", why[0]);
        g = newGraph();
        p = classParam(g);
        PiNode pi = g.addWithoutUnique(new PiNode(p, StampFactory.objectNonNull()));
        g.add(new StoreFieldNode(null, META.lookupJavaField(ObjRetIdentityRulesTest.class.getDeclaredField("sink")), pi));
        Assert.assertFalse("through the Pi to a store", ObjRetRules.harmlessClassUses(p, why));
        Assert.assertEquals("node:StoreFieldNode", why[0]);
        g = newGraph();
        p = classParam(g);
        pi = g.addWithoutUnique(new PiNode(p, StampFactory.objectNonNull()));
        g.addOrUniqueWithInputs(IsNullNode.create(pi));
        Assert.assertTrue("through the Pi to an observation", ObjRetRules.harmlessClassUses(p, null));
    }
}
