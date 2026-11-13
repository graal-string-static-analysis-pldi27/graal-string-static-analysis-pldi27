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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import org.graalvm.word.LocationIdentity;

import com.oracle.svm.core.graal.nodes.FieldOffsetNode;
import com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.FieldOpen;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.RawLoadNode;
import jdk.graal.compiler.nodes.extended.RawStoreNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaField;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Pins of the closed-field rule ({@code ClosedFieldEscape.closedFieldRule}):
 * (1) the knob defaults on; (2) the rule's decision table: a field is closed iff it is reference-typed
 * and no exclusion holds, each exclusion alone opens it, with its own reason (including REGISTERED_ACCESSED);
 * (2b) the read index fails closed; (3) the read index keys IR loads by the declaring field

 * (a subclass receiver's {@code getfield E.f} resolves to {@code D.f}; a shadowing {@code E.f} is a different field;
 * primitive and static loads are not indexed; an unresolvable load reports its name); (4) the unframed-method scan finds
 * every {@code getfield} name:type in the bytecode, and abstract / native bodies read nothing. (2) also covers OFFSET_TAKEN
 * (a 9th input, checked last); (5) the same one node walk collects the fields whose offset is taken (a
 * {@code FieldOffsetProvider}, an Unsafe access with a {@code FieldLocationIdentity} or a constant field offset); (6) the
 * unframed scan counts {@code objectFieldOffset} calls (each such method is opaque).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.core.common.memory",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended", "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type"})
public class ClosedFieldRuleTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** Fixture: D declares f; E inherits it; S shadows it with its own f. */
    static class D {
        String f;
        int p;
        static String st;
    }

    static class E extends D {
        String viaSubclass() {
            return f; // javac: getfield E.f (the qualifying type), resolved to D.f
        }
    }

    static class S extends D {
        String f;

        String sup() {
            return super.f; // getfield D.f
        }

        String own() {
            return f; // getfield S.f (a different field)
        }
    }

    abstract static class A {
        abstract String body();

        native String nat();
    }

    @Test
    public void ruleDecisionTable() {
        // closed iff reference-typed and every exclusion clear; every other combination is open, with the first reason
        for (int bits = 0; bits < (1 << 9); bits++) {
            boolean ref = (bits & 1) != 0;
            boolean pub = (bits & 2) != 0;
            boolean unsafe = (bits & 4) != 0;
            boolean jni = (bits & 8) != 0;
            boolean subst = (bits & 16) != 0;
            boolean unframed = (bits & 32) != 0;
            boolean unreadable = (bits & 64) != 0;
            boolean accessed = (bits & 128) != 0;
            boolean offset = (bits & 256) != 0;
            FieldOpen r = ClosedFieldEscape.closedFieldRule(ref, pub, unsafe, jni, subst, unframed, unreadable, accessed, offset);
            boolean closed = ref && !pub && !unsafe && !jni && !subst && !unframed && !unreadable && !accessed && !offset;
            Assert.assertEquals("bits=" + Integer.toBinaryString(bits), closed, r == null);
            if (!ref) {
                Assert.assertEquals(FieldOpen.PRIMITIVE, r);
            }
        }
        Assert.assertNull(ClosedFieldEscape.closedFieldRule(true, false, false, false, false, false, false, false, false));
        Assert.assertEquals(FieldOpen.PUBLIC, ClosedFieldEscape.closedFieldRule(true, true, false, false, false, false, false, false, false));
        Assert.assertEquals(FieldOpen.UNSAFE_ACCESSED, ClosedFieldEscape.closedFieldRule(true, false, true, false, false, false, false, false, false));
        Assert.assertEquals(FieldOpen.JNI_REGISTERED, ClosedFieldEscape.closedFieldRule(true, false, false, true, false, false, false, false, false));
        Assert.assertEquals(FieldOpen.SUBSTITUTED, ClosedFieldEscape.closedFieldRule(true, false, false, false, true, false, false, false, false));
        Assert.assertEquals(FieldOpen.UNFRAMED_READER, ClosedFieldEscape.closedFieldRule(true, false, false, false, false, true, false, false, false));
        Assert.assertEquals(FieldOpen.UNREADABLE, ClosedFieldEscape.closedFieldRule(true, false, false, false, false, false, true, false, false));
        // registered as accessed only (Feature.registerAsAccessed, Truffle's node fields): open
        Assert.assertEquals(FieldOpen.REGISTERED_ACCESSED, ClosedFieldEscape.closedFieldRule(true, false, false, false, false, false, false, true, false));
        // an Unsafe-accessed / JNI field is also registered as accessed: the more specific reason comes first
        Assert.assertEquals(FieldOpen.UNSAFE_ACCESSED, ClosedFieldEscape.closedFieldRule(true, false, true, false, false, false, false, true, false));
        Assert.assertEquals(FieldOpen.JNI_REGISTERED, ClosedFieldEscape.closedFieldRule(true, false, false, true, false, false, false, true, false));
        // the field's offset is taken (a folded objectFieldOffset, a VarHandle offset, an Unsafe access naming it): open,
        // counted only when nothing else opens it
        Assert.assertEquals(FieldOpen.OFFSET_TAKEN, ClosedFieldEscape.closedFieldRule(true, false, false, false, false, false, false, false, true));
        Assert.assertEquals(FieldOpen.UNSAFE_ACCESSED, ClosedFieldEscape.closedFieldRule(true, false, true, false, false, false, false, false, true));
        Assert.assertEquals(FieldOpen.REGISTERED_ACCESSED, ClosedFieldEscape.closedFieldRule(true, false, false, false, false, false, false, true, true));
        Assert.assertEquals(FieldOpen.PRIMITIVE, ClosedFieldEscape.closedFieldRule(false, false, false, false, false, false, false, false, true));
        // fail closed first: an unreadable field is open whatever else holds
        Assert.assertEquals(FieldOpen.UNREADABLE, ClosedFieldEscape.closedFieldRule(true, true, true, true, true, true, true, true, true));
    }

    @Test
    public void readIndexFailsClosed() {
        // the index is trusted only when the enumeration met every frame
        Assert.assertNull(ClosedFieldEscape.indexFailure(100, 40, 40));
        Assert.assertNotNull("empty universe (the enumeration swallowed a failure)", ClosedFieldEscape.indexFailure(0, 0, 0));
        Assert.assertNotNull("a partial enumeration: fewer frames met than exist", ClosedFieldEscape.indexFailure(100, 39, 40));
        Assert.assertNotNull("more frames met than counted", ClosedFieldEscape.indexFailure(100, 41, 40));
        Assert.assertNotNull("frame count unknown (the bridge's default)", ClosedFieldEscape.indexFailure(100, 40, -1));
    }

    private ResolvedJavaMethod method(Class<?> c, String name) throws NoSuchMethodException {
        return metaAccess.lookupJavaMethod(c.getDeclaredMethod(name));
    }

    /** The resolved field of the first getfield in {@code m} (the fixtures were executed: their references are resolved). */
    private static JavaField firstGetfield(ResolvedJavaMethod m) {
        BytecodeStream s = new BytecodeStream(m.getCode());
        while (s.currentBC() != Bytecodes.END) {
            if (s.currentBC() == Bytecodes.GETFIELD) {
                return m.getConstantPool().lookupField(s.readCPI(), m, Bytecodes.GETFIELD);
            }
            s.next();
        }
        return null;
    }

    @Test
    public void subclassReceiverResolvesToTheDeclaringField() throws Exception {
        S sh = new S();
        sh.f = "own";
        ((D) sh).f = "inherited";
        Assert.assertEquals("inherited", sh.sup());
        Assert.assertEquals("own", sh.own());
        E e = new E();
        e.f = "x";
        Assert.assertEquals("x", e.viaSubclass());
        ResolvedJavaField df = metaAccess.lookupJavaField(D.class.getDeclaredField("f"));
        ResolvedJavaField sf = metaAccess.lookupJavaField(S.class.getDeclaredField("f"));
        JavaField viaE = firstGetfield(method(E.class, "viaSubclass"));
        Assert.assertTrue("resolved: " + viaE, viaE instanceof ResolvedJavaField);
        Assert.assertEquals("getfield E.f is D.f (the same field the store writes)", df, viaE);
        Assert.assertEquals("super.f is D.f", df, firstGetfield(method(S.class, "sup")));
        Assert.assertEquals("the shadowing field is its own field", sf, firstGetfield(method(S.class, "own")));
        Assert.assertNotEquals(df, sf);
    }

    @Test
    public void unframedScanFindsEveryGetfield() throws Exception {
        Set<String> out = new HashSet<>();
        Assert.assertTrue(ClosedFieldEscape.getfieldsOf(method(S.class, "sup"), out));
        Assert.assertTrue(ClosedFieldEscape.getfieldsOf(method(E.class, "viaSubclass"), out));
        Assert.assertEquals(Set.of("f:Ljava/lang/String;"), out);
        Set<String> none = new HashSet<>();
        Assert.assertTrue("abstract: no body", ClosedFieldEscape.getfieldsOf(method(A.class, "body"), none));
        Assert.assertTrue("native: JNI only", ClosedFieldEscape.getfieldsOf(method(A.class, "nat"), none));
        Assert.assertTrue(none.isEmpty());
        Assert.assertEquals("f:Ljava/lang/String;", ClosedFieldEscape.nameAndType(metaAccess.lookupJavaField(D.class.getDeclaredField("f"))));
    }

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("ClosedFieldRuleTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    @Test
    public void loadIndexKeysByDeclaringField() throws Exception {
        StructuredGraph g = graph();
        ResolvedJavaType st = metaAccess.lookupJavaType(S.class);
        ParameterNode o = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(st)))));
        ResolvedJavaField df = metaAccess.lookupJavaField(D.class.getDeclaredField("f"));
        ResolvedJavaField sf = metaAccess.lookupJavaField(S.class.getDeclaredField("f"));
        ResolvedJavaField dp = metaAccess.lookupJavaField(D.class.getDeclaredField("p"));
        ResolvedJavaField ds = metaAccess.lookupJavaField(D.class.getDeclaredField("st"));
        LoadFieldNode ld = g.add(LoadFieldNode.create(null, o, df));
        LoadFieldNode ls = g.add(LoadFieldNode.create(null, o, sf));
        g.add(LoadFieldNode.create(null, o, dp)); // primitive: never holds a string
        g.add(LoadFieldNode.create(null, null, ds)); // static: its own table, not indexed
        List<String> got = new ArrayList<>();
        List<String> unresolved = new ArrayList<>();
        ClosedFieldEscape.collectLoads(g, f -> f, (k, n) -> got.add(k.getDeclaringClass().toJavaName(true) + "." + k.getName() + (n == ld ? "@ld" : n == ls ? "@ls" : "@?")),
                        unresolved::add);
        got.sort(null);
        Assert.assertEquals(List.of(D.class.getName() + ".f@ld", S.class.getName() + ".f@ls"), got);
        Assert.assertTrue(unresolved.isEmpty());
        // an unresolvable load (the resolver answers null) reports its name: fail closed for every field of that name
        List<String> names = new ArrayList<>();
        ClosedFieldEscape.collectLoads(g, f -> null, (k, n) -> Assert.fail("nothing resolves"), names::add);
        names.sort(null);
        Assert.assertEquals(List.of("f", "f"), names);
    }

    /** Fixture: a method named objectFieldOffset (the unframed scan is name-based) and a caller. */
    static final class OffsetCaller {
        static long objectFieldOffset(Class<?> c, String name) {
            return c.getName().length() + name.length();
        }

        static long caller() {
            return objectFieldOffset(D.class, "f");
        }

        static long noCall() {
            return 3L;
        }
    }

    @Test
    public void offsetTakenFieldsAreCollectedInTheSameWalk() throws Exception {
        StructuredGraph g = graph();
        ResolvedJavaType st = metaAccess.lookupJavaType(S.class);
        ParameterNode o = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(st)))));
        ResolvedJavaField df = metaAccess.lookupJavaField(D.class.getDeclaredField("f"));
        ResolvedJavaField sf = metaAccess.lookupJavaField(S.class.getDeclaredField("f"));
        ResolvedJavaField dp = metaAccess.lookupJavaField(D.class.getDeclaredField("p"));
        ResolvedJavaField ds = metaAccess.lookupJavaField(D.class.getDeclaredField("st"));
        g.markUnsafeAccess(RawLoadNode.class);
        // a folded objectFieldOffset(D.class, "f") (SVM's FieldOffsetNode: a FieldOffsetProvider), used by a swap on o
        ValueNode fo = g.addOrUniqueWithInputs(FieldOffsetNode.create(JavaKind.Long, df));
        g.add(new AtomicReadAndWriteNode(o, fo, ConstantNode.forConstant(JavaConstant.NULL_POINTER, metaAccess, g), JavaKind.Object, LocationIdentity.any()));
        // a raw load whose location is S.f's FieldLocationIdentity (offset unknown)
        ParameterNode off = g.addWithoutUnique(new ParameterNode(1, StampPair.createSingle(StampFactory.forKind(JavaKind.Long))));
        g.add(new RawLoadNode(o, off, JavaKind.Object, new FieldLocationIdentity(sf)));
        // a raw store at D.p's constant (hosted) offset on o: the field resolves on the receiver's type
        g.add(new RawStoreNode(o, ConstantNode.forLong(dp.getOffset(), g), ConstantNode.forInt(1, g), JavaKind.Int, LocationIdentity.any()));
        // a static field's location: never collected (static fields are never closed; a static FieldOffsetNode needs the
        // image builder's singletons)
        g.add(new RawLoadNode(o, off, JavaKind.Object, new FieldLocationIdentity(ds)));
        // a raw load at an unknown offset with an unknown location: names no field
        g.add(new RawLoadNode(o, off, JavaKind.Object, LocationIdentity.any()));
        List<String> taken = new ArrayList<>();
        List<String> unresolved = new ArrayList<>();
        ClosedFieldEscape.scanFieldAccesses(g, f -> f, (k, n) -> Assert.fail("no LoadField in this graph"), unresolved::add,
                        (k, viaUnsafe) -> taken.add(k.getDeclaringClass().toJavaName(true) + "." + k.getName() + (viaUnsafe ? "@unsafe" : "@offset")));
        taken.sort(null);
        Assert.assertEquals(List.of(D.class.getName() + ".f@offset", D.class.getName() + ".p@unsafe", S.class.getName() + ".f@unsafe"), taken);
        Assert.assertTrue(unresolved.isEmpty());
        // an unresolvable offset field reports its name (fail closed for that name)
        List<String> names = new ArrayList<>();
        ClosedFieldEscape.scanFieldAccesses(g, f -> null, (k, n) -> Assert.fail(), names::add, (k, v) -> Assert.fail("nothing resolves"));
        names.sort(null);
        Assert.assertEquals(List.of("f", "f", "p"), names);
        // the loads-only entry point ignores the offset nodes
        ClosedFieldEscape.collectLoads(g, f -> f, (k, n) -> Assert.fail("no LoadField"), n -> Assert.fail("nothing unresolved"));
    }

    @Test
    public void unframedScanCountsObjectFieldOffsetCalls() throws Exception {
        Assert.assertTrue("the fixture runs (its references resolve)", OffsetCaller.caller() > 0 && OffsetCaller.noCall() == 3L);
        ClosedFieldEscape.FieldReadIndex x = new ClosedFieldEscape.FieldReadIndex();
        Set<String> out = new HashSet<>();
        Assert.assertTrue(ClosedFieldEscape.getfieldsOf(method(OffsetCaller.class, "noCall"), out, x));
        Assert.assertEquals(0, x.unframedOffsetCalls);
        Assert.assertTrue(ClosedFieldEscape.getfieldsOf(method(OffsetCaller.class, "caller"), out, x));
        Assert.assertEquals("one objectFieldOffset call", 1, x.unframedOffsetCalls);
        Assert.assertTrue("no getfield in either", out.isEmpty());
    }
}
