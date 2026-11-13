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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.JavaType;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The named-class object-return rules, second part: the CLINIT exception and the MethodHandle wildcard of the INLINED_ONLY index, the caller-matching rule, the
 * CLASS_CAST message argument, the one-shot / PRECISE(empty) model of two hooks on real tables, ID-DEP propagation and
 * the cross-candidate precedence, the guard-trip rerun decision, and the correspondence guard of the lookahead.
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
public class ObjRetNamedRulesTest {
    private static final ObjRetRules.UnframedCause IO = ObjRetRules.UnframedCause.INLINED_ONLY;

    @Test
    public void knobDefaultsAreTheRevertIdentity() {
        // rule U delivers by default; objret=0 is the revert switch
        Assert.assertEquals(1, RecursiveTracking.OBJRET);
        Assert.assertTrue(RecursiveTracking.OBJRET_DELIVER);
        Assert.assertFalse(StringAnalysisForkSupport.objretRerunRequested());
    }

    // ------------------------------------------------------------------ the CLINIT exception
    /** A caller table with dead class initializers. */
    static final class Table implements ObjRetRules.InlinedFacts<String> {
        final Map<String, ObjRetRules.UnframedCause> cause = new HashMap<>();
        final Map<String, List<String>> callers = new HashMap<>();
        final Set<String> dead = new HashSet<>();

        Table m(String name, ObjRetRules.UnframedCause c, String... cs) {
            cause.put(name, c);
            callers.put(name, cs == null ? null : List.of(cs));
            return this;
        }

        @Override
        public ObjRetRules.UnframedCause causeOf(String m) {
            return cause.get(m);
        }

        @Override
        public boolean excluded(String m) {
            return false;
        }

        @Override
        public Collection<String> callers(String m) {
            return callers.get(m);
        }

        @Override
        public boolean deadClinit(String m) {
            return dead.contains(m);
        }
    }

    @Test
    public void clinitExceptionTruthTable() {
        ObjRetRules.UnframedCause bt = ObjRetRules.UnframedCause.CLINIT_BUILD_TIME;
        ObjRetRules.UnframedCause sim = ObjRetRules.UnframedCause.CLINIT_SIMULATED;
        // a dead (build-time) clinit only: ok (the non-empty-callers rule holds: it is in the set)
        Table t = new Table().m("x", IO, "c").m("c", bt);
        t.dead.add("c");
        Assert.assertTrue(ObjRetRules.inlinedOnlyOk("x", t));
        // a dead simulated clinit + a framed caller: ok
        t = new Table().m("x", IO, "c", "f").m("c", sim).m("f", null);
        t.dead.add("c");
        Assert.assertTrue(ObjRetRules.inlinedOnlyOk("x", t));
        // a build-time clinit that is not dead (e.g. an info with an initializer pointer): fail closed
        t = new Table().m("x", IO, "c").m("c", bt);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // a run-time clinit: never skipped, even when the facts said dead
        t = new Table().m("x", IO, "c").m("c", ObjRetRules.UnframedCause.CLINIT_RUNTIME);
        t.dead.add("c");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // "dead" is honoured only for the clinit causes (another cause stays fail-closed)
        t = new Table().m("x", IO, "c").m("c", ObjRetRules.UnframedCause.NATIVE);
        t.dead.add("c");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // a dead clinit next to an unframed caller: fail closed
        t = new Table().m("x", IO, "c", "n").m("c", bt).m("n", ObjRetRules.UnframedCause.NO_IR);
        t.dead.add("c");
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // empty callers stay false
        t = new Table().m("x", IO);
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", t));
        // the production default of the facts: no clinit is dead
        ObjRetRules.InlinedFacts<String> plain = new ObjRetRules.InlinedFacts<>() {
            @Override
            public ObjRetRules.UnframedCause causeOf(String m) {
                return m.equals("x") ? IO : bt;
            }

            @Override
            public boolean excluded(String m) {
                return false;
            }

            @Override
            public Collection<String> callers(String m) {
                return List.of("c");
            }
        };
        Assert.assertFalse(plain.deadClinit("c"));
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", plain));
    }

    /** The wildcard (MethodHandle / invokedynamic) callers, image-level. */
    @Test
    public void wildcardCallerTruthTable() {
        ObjRetRules.UnframedCause bt = ObjRetRules.UnframedCause.CLINIT_BUILD_TIME;
        Table t = new Table().m("w", null).m("i", IO, "f").m("f", null).m("c", bt).m("d", bt).m("j", IO, "n").m("n", ObjRetRules.UnframedCause.NO_IR).m("k", IO);
        t.dead.add("c");
        Assert.assertTrue("framed", ObjRetRules.wildcardOk("w", t));
        Assert.assertTrue("inlined-only, framed bytecode callers", ObjRetRules.wildcardOk("i", t));
        Assert.assertTrue("a dead clinit", ObjRetRules.wildcardOk("c", t));
        Assert.assertFalse("a live build-time clinit", ObjRetRules.wildcardOk("d", t));
        Assert.assertFalse("inlined-only into an unframed caller", ObjRetRules.wildcardOk("j", t));
        Assert.assertFalse("inlined-only without bytecode callers", ObjRetRules.wildcardOk("k", t));
        for (ObjRetRules.UnframedCause c : List.of(ObjRetRules.UnframedCause.NATIVE, ObjRetRules.UnframedCause.STUB, ObjRetRules.UnframedCause.NO_IR,
                        ObjRetRules.UnframedCause.CLINIT_RUNTIME, ObjRetRules.UnframedCause.INTRINSIC, ObjRetRules.UnframedCause.OTHER)) {
            Assert.assertFalse(c.name(), ObjRetRules.wildcardOk("u", new Table().m("u", c)));
        }
        // the image-level verdict gates every x: a framed-only x fails when some wildcard caller fails
        ObjRetRules.InlinedFacts<String> wildFail = new ObjRetRules.InlinedFacts<>() {
            @Override
            public ObjRetRules.UnframedCause causeOf(String m) {
                return m.equals("x") ? IO : null;
            }

            @Override
            public boolean excluded(String m) {
                return false;
            }

            @Override
            public Collection<String> callers(String m) {
                return List.of("f");
            }

            @Override
            public boolean wildcardsOk() {
                return false;
            }
        };
        Assert.assertFalse(ObjRetRules.inlinedOnlyOk("x", wildFail));
    }

    // ------------------------------------------------------------------ the caller index rules
    @Test
    public void bytecodeCallerMatchTruthTable() {
        // (holderUnresolved, ctor, staticOrSpecial, holderIsXClass, xAssignableFromHolder, holderAssignableFromX)
        Assert.assertTrue("an unresolved holder matches", ObjRetRules.bytecodeCallerMatch(true, false, false, false, false, false));
        Assert.assertTrue("a constructor from its own class", ObjRetRules.bytecodeCallerMatch(false, true, true, true, true, true));
        Assert.assertFalse("a constructor from a subclass holder (super(...) of another class)", ObjRetRules.bytecodeCallerMatch(false, true, true, false, true, false));
        Assert.assertFalse("a constructor from a superclass holder", ObjRetRules.bytecodeCallerMatch(false, true, true, false, false, true));
        Assert.assertTrue("static/special resolve upward: holder = a subclass of x's class", ObjRetRules.bytecodeCallerMatch(false, false, true, false, true, false));
        Assert.assertFalse("static/special never dispatch downward", ObjRetRules.bytecodeCallerMatch(false, false, true, false, false, true));
        Assert.assertTrue("virtual: upward", ObjRetRules.bytecodeCallerMatch(false, false, false, false, true, false));
        Assert.assertTrue("virtual: downward (holder is a supertype of x's class)", ObjRetRules.bytecodeCallerMatch(false, false, false, false, false, true));
        Assert.assertFalse("virtual: an unrelated holder", ObjRetRules.bytecodeCallerMatch(false, false, false, false, false, false));
    }

    @Test
    public void methodHandleInvokersAreWildcards() {
        for (String n : List.of("invoke", "invokeExact", "invokeBasic", "invokeWithArguments", "linkToStatic", "linkToVirtual", "linkToSpecial", "linkToInterface")) {
            Assert.assertTrue(n, ObjRetRules.methodHandleInvoker("java.lang.invoke.MethodHandle", n));
        }
        Assert.assertFalse(ObjRetRules.methodHandleInvoker("java.lang.invoke.MethodHandle", "type"));
        Assert.assertFalse(ObjRetRules.methodHandleInvoker("java.lang.invoke.MethodHandle", "bindTo"));
        Assert.assertFalse(ObjRetRules.methodHandleInvoker("java.lang.invoke.VarHandle", "get"));
        Assert.assertFalse(ObjRetRules.methodHandleInvoker("org.Foo", "invoke"));
    }

    // ------------------------------------------------------------------ the CLASS_CAST message argument
    @Test
    public void classCastMessageArgumentRows() {
        Object obj = new Object();
        Object cls = new Object();
        Assert.assertTrue("arg 1 of a CLASS_CAST node", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.CLASS_CAST, List.of(obj, cls), cls));
        Assert.assertFalse("arg 0 (the object) is harmful", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.CLASS_CAST, List.of(cls, obj), cls));
        Assert.assertFalse("both args", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.CLASS_CAST, List.of(cls, cls), cls));
        Assert.assertFalse("another kind", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.ARRAY_STORE, List.of(obj, cls), cls));
        Assert.assertFalse("another kind", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.NULL_POINTER, List.of(obj, cls), cls));
        Assert.assertFalse("a 1-argument node", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.CLASS_CAST, List.of(cls), cls));
        Assert.assertFalse("a 3-argument node", ObjRetRules.classCastMessageArgument(BytecodeExceptionKind.CLASS_CAST, List.of(obj, cls, obj), cls));
        Assert.assertFalse("not a bytecode exception node", ObjRetRules.classCastMessageArgument((jdk.graal.compiler.graph.Node) null, null));
    }

    // ------------------------------------------------------------------ two hooks, one-shot + PRECISE(empty)
    private static final ContainerTables.RTrackRefusal R = ContainerTables.RTrackRefusal.MISSING_IR;
    private static final ObjIdRules.Registrar RAW = (list, key, onEntry, onRefusal) -> list.register(new ContainerTables.Waiter(key, onEntry, null, onRefusal));

    /** One hook (the RT ObjretHook model): its births' lists, the shared one-shot flag, the fallback count, the deliveries. */
    static final class Hook {
        final List<ContainerTables.Table> tables = new ArrayList<>();
        final List<ContainerTables.EntryList<String>> lists = new ArrayList<>();
        final AtomicBoolean fell = new AtomicBoolean();
        final AtomicInteger fallbacks = new AtomicInteger();
        final List<String> delivered = java.util.Collections.synchronizedList(new ArrayList<>());

        Hook(String name, int births) {
            for (int i = 0; i < births; i++) {
                ContainerTables.Table t = new ContainerTables.Table(name + i, false);
                tables.add(t);
                lists.add(new ContainerTables.EntryList<>(t, "entryPaths"));
            }
            ObjIdRules.wireUnion(fell, lists, l -> List.of(name, l.table.owner), RAW, (l, idx) -> delivered.add(l.get(idx)), (l, r) -> fallbacks.incrementAndGet());
        }

        int entries() {
            int n = 0;
            for (ContainerTables.EntryList<String> l : lists) {
                n += l.size();
            }
            return n;
        }
    }

    private static boolean emptyRule(List<Hook> hooks) {
        return ObjIdRules.emptyRule(hooks, h -> h.fell, Hook::entries, h -> h.fallbacks.incrementAndGet());
    }

    @Test
    public void twoHooksOneShotAndPreciseEmpty() {
        ContainerTables.DEFER = Runnable::run;
        Hook a = new Hook("a", 2);
        Hook b = new Hook("b", 1);
        List<Hook> hooks = List.of(a, b);
        a.lists.get(1).append("a@1", "a@1");
        // the fixpoint: a delivered, b is PRECISE(empty): only b falls back, once
        Assert.assertTrue(emptyRule(hooks));
        Assert.assertEquals(0, a.fallbacks.get());
        Assert.assertEquals(1, b.fallbacks.get());
        Assert.assertEquals(List.of("a@1"), a.delivered);
        // the next boundary: nothing left to do (the drain may stop)
        Assert.assertFalse(emptyRule(hooks));
        // b's table refuses later: the refusal fallback shares b's one-shot flag (no second fallback)
        b.tables.get(0).refuse(R);
        Assert.assertEquals(1, b.fallbacks.get());
        // b's later entry is still delivered (a pure union after the fallback)
        b.lists.get(0).append("b@2", "b@2");
        Assert.assertEquals(List.of("b@2"), b.delivered);
        // a refuses: its one fallback (refusal side); a later empty rule never runs it again
        a.tables.get(0).refuse(R);
        a.tables.get(1).refuse(ContainerTables.RTrackRefusal.CLASS_ESCAPE);
        Assert.assertEquals(1, a.fallbacks.get());
        Assert.assertFalse(emptyRule(hooks));
        Assert.assertEquals(1, a.fallbacks.get());
        // a hook whose refusal came first is never PRECISE(empty)-ed afterwards
        Hook c = new Hook("c", 1);
        c.tables.get(0).refuse(R);
        Assert.assertEquals(1, c.fallbacks.get());
        Assert.assertFalse(emptyRule(List.of(c)));
        Assert.assertEquals(1, c.fallbacks.get());
    }

    // ------------------------------------------------------------------ ID-DEP propagation
    private final Map<ContainerTables.Table, ContainerTables.EntryList<String>> lists = new HashMap<>();

    private ContainerTables.EntryList<String> list(ContainerTables.Table t) {
        return lists.computeIfAbsent(t, k -> new ContainerTables.EntryList<>(k, "entryPaths"));
    }

    @Test
    public void idDepTravelsAlongWaiterAndListenerEdges() {
        ContainerTables.DEFER = Runnable::run;
        ContainerTables.Table src = new ContainerTables.Table("src", false);
        ContainerTables.Table mid = new ContainerTables.Table("mid", false);
        ContainerTables.Table off = new ContainerTables.Table("off", false);
        ContainerTables.Sink sink = new ContainerTables.Sink("sink", 100, 100);
        ContainerTables.Table reader = new ContainerTables.Table("reader", false);
        // mid reads src (a refusal-target waiter); sink reads mid (a backward-walk waiter); reader listens to sink
        list(src).register(new ContainerTables.Waiter("w1", i -> {
        }, null, r -> {
        }, mid));
        list(mid).register(new ContainerTables.Waiter("w2", i -> {
        }, null, r -> {
        }, sink));
        sink.addListener(new ContainerTables.Listener("l1", a -> {
        }, r -> {
        }, reader));
        // a waiter with a fallback (no refusal target) but an explicit dependent (the owner-return waiter)
        list(src).register(new ContainerTables.Waiter("w3", i -> {
        }, null, r -> {
        }, null, off));
        Assert.assertFalse(src.idDep() || mid.idDep() || sink.idDep() || reader.idDep() || off.idDep());
        long untargeted = ContainerTables.ID_DEP_UNTARGETED.sum();
        ContainerTables.markIdDep(src);
        Assert.assertTrue(src.idDep() && mid.idDep() && sink.idDep() && reader.idDep() && off.idDep());
        Assert.assertEquals(untargeted, ContainerTables.ID_DEP_UNTARGETED.sum());
        // a reader registering LATER on an ID-DEP table is marked at registration (a dependence on its refusal state)
        ContainerTables.Table late = new ContainerTables.Table("late", false);
        list(src).register(new ContainerTables.Waiter("w4", i -> {
        }, null, r -> {
        }, late));
        Assert.assertTrue(late.idDep());
        // an unaudited reader (no target) is counted; NO_READER stops silently
        list(src).register(new ContainerTables.Waiter("w5", i -> {
        }, null, r -> {
        }, null, null));
        Assert.assertEquals(untargeted + 1, ContainerTables.ID_DEP_UNTARGETED.sum());
        list(src).register(new ContainerTables.Waiter("w6", i -> {
        }, null, r -> {
        }, null, ContainerTables.NO_READER));
        Assert.assertEquals(untargeted + 1, ContainerTables.ID_DEP_UNTARGETED.sum());
        // marking is monotone and idempotent; it never refuses
        ContainerTables.markIdDep(src);
        Assert.assertTrue(src.refusalsSnapshot().isEmpty() && mid.refusalsSnapshot().isEmpty() && !sink.refused());
        // a cycle terminates
        ContainerTables.Table x = new ContainerTables.Table("x", false);
        ContainerTables.Table y = new ContainerTables.Table("y", false);
        list(x).register(new ContainerTables.Waiter("xy", i -> {
        }, null, r -> {
        }, y));
        list(y).register(new ContainerTables.Waiter("yx", i -> {
        }, null, r -> {
        }, x));
        ContainerTables.markIdDep(x);
        Assert.assertTrue(x.idDep() && y.idDep());
    }

    // ------------------------------------------------------------------ the cross-candidate precedence (equals conflict)
    private static InstrumentationDecision decision(OptimizationType t, String variant, String loc, boolean idDep) {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex v = graph.newVertex();
        v.setEnclosingClassName("TestUserClass");
        v.setSourceLocation(loc);
        if (idDep) {
            v.markIdDep();
        }
        return new InstrumentationDecision(v, t, variant);
    }

    @Test
    public void idDepAdmitNeverDemotesANonIdDepOne() {
        // without ID-DEP: the plain conflict rule (the identity at objret=0)
        InstrumentationDecision sv = decision(OptimizationType.STRING_VIEW, null, "A.java:1", false);
        InstrumentationDecision rope = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:2", false);
        Assert.assertEquals(HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv), List.of(rope)), HeuristicOrchestrator.crossRepEqualsRevertsIdDep(List.of(sv), List.of(rope)));
        // an ID-DEP SV (higher priority) vs a non-ID-DEP lazy rep: the ID-DEP one is dropped, the lazy one stays
        InstrumentationDecision svDep = decision(OptimizationType.STRING_VIEW, null, "A.java:3", true);
        Assert.assertEquals(List.of(rope), HeuristicOrchestrator.crossRepEqualsReverts(List.of(svDep), List.of(rope)));
        Assert.assertEquals(List.of(svDep), HeuristicOrchestrator.crossRepEqualsRevertsIdDep(List.of(svDep), List.of(rope)));
        // an ID-DEP lazy rep vs a non-ID-DEP SV: the lazy (ID-DEP) one is reverted either way
        InstrumentationDecision ropeDep = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:4", true);
        Assert.assertEquals(List.of(ropeDep), HeuristicOrchestrator.crossRepEqualsRevertsIdDep(List.of(sv), List.of(ropeDep)));
        // non-ID-DEP decisions conflicting among themselves keep the knob-0 outcome; every involved ID-DEP one goes
        InstrumentationDecision fixed4 = decision(OptimizationType.LAZY_CONCAT, "FIXED4", "A.java:5", false);
        List<InstrumentationDecision> r = HeuristicOrchestrator.crossRepEqualsRevertsIdDep(List.of(sv, svDep), List.of(rope, fixed4));
        Assert.assertTrue(r.containsAll(HeuristicOrchestrator.crossRepEqualsReverts(List.of(sv), List.of(rope, fixed4))));
        Assert.assertTrue(r.contains(svDep));
        Assert.assertFalse(r.contains(sv));
        // only ID-DEP decisions involved: the normal rule among them
        InstrumentationDecision rope2Dep = decision(OptimizationType.LAZY_CONCAT, "ROPE", "A.java:6", true);
        Assert.assertEquals(HeuristicOrchestrator.crossRepEqualsReverts(List.of(svDep), List.of(rope2Dep)), HeuristicOrchestrator.crossRepEqualsRevertsIdDep(List.of(svDep), List.of(rope2Dep)));
        Assert.assertTrue(HeuristicOrchestrator.idDepMixed(List.of(sv, svDep)));
        Assert.assertFalse(HeuristicOrchestrator.idDepMixed(List.of(sv, rope)));
    }

    // ------------------------------------------------------------------ the guard-trip rerun decision
    @Test
    public void rerunDecisionTruthTable() {
        for (int mask = 0; mask < 16; mask++) {
            boolean deliver = (mask & 1) != 0;
            boolean premise = (mask & 2) != 0;
            int usable = (mask & 4) != 0 ? 3 : 0;
            boolean tripped = (mask & 8) != 0;
            Assert.assertEquals("row " + mask, mask == 15, StringAnalysisForkSupport.objretRerunDecision(deliver, premise, usable, tripped));
        }
        List<String> cmd = List.of("java", "-Xmx1g", "-Dsvm.stringanalysis.fwd.rtrack.objret=1", "--module", "x/y.Main", "-H:+StringAnalysisFork");
        List<String> rc = StringAnalysisForkSupport.rerunCommand(cmd, cmd.indexOf("--module"));
        // the rerun is a plain objret=0 child (census off too)
        Assert.assertEquals(List.of("java", "-Xmx1g", "-Dsvm.stringanalysis.fwd.rtrack.objret=1", "-Dsvm.stringanalysis.fwd.rtrack.objret=0", "-Dsvm.stringanalysis.fwd.rtrack.objret.census=0",
                        "--module", "x/y.Main", "-H:+StringAnalysisFork"), rc);
        Assert.assertTrue("the objret=0 option comes after the inherited one (the last -D wins)",
                        rc.indexOf("-Dsvm.stringanalysis.fwd.rtrack.objret=0") > rc.indexOf("-Dsvm.stringanalysis.fwd.rtrack.objret=1"));
    }

    // ------------------------------------------------------------------ the lookahead correspondence guard
    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static ResolvedJavaMethod method(Class<?> c, String name) {
        ResolvedJavaType t = META.lookupJavaType(c);
        ResolvedJavaMethod found = null;
        for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
            if (m.getName().equals(name)) {
                Assert.assertNull("one method named " + name, found);
                found = m;
            }
        }
        Assert.assertNotNull(name, found);
        return found;
    }

    /** The engine classes whose calls {@link #rows} lists: the tracking engine and its rule classes, the JDK models, ObjRetRules. */
    private static final List<String> ENGINE_CLASSES = List.of("RecursiveTracking", "HolderEndRule", "ThreadLocalModel", "ObjectReturnRule", "ObjectIdentityRule", "ClosedFieldEscape",
                    "ReflectionBridgeCrossings", "WorldTopRule", "ReverseHeapIndex", "JdkModelEngine", "ObjRetRules");

    /** The bytecode rows of {@code m}: every instanceof target (simple name) and every call of a method of the engine classes, in order. */
    private static List<String> rows(ResolvedJavaMethod m, boolean types, boolean calls) {
        List<String> out = new ArrayList<>();
        Assert.assertNotNull("bytecode of " + m.getName(), m.getCode());
        BytecodeStream bs = new BytecodeStream(m.getCode());
        ConstantPool cp = m.getConstantPool();
        while (bs.currentBC() != Bytecodes.END) {
            int bc = bs.currentBC();
            if (types && bc == Bytecodes.INSTANCEOF) {
                JavaType jt = cp.lookupType(bs.readCPI(), bc);
                String n = jt.toJavaName(false);
                out.add("instanceof " + n.substring(n.lastIndexOf('.') + 1));
            } else if (calls && (bc == Bytecodes.INVOKEVIRTUAL || bc == Bytecodes.INVOKESPECIAL || bc == Bytecodes.INVOKESTATIC || bc == Bytecodes.INVOKEINTERFACE)) {
                JavaMethod jm = cp.lookupMethod(bs.readCPI(), bc, m);
                String h = jm.getDeclaringClass().toJavaName(false);
                if (ENGINE_CLASSES.contains(h)) {
                    out.add(h + "." + jm.getName());
                }
            }
            bs.next();
        }
        return out;
    }

    /**
     * The lookahead trigger ({@link ObjRetRules#pureForwarder} / {@code certainRefusalOf}) is
     * sound for monotonicity only while {@code classifyUsage}'s Phi / proxy / conditional / Return rows forward a value
     * unchanged and {@code returnCase} tries its branches (DesugaredCall, model, fold, path, STATIC, OWNER, then rule U
     * and the fan) in this order. This pin fails on any change of the row set / order or of the branch order: re-check
     * the monotonicity argument (pureForwarder's accepted uses must still be exactly the forwarding rows).
     */
    @Test
    public void lookaheadCorrespondenceGuard() {
        List<String> cu = rows(method(RecursiveTracking.class, "classifyUsage"), true, false);
        List<String> rc = rows(method(RecursiveTracking.class, "returnCase"), false, true);
        Assert.assertEquals("classifyUsage rows changed: re-check the lookahead argument", CLASSIFY_USAGE_ROWS, cu);
        Assert.assertEquals("returnCase branch order changed: re-check the lookahead argument", RETURN_CASE_ROWS, rc);
    }

    /** The rows of classifyUsage in order (the Phi / proxy / conditional / Return rows are the ones the lookahead relies on). */
    static final List<String> CLASSIFY_USAGE_ROWS = List.of(
                    "instanceof ObjectClone",
                    "instanceof ValueNode",
                    "instanceof StoreFieldNode",
                    "instanceof LoadFieldNode",
                    "instanceof StoreIndexedNode",
                    "instanceof LoadIndexedNode",
                    "instanceof BasicArrayCopyNode",
                    "instanceof ObjectClone",
                    "instanceof CommitAllocationNode",
                    "instanceof VirtualState",
                    "instanceof FrameState",
                    "instanceof MethodCallTargetNode",
                    "instanceof IndirectCallTargetNode",
                    "instanceof ReturnNode",
                    "instanceof UnwindNode",
                    "instanceof StoreVMThreadLocalNode",
                    "instanceof CompareAndSetVMThreadLocalNode",
                    "instanceof PiNode",
                    "instanceof LimitedValueProxy",
                    "instanceof PhiNode",
                    "instanceof ConditionalNode",
                    "instanceof BytecodeExceptionNode",
                    "instanceof IdentityHashCodeNode");
    /** The engine calls of returnCase in order (the branch order: concat / model / fold / path / STATIC / OWNER, then rule U, the identity return and the fan). */
    static final List<String> RETURN_CASE_ROWS = List.of(
                    "RecursiveTracking.concatOperandArrival",
                    "JdkModelEngine.returnArrival",
                    "RecursiveTracking.returnAlongFold",
                    "RecursiveTracking.invokesOf",
                    "RecursiveTracking.refuse",
                    "RecursiveTracking.restored",
                    "RecursiveTracking.enqueueWalk",
                    "RecursiveTracking.invokesByBci",
                    "RecursiveTracking.refuse",
                    "RecursiveTracking.enqueueWalk",
                    "RecursiveTracking.internKey",
                    "WorldTopRule.outsideCaller",
                    "WorldTopRule.e2Note",
                    "RecursiveTracking.refuse",
                    "HolderEndRule.waitRec",
                    "RecursiveTracking.register", // the owner waiter (with the fallback to the caller fan)
                    "ObjectReturnRule.objretReturn",
                    "ObjectIdentityRule.idReturn",
                    "RecursiveTracking.returnAllCallers");
}
