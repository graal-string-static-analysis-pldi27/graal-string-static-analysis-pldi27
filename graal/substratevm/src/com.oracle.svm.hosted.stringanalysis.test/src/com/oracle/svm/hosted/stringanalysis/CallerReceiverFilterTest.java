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

import java.lang.annotation.Annotation;
import java.lang.reflect.AnnotatedElement;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.java.GraphBuilderPhase;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.OptimisticOptimizations;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Decision pins of the receiver-typed caller filter for path-less caller fans
 * ({@link DispatchResolution#callerSiteDecision}, {@link DispatchResolution#keepNeverEmpty},
 * {@link WorldTopRule#callerSiteReason}), on real AnalysisTypes. A caller site of a frame of method M is dropped
 * only when the call's final points-to receiver types all resolve, inside the call's CHA fan, to methods other than M
 * (the caller premise: the child's final unsaturated receiver state contains the exact class of every run-time
 * receiver). Every doubt keeps the site; the list is never emptied; non-LFG sites (IR-index, reflection bridge) are
 * kept without consulting the points-to state; knob 0 is the identity. These pin the decisions (literal tables over a
 * hierarchy with default methods, bridges, an abstract middle class and a cross-package package-private non-override).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.nodes.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf", "jdk.graal.compiler/jdk.graal.compiler.java",
                "jdk.graal.compiler/jdk.graal.compiler.phases", "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual", "jdk.graal.compiler/jdk.graal.compiler.nodes.util",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type", "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.gc", "jdk.graal.compiler/jdk.graal.compiler.nodes.loop",
                "jdk.internal.vm.ci/jdk.vm.ci.common", "jdk.graal.compiler/jdk.graal.compiler.phases.util", "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class CallerReceiverFilterTest {

    interface Fn {
        Object apply(Object o);
    }

    static final class A implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    static final class B implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    static final class Outside implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    static class Base implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }

        static Object st(Object o) {
            return o;
        }
    }

    static final class Heir extends Base {
    }

    // the hierarchy cases
    interface Dflt {
        default Object run(Object o) {
            return o;
        }
    }

    static final class DUse implements Dflt {
    }

    static final class DOver implements Dflt {
        @Override
        public Object run(Object o) {
            return o;
        }
    }

    interface Gen<T> {
        T get(T t);
    }

    /** javac emits the bridge {@code Object get(Object)} that calls {@code String get(String)}. */
    static final class Spec implements Gen<String> {
        @Override
        public String get(String s) {
            return s;
        }
    }

    static class CBase {
        Object make() {
            return null;
        }
    }

    /** A covariant override: javac emits the bridge {@code Object make()} that calls {@code String make()}. */
    static final class CSub extends CBase {
        @Override
        String make() {
            return "";
        }
    }

    abstract static class Mid implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    /** Inherits {@code Mid.apply} through the abstract middle class. */
    static final class Leaf extends Mid {
    }

    static final class Leaf2 extends Mid {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    /** A JVMCI-backed analysis universe (the ChaAbstractRootLoopTest fixture). */
    private static final class World {
        final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        final AnalysisUniverse universe;

        World(Class<?>... lookups) {
            AnnotationExtractor annotations = new AnnotationExtractor() {
                @Override
                public boolean hasAnnotation(AnnotatedElement element, Class<? extends Annotation> annotationType) {
                    return element.isAnnotationPresent(annotationType);
                }

                @Override
                public <T extends Annotation> T extractAnnotation(AnnotatedElement element, Class<T> annotationType, boolean declaredOnly) {
                    return declaredOnly ? element.getDeclaredAnnotation(annotationType) : element.getAnnotation(annotationType);
                }

                @Override
                @SuppressWarnings("unchecked")
                public Class<? extends Annotation>[] getAnnotationTypes(AnnotatedElement element) {
                    return Arrays.stream(element.getAnnotations()).map(Annotation::annotationType).toArray(Class[]::new);
                }
            };
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), CallerReceiverFilterTest.class.getClassLoader()) {
                @Override
                public void onTypeReachable(BigBang bb, AnalysisType type) {
                    // no-op
                }

                @Override
                public boolean isInitialized(AnalysisType type) {
                    return true;
                }

                @Override
                public GraphBuilderPhase.Instance createGraphBuilderPhase(com.oracle.graal.pointsto.meta.HostedProviders providers,
                                GraphBuilderConfiguration config, OptimisticOptimizations optimizations, IntrinsicContext intrinsicContext) {
                    return null;
                }

                @Override
                public Comparator<? super ResolvedJavaType> getTypeComparator() {
                    return null;
                }
            };
            this.universe = new AnalysisUniverse(host, JavaKind.Object, new DefaultAnalysisPolicy(new OptionValues(EconomicMap.create())),
                            SubstitutionProcessor.IDENTITY, metaAccess, new PointsToAnalysisFactory(), annotations);
            type(Object.class);
            type(Cloneable.class); // the universe's own bootstrap order (AnalysisType's constructor reads Cloneable)
            type(java.io.Serializable.class);
            type(String.class);
            type(void.class); // the fixture methods' signature types, created before the stand-in below
            // every fixture type is in the universe (so in its supertypes' subtype sets) before anything is instantiated
            for (Class<?> c : lookups) {
                type(c);
            }
            /*
             * registerAsInstantiated and method creation call the analysis; a no-op stand-in answers null/false. Every
             * type exists by now: a type created later would register itself with the stand-in and fail loudly.
             */
            universe.setBigBang((BigBang) Proxy.newProxyInstance(BigBang.class.getClassLoader(), new Class<?>[]{BigBang.class},
                            (proxy, m, args) -> noOp(proxy, m, args)));
        }

        AnalysisType type(Class<?> c) {
            ResolvedJavaType t = metaAccess.lookupJavaType(c);
            t.link(); // HotSpot resolves a concrete method only on a linked type
            return universe.lookup(t);
        }

        AnalysisMethod method(Class<?> c, String name) {
            try {
                return universe.lookup(metaAccess.lookupJavaMethod(c.getDeclaredMethod(name)));
            } catch (NoSuchMethodException e) {
                throw new AssertionError(e);
            }
        }
    }

    private static Object noOp(Object proxy, Method m, Object[] args) {
        switch (m.getName()) {
            case "equals":
                return proxy == args[0];
            case "hashCode":
                return System.identityHashCode(proxy);
            case "toString":
                return "CallerReceiverFilterTest.NoOpBigBang";
            default:
                break;
        }
        Class<?> r = m.getReturnType();
        if (r == boolean.class) {
            return false;
        }
        if (r.isPrimitive() && r != void.class) {
            return defaultPrimitive(r);
        }
        return null;
    }

    private static Object defaultPrimitive(Class<?> r) {
        if (r == long.class) {
            return 0L;
        } else if (r == float.class) {
            return 0f;
        } else if (r == double.class) {
            return 0d;
        } else if (r == short.class) {
            return (short) 0;
        } else if (r == byte.class) {
            return (byte) 0;
        } else if (r == char.class) {
            return (char) 0;
        }
        return 0;
    }

    private static DispatchResolution.ResolvedTarget target(AnalysisMethod m) {
        return new DispatchResolution.ResolvedTarget(m, null, null, false, m.getDeclaringClass().toJavaName(true));
    }

    private static final Class<?>[] ALL = {Fn.class, A.class, B.class, Outside.class, Base.class, Heir.class};

    private static AnalysisMethod apply(World w, Class<?> c) {
        try {
            return w.universe.lookup(w.metaAccess.lookupJavaMethod(c.getDeclaredMethod("apply", Object.class)));
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
    }

    private static List<DispatchResolution.ResolvedTarget> fan(World w) {
        return List.of(target(apply(w, A.class)), target(apply(w, B.class)), target(apply(w, Base.class)));
    }

    private static final Class<?>[] HIER = {Fn.class, A.class, B.class, Outside.class, Base.class, Heir.class, Dflt.class, DUse.class, DOver.class, Gen.class, Spec.class, CBase.class,
                    CSub.class, Mid.class, Leaf.class, Leaf2.class, PackagePrivateBase.class, com.oracle.svm.hosted.stringanalysis.otherpackage.PackagePrivateSub.class};

    private static AnalysisMethod declared(World w, Class<?> c, String name, Class<?>... params) {
        try {
            return w.universe.lookup(w.metaAccess.lookupJavaMethod(c.getDeclaredMethod(name, params)));
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
    }

    /** The one bridge (or the one non-bridge) method {@code name} declared by {@code c}. */
    private static AnalysisMethod declared(World w, Class<?> c, String name, boolean bridge) {
        Method found = null;
        for (Method m : c.getDeclaredMethods()) {
            if (m.getName().equals(name) && m.isBridge() == bridge) {
                Assert.assertNull("one " + (bridge ? "bridge" : "method") + " " + name + " in " + c, found);
                found = m;
            }
        }
        Assert.assertNotNull(name + " in " + c + " bridge=" + bridge, found);
        return w.universe.lookup(w.metaAccess.lookupJavaMethod(found));
    }

    private static List<DispatchResolution.ResolvedTarget> fanOf(AnalysisMethod... ms) {
        List<DispatchResolution.ResolvedTarget> out = new ArrayList<>();
        for (AnalysisMethod m : ms) {
            out.add(target(m));
        }
        return out;
    }

    private static String decide(World w, AnalysisMethod callee, AnalysisMethod frame, List<DispatchResolution.ResolvedTarget> fan, Class<?>... receivers) {
        List<AnalysisType> types = new ArrayList<>();
        for (Class<?> r : receivers) {
            types.add(w.type(r));
        }
        return DispatchResolution.callerSiteDecision(types, callee, frame, fan);
    }

    /** An interface default method is the frame of every implementor that does not override it. */
    @Test
    public void defaultMethodTable() {
        World w = new World(HIER);
        AnalysisMethod callee = declared(w, Dflt.class, "run", Object.class);
        AnalysisMethod over = declared(w, DOver.class, "run", Object.class);
        List<DispatchResolution.ResolvedTarget> fan = fanOf(callee, over);
        Assert.assertEquals("dispatches", decide(w, callee, callee, fan, DUse.class));
        Assert.assertEquals("drop", decide(w, callee, callee, fan, DOver.class));
        Assert.assertEquals("dispatches", decide(w, callee, callee, fan, DOver.class, DUse.class));
        Assert.assertEquals("drop", decide(w, callee, over, fan, DUse.class));
        Assert.assertEquals("dispatches", decide(w, callee, over, fan, DOver.class));
    }

    /**
     * Bridges. A call to the erased interface method on a receiver of the generic implementor dispatches to
     * the synthetic bridge (whose own call to the specific method is a separate, direct site), never to the specific
     * method itself; the same for a covariant-return override reached through the superclass method.
     */
    @Test
    public void bridgeTable() {
        World w = new World(HIER);
        AnalysisMethod gen = declared(w, Gen.class, "get", Object.class);
        AnalysisMethod specBridge = declared(w, Spec.class, "get", true);
        AnalysisMethod specReal = declared(w, Spec.class, "get", false);
        Assert.assertTrue(specBridge.isBridge());
        Assert.assertFalse(specReal.isBridge());
        List<DispatchResolution.ResolvedTarget> gfan = fanOf(specBridge);
        Assert.assertEquals("dispatches", decide(w, gen, specBridge, gfan, Spec.class));
        Assert.assertEquals("drop", decide(w, gen, specReal, gfan, Spec.class));

        AnalysisMethod cbase = declared(w, CBase.class, "make");
        AnalysisMethod csubBridge = declared(w, CSub.class, "make", true);
        AnalysisMethod csubReal = declared(w, CSub.class, "make", false);
        List<DispatchResolution.ResolvedTarget> cfan = fanOf(cbase, csubBridge);
        Assert.assertEquals("dispatches", decide(w, cbase, csubBridge, cfan, CSub.class));
        Assert.assertEquals("drop", decide(w, cbase, csubReal, cfan, CSub.class));
        Assert.assertEquals("drop", decide(w, cbase, cbase, cfan, CSub.class));
        Assert.assertEquals("dispatches", decide(w, cbase, cbase, cfan, CBase.class));
        Assert.assertEquals("dispatches", decide(w, cbase, cbase, cfan, CSub.class, CBase.class));
    }

    /** An abstract middle class's method is the frame of a concrete heir that does not override it. */
    @Test
    public void abstractMiddleTable() {
        World w = new World(HIER);
        AnalysisMethod fn = apply(w, Fn.class);
        AnalysisMethod mid = apply(w, Mid.class);
        AnalysisMethod leaf2 = apply(w, Leaf2.class);
        List<DispatchResolution.ResolvedTarget> fan = fanOf(mid, leaf2);
        Assert.assertEquals("dispatches", decide(w, fn, mid, fan, Leaf.class));
        Assert.assertEquals("drop", decide(w, fn, mid, fan, Leaf2.class));
        Assert.assertEquals("dispatches", decide(w, fn, mid, fan, Leaf2.class, Leaf.class));
        Assert.assertEquals("drop", decide(w, fn, leaf2, fan, Leaf.class));
        Assert.assertEquals("declared callee = the abstract class's method", "dispatches", decide(w, mid, mid, fan, Leaf.class));
        Assert.assertEquals("drop", decide(w, mid, mid, fan, Leaf2.class));
    }

    /**
     * A package-private method redeclared in a subclass of another package does not override it (HotSpot
     * LinkResolver semantics): a receiver of the subclass dispatches to the base method, never to the subclass's.
     */
    @Test
    public void packagePrivateTable() {
        World w = new World(HIER);
        AnalysisMethod base = declared(w, PackagePrivateBase.class, "m", Object.class);
        AnalysisMethod sub = declared(w, com.oracle.svm.hosted.stringanalysis.otherpackage.PackagePrivateSub.class, "m", Object.class);
        List<DispatchResolution.ResolvedTarget> fan = fanOf(base);
        Assert.assertEquals("dispatches", decide(w, base, base, fan, com.oracle.svm.hosted.stringanalysis.otherpackage.PackagePrivateSub.class));
        Assert.assertEquals("drop", decide(w, base, sub, fan, com.oracle.svm.hosted.stringanalysis.otherpackage.PackagePrivateSub.class));
        Assert.assertEquals("dispatches", decide(w, base, base, fan, PackagePrivateBase.class));
    }

    /** The IR-level keeps (an inlined scope first, then a direct invoke kind such as invokespecial). */
    @Test
    public void irKeepReasons() {
        Assert.assertEquals("direct", WorldTopRule.irKeepReason(false, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Special));
        Assert.assertEquals("direct", WorldTopRule.irKeepReason(false, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Static));
        Assert.assertNull(WorldTopRule.irKeepReason(false, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Virtual));
        Assert.assertNull(WorldTopRule.irKeepReason(false, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Interface));
        Assert.assertNull(WorldTopRule.irKeepReason(false, null));
        Assert.assertEquals("inlined", WorldTopRule.irKeepReason(true, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Virtual));
        Assert.assertEquals("inlined", WorldTopRule.irKeepReason(true, jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Special));
        Assert.assertEquals("inlined", WorldTopRule.irKeepReason(true, null));
    }

    /** The filter runs on a non-empty list only. */
    @Test
    public void fanOrAllFiltersOnlyANonEmptyList() {
        List<String> all = List.of("a", "b");
        boolean[] ran = {false};
        java.util.function.UnaryOperator<List<String>> f = l -> {
            ran[0] = true;
            return List.of("a");
        };
        Assert.assertEquals(List.of("a"), WorldTopRule.fanOrAll(all, f));
        Assert.assertTrue(ran[0]);
        ran[0] = false;
        Assert.assertTrue(WorldTopRule.fanOrAll(List.<String> of(), f).isEmpty());
        Assert.assertNull(WorldTopRule.fanOrAll(null, f));
        Assert.assertFalse(ran[0]);
    }

    /** The site-level table: drop iff every receiver type resolves inside the fan to a method other than the frame's. */
    @Test
    public void dropOnlyWhenNoReceiverDispatchesToTheFrame() {
        World w = new World(ALL);
        AnalysisMethod callee = apply(w, Fn.class);
        AnalysisMethod a = apply(w, A.class);
        AnalysisMethod base = apply(w, Base.class);
        List<DispatchResolution.ResolvedTarget> fan = fan(w);
        Assert.assertEquals("drop", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), callee, a, fan));
        Assert.assertEquals("drop", DispatchResolution.callerSiteDecision(List.of(w.type(B.class), w.type(Heir.class)), callee, a, fan));
        Assert.assertEquals("dispatches", DispatchResolution.callerSiteDecision(List.of(w.type(A.class)), callee, a, fan));
        Assert.assertEquals("one receiver of M among others keeps", "dispatches", DispatchResolution.callerSiteDecision(List.of(w.type(B.class), w.type(A.class)), callee, a, fan));
        Assert.assertEquals("an heir inheriting M dispatches to M", "dispatches", DispatchResolution.callerSiteDecision(List.of(w.type(Heir.class)), callee, base, fan));
        Assert.assertEquals("an heir inheriting another method is no receiver of M", "drop", DispatchResolution.callerSiteDecision(List.of(w.type(Heir.class)), callee, a, fan));
    }

    /** Every doubt keeps the site. */
    @Test
    public void everyDoubtKeepsTheSite() {
        World w = new World(ALL);
        AnalysisMethod callee = apply(w, Fn.class);
        AnalysisMethod a = apply(w, A.class);
        List<DispatchResolution.ResolvedTarget> fan = fan(w);
        Assert.assertEquals("noTypes", DispatchResolution.callerSiteDecision(null, callee, a, fan));
        Assert.assertEquals("empty", DispatchResolution.callerSiteDecision(List.of(), callee, a, fan));
        Assert.assertEquals("a resolution outside the fan", "typeOutsideFan", DispatchResolution.callerSiteDecision(List.of(w.type(B.class), w.type(Outside.class)), callee, a, fan));
        Assert.assertEquals("a type with no resolution", "typeOutsideFan", DispatchResolution.callerSiteDecision(List.of(w.type(Object.class)), callee, a, fan));
        Assert.assertEquals("an unknown (null) type", "typeOutsideFan", DispatchResolution.callerSiteDecision(Arrays.asList(w.type(B.class), null), callee, a, fan));
        Assert.assertEquals("no fan", "typeOutsideFan", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), callee, a, null));
        Assert.assertEquals("a statically bound callee (a final class's method)", "direct", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), a, apply(w, B.class), fan));
        AnalysisMethod st;
        try {
            st = w.universe.lookup(w.metaAccess.lookupJavaMethod(Base.class.getDeclaredMethod("st", Object.class)));
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
        Assert.assertEquals("a static callee", "direct", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), st, a, fan));
        Assert.assertEquals("a static frame", "direct", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), callee, st, fan));
        Assert.assertEquals("no frame method", "direct", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), callee, null, fan));
        Assert.assertEquals("no callee", "direct", DispatchResolution.callerSiteDecision(List.of(w.type(B.class)), null, a, fan));
    }

    /** The decision never drops a site one of whose receiver types reaches M (exhaustive over the fixture's type subsets). */
    @Test
    public void neverDropsASiteWithAReceiverOfTheFrame() {
        World w = new World(ALL);
        AnalysisMethod callee = apply(w, Fn.class);
        List<DispatchResolution.ResolvedTarget> fan = fan(w);
        AnalysisType[] types = {w.type(A.class), w.type(B.class), w.type(Outside.class), w.type(Base.class), w.type(Heir.class), w.type(Object.class)};
        for (AnalysisMethod frame : List.of(apply(w, A.class), apply(w, B.class), apply(w, Base.class))) {
            for (int mask = 1; mask < 1 << types.length; mask++) {
                List<AnalysisType> sel = new ArrayList<>();
                boolean reaches = false;
                for (int i = 0; i < types.length; i++) {
                    if ((mask & 1 << i) != 0) {
                        sel.add(types[i]);
                        AnalysisMethod r = types[i].resolveConcreteMethod(callee);
                        reaches |= r == null || r.equals(frame) || fan.stream().noneMatch(t -> t.method().equals(r));
                    }
                }
                String d = DispatchResolution.callerSiteDecision(sel, callee, frame, fan);
                if (reaches) {
                    Assert.assertNotEquals(frame + " " + sel, DispatchResolution.CALLER_DROP, d);
                }
            }
        }
    }

    /** The list-level rule: order kept; nothing dropped or everything dropped = the unfiltered list itself. */
    @Test
    public void theListIsNeverEmptied() {
        List<String> all = List.of("a", "b", "c");
        Assert.assertEquals(List.of("a", "c"), DispatchResolution.keepNeverEmpty(all, s -> !s.equals("b")));
        Assert.assertSame("everything dropped: the unfiltered list", all, DispatchResolution.keepNeverEmpty(all, s -> false));
        Assert.assertSame("nothing dropped: the list itself", all, DispatchResolution.keepNeverEmpty(all, s -> true));
        Assert.assertNull(DispatchResolution.keepNeverEmpty(null, s -> false));
        Assert.assertTrue(DispatchResolution.keepNeverEmpty(List.<String> of(), s -> false).isEmpty());
    }

    /** A bridge stand-in answering the receiver state and the fan; it records whether the points-to state was read. */
    private static RecursiveTracking.Bridge bridge(List<AnalysisType> types, String why, List<DispatchResolution.ResolvedTarget> fan, boolean[] consulted) {
        return (RecursiveTracking.Bridge) Proxy.newProxyInstance(RecursiveTracking.Bridge.class.getClassLoader(), new Class<?>[]{RecursiveTracking.Bridge.class}, (p, m, args) -> {
            switch (m.getName()) {
                case "pointsToReceiverTypes":
                    consulted[0] = true;
                    if (types == null) {
                        @SuppressWarnings("unchecked")
                        java.util.function.Consumer<String> c = (java.util.function.Consumer<String>) args[2];
                        c.accept(why);
                    }
                    return types;
                case "resolveCrossing":
                case "committedFan":
                    return fan;
                case "methodOf":
                    return null;
                case "hashCode":
                    return System.identityHashCode(p);
                case "equals":
                    return p == args[0];
                default:
                    throw new AssertionError("unexpected bridge call " + m.getName());
            }
        });
    }

    /** The site rule over the bridge: non-LFG sites kept unread; LFG sites read the final state; fallbacks named. */
    @Test
    public void siteRuleOverTheBridge() {
        World w = new World(ALL);
        AnalysisMethod callee = apply(w, Fn.class);
        AnalysisMethod a = apply(w, A.class);
        AnalysisMethod caller = apply(w, B.class); // any analysed method stands for the caller
        LocalFlowGraph.LocalVertex v = new LocalFlowGraph.LocalVertex(null, 0, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
        v.calleeMethod = callee;
        ForwardFixpoint.CallerSite site = new ForwardFixpoint.CallerSite(caller, v);
        Set<ForwardFixpoint.CallerSite> lfg = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        lfg.add(site);
        boolean[] consulted = {false};
        Assert.assertEquals("drop", WorldTopRule.callerSiteReason(bridge(List.of(w.type(B.class)), null, fan(w), consulted), a, site, lfg));
        Assert.assertTrue(consulted[0]);
        Assert.assertEquals("dispatches", WorldTopRule.callerSiteReason(bridge(List.of(w.type(A.class)), null, fan(w), consulted), a, site, lfg));
        Assert.assertEquals("pt:receiverSaturated", WorldTopRule.callerSiteReason(bridge(null, "receiverSaturated", fan(w), consulted), a, site, lfg));
        Assert.assertEquals("pt:invokeSaturated", WorldTopRule.callerSiteReason(bridge(null, "invokeSaturated", fan(w), consulted), a, site, lfg));
        Assert.assertEquals("pt:receiverAllInstantiated", WorldTopRule.callerSiteReason(bridge(null, "receiverAllInstantiated", fan(w), consulted), a, site, lfg));
        // a detached IR-index site or a reflection-bridge site (an equal record that is not the LFG's own object): kept, the state unread
        consulted[0] = false;
        ForwardFixpoint.CallerSite detached = new ForwardFixpoint.CallerSite(caller, v);
        Assert.assertEquals("notLfg", WorldTopRule.callerSiteReason(bridge(List.of(w.type(B.class)), null, fan(w), consulted), a, detached, lfg));
        Assert.assertFalse(consulted[0]);
        Assert.assertEquals("noCall", WorldTopRule.callerSiteReason(bridge(List.of(w.type(B.class)), null, fan(w), consulted), a, new ForwardFixpoint.CallerSite(caller, null), lfg));
        // a bridge that throws: kept
        RecursiveTracking.Bridge thrower = (RecursiveTracking.Bridge) Proxy.newProxyInstance(RecursiveTracking.Bridge.class.getClassLoader(), new Class<?>[]{RecursiveTracking.Bridge.class},
                        (p, m, args) -> {
                            throw new IllegalStateException("boom");
                        });
        Assert.assertEquals("exception", WorldTopRule.callerSiteReason(thrower, a, site, lfg));
    }
}
