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
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
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
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Lambda object-identity tracking pins: the qualification rule ({@link ObjIdRules#qualifies}) on real AnalysisTypes, the
 * guard's decision table and order ({@link ObjIdRules#guard}), the caller-set union with the one-shot fan
 * ({@link ObjIdRules#callerUnion}), the knob default, the class-escape predicate and the query key space
 * ({@link ObjectIdentityRule.IdSite}).
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
                "jdk.internal.vm.ci/jdk.vm.ci.common", "jdk.graal.compiler/jdk.graal.compiler.phases.util", "org.graalvm.nativeimage/org.graalvm.nativeimage.impl",
                "java.base/jdk.internal.reflect", "jdk.graal.compiler/jdk.graal.compiler.bytecode"})
public class ObjectIdentityTest {

    interface Fn {
        Object apply(Object o);
    }

    static final class Leaf implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }

        static Object st(Object o) {
            return o;
        }
    }

    static class Base implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    static final class Heir extends Base {
    }

    static class Lonely implements Fn {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    /** A subclass that exists but is never instantiated: Lonely still qualifies. */
    static final class LonelyHeir extends Lonely {
    }

    abstract static class Abs implements Fn {
    }

    /** G4 fixture: an interface whose only implementor is never instantiated. */
    interface Idle {
    }

    static final class Never implements Fn, Idle {
        @Override
        public Object apply(Object o) {
            return o;
        }
    }

    /** Closure fixtures: an int-only final record class, a holder of a Fn, a holder of an Object, an array holder. */
    static final class IntsOnly {
        int a;
        long b;
    }

    static final class HoldsFn {
        Fn f;
        IntsOnly i;
    }

    static final class HoldsObject {
        Object o;
    }

    static final class HoldsArr {
        HoldsFn[] fs;
        byte[] raw;
    }

    static final java.util.function.Function<String, String> LAMBDA = mk("cap");

    static java.util.function.Function<String, String> mk(String loc) {
        return k -> loc + k; // a capturing lambda: its class is a final hidden LMF class
    }

    static final Set<Class<?>> NOT_INSTANTIATED = Set.of(LonelyHeir.class, Never.class);

    private static final Class<?>[] ALL = {Fn.class, Idle.class, Leaf.class, Base.class, Heir.class, Lonely.class, LonelyHeir.class, Abs.class, Never.class, LAMBDA.getClass(),
                    IntsOnly.class, HoldsFn.class, HoldsObject.class, HoldsArr.class, HoldsFn[].class, byte[].class, Object[].class};

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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), ObjectIdentityTest.class.getClassLoader()) {
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
            type(int.class); // the closure fixtures' field types (a field's creation looks its type up)
            type(long.class);
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
            for (Class<?> c : lookups) {
                if (!c.isInterface() && !java.lang.reflect.Modifier.isAbstract(c.getModifiers()) && !NOT_INSTANTIATED.contains(c)) {
                    type(c).registerAsInstantiated("ObjectIdentityTest fixture");
                }
            }
        }

        private final java.util.Map<AnalysisType, Class<?>> classes = new java.util.HashMap<>();

        AnalysisType type(Class<?> c) {
            ResolvedJavaType t = metaAccess.lookupJavaType(c);
            t.link(); // HotSpot resolves a concrete method only on a linked type
            AnalysisType at = universe.lookup(t);
            classes.put(at, c);
            return at;
        }

        /** The fixture's hosted Class of a looked-up type (production: {@code AnalysisType.getJavaClass}). */
        Class<?> javaClass(AnalysisType t) {
            return classes.get(t);
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
                return "ObjectIdentityTest.NoOpBigBang";
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

    @Test
    public void qualificationTableIsOrderedAndComplete() {
        for (int bits = 0; bits < 32; bits++) {
            boolean st = (bits & 1) != 0;
            boolean ai = (bits & 2) != 0;
            boolean inst = (bits & 4) != 0;
            boolean sub = (bits & 8) != 0;
            boolean hidden = (bits & 16) != 0;
            ObjIdRules.NoQualify expect = st ? ObjIdRules.NoQualify.STATIC
                            : !hidden ? ObjIdRules.NoQualify.NOT_HIDDEN
                                            : ai ? ObjIdRules.NoQualify.ABSTRACT_OR_INTERFACE
                                                            : !inst ? ObjIdRules.NoQualify.NOT_INSTANTIATED : sub ? ObjIdRules.NoQualify.INSTANTIATED_SUBTYPE : null;
            Assert.assertEquals("bits=" + bits, expect, ObjIdRules.qualifies(st, hidden, ai, inst, sub));
        }
    }

    @Test
    public void qualificationOnRealTypes() {
        World w = new World(ALL);
        // an ordinary class never qualifies, whatever its shape (the fan); only hidden (lambda) classes
        for (Class<?> c : new Class<?>[]{Leaf.class, Base.class, Lonely.class, Never.class}) {
            Assert.assertEquals(c.getSimpleName() + " is not hidden", ObjIdRules.NoQualify.NOT_HIDDEN, ObjIdRules.qualifies(false, w.type(c), w::javaClass));
        }
        Assert.assertEquals(ObjIdRules.NoQualify.STATIC, ObjIdRules.qualifies(true, w.type(Leaf.class), w::javaClass));
        Assert.assertEquals("an interface is not hidden either", ObjIdRules.NoQualify.NOT_HIDDEN, ObjIdRules.qualifies(false, w.type(Fn.class), w::javaClass));
        AnalysisType lam = w.type(LAMBDA.getClass());
        Assert.assertTrue("an LMF class is final", lam.isFinalFlagSet());
        Assert.assertTrue("an LMF class is hidden", LAMBDA.getClass().isHidden());
        Assert.assertNull("a capturing lambda class qualifies", ObjIdRules.qualifies(false, lam, w::javaClass));
        Assert.assertEquals("a static frame of a lambda class", ObjIdRules.NoQualify.STATIC, ObjIdRules.qualifies(true, lam, w::javaClass));
        // the remaining structural rules, on a hidden class (the pure table pins their order for every hidden/not tuple)
        Assert.assertEquals(ObjIdRules.NoQualify.INSTANTIATED_SUBTYPE, ObjIdRules.qualifies(false, true, false, true, true));
        Assert.assertEquals(ObjIdRules.NoQualify.NOT_INSTANTIATED, ObjIdRules.qualifies(false, true, false, false, false));
        Assert.assertEquals(ObjIdRules.NoQualify.ABSTRACT_OR_INTERFACE, ObjIdRules.qualifies(false, true, true, true, false));
    }

    @Test
    public void guardTableOrder() {
        // the passing tuple, then each reason alone, then the precedence of every pair (the first in the order wins)
        Assert.assertNull(ObjIdRules.guard(false, false, false, 0, false, false, 0, 1, 0, 0, false, 0));
        Assert.assertNull(ObjIdRules.guard(false, false, false, 0, false, false, 0, ObjIdRules.MAX_BIRTHS, 0, 0, false, 0));
        ObjIdRules.GuardFail[] order = ObjIdRules.GuardFail.values();
        for (int i = 0; i < order.length; i++) {
            Assert.assertEquals(order[i], guardWith(i));
            for (int j = i + 1; j < order.length; j++) {
                Assert.assertEquals(order[i] + " before " + order[j], order[i], guardWith(i, j));
            }
        }
    }

    /** The guard with the given reasons (by enum ordinal) failing and everything else passing. */
    private static ObjIdRules.GuardFail guardWith(int... fails) {
        boolean[] f = new boolean[ObjIdRules.GuardFail.values().length];
        for (int i : fails) {
            f[i] = true;
        }
        int births = f[ObjIdRules.GuardFail.NO_FRAMED_BIRTH.ordinal()] ? 0 : f[ObjIdRules.GuardFail.TOO_MANY_BIRTHS.ordinal()] ? ObjIdRules.MAX_BIRTHS + 1 : 1;
        return ObjIdRules.guard(f[ObjIdRules.GuardFail.PREMISE.ordinal()], f[ObjIdRules.GuardFail.LAMBDA_CSM.ordinal()], f[ObjIdRules.GuardFail.INDEX_FAILED.ordinal()],
                        f[ObjIdRules.GuardFail.UNFRAMED_METHOD.ordinal()] ? 1 : 0,
                        f[ObjIdRules.GuardFail.UNFRAMED_BIRTH.ordinal()], f[ObjIdRules.GuardFail.UNWALKABLE_BIRTH.ordinal()], f[ObjIdRules.GuardFail.HEAP_INSTANCE.ordinal()] ? 1 : 0, births,
                        f[ObjIdRules.GuardFail.CLASS_CONSTANT.ordinal()] ? 1 : 0, f[ObjIdRules.GuardFail.CLASS_HOLDER.ordinal()] ? 1 : 0,
                        f[ObjIdRules.GuardFail.REGISTERED.ordinal()], f[ObjIdRules.GuardFail.PENDING_SLOT.ordinal()] ? 1 : 0);
    }

    @Test
    public void guardNamesTheP_FBSources() {
        // P-FB (b) and (c): a class constant, a heap holder of the Class, a registry entry each refuse the birth set
        Assert.assertEquals(ObjIdRules.GuardFail.CLASS_CONSTANT, ObjIdRules.guard(false, false, false, 0, false, false, 0, 1, 1, 0, false, 0));
        Assert.assertEquals(ObjIdRules.GuardFail.CLASS_HOLDER, ObjIdRules.guard(false, false, false, 0, false, false, 0, 1, 0, 1, false, 0));
        Assert.assertEquals(ObjIdRules.GuardFail.REGISTERED, ObjIdRules.guard(false, false, false, 0, false, false, 0, 1, 0, 0, true, 0));
        // phase 1: heap instances (singletons) are not births
        Assert.assertEquals(ObjIdRules.GuardFail.HEAP_INSTANCE, ObjIdRules.guard(false, false, false, 0, false, false, 1, 1, 0, 0, false, 0));
        // the allow-list: a pending slot kind that may hold the Class or an instance and is not listed
        Assert.assertEquals(ObjIdRules.GuardFail.PENDING_SLOT, ObjIdRules.guard(false, false, false, 0, false, false, 0, 1, 0, 0, false, 1));
        // the conditional premise: an image-level failure and a lambda calling a CSM directly, both before the per-class P-FB checks
        Assert.assertEquals(ObjIdRules.GuardFail.PREMISE, ObjIdRules.guard(true, false, false, 0, false, false, 0, 1, 0, 0, false, 0));
        Assert.assertEquals(ObjIdRules.GuardFail.LAMBDA_CSM, ObjIdRules.guard(false, true, false, 0, false, false, 0, 1, 0, 0, false, 0));
        // a framed birth without an AllocatedObject (a virtual instance committed only as another object's slot)
        Assert.assertEquals(ObjIdRules.GuardFail.UNWALKABLE_BIRTH, ObjIdRules.guard(false, false, false, 0, false, true, 0, 1, 0, 0, false, 0));
    }

    @Test
    public void callerSetIsAPureUnionWithAOneShotFan() {
        List<Set<String>> entries = List.of(new LinkedHashSet<>(List.of("a@1", "b@2")), new LinkedHashSet<>(List.of("b@2", "c@3")));
        List<String> fan = List.of("a@1", "s@9", "t@8");
        // no refusal: exactly the union of the births' entry lists (the fan's other sites are not callers)
        Assert.assertEquals(List.of("a@1", "b@2", "c@3"), ObjIdRules.callerUnion(entries, List.of(false, false), fan));
        // any birth refused: the union plus the fan; nothing delivered is removed
        List<String> fell = ObjIdRules.callerUnion(entries, List.of(false, true), fan);
        Assert.assertEquals(List.of("a@1", "b@2", "c@3", "s@9", "t@8"), fell);
        Assert.assertTrue(fell.containsAll(ObjIdRules.callerUnion(entries, List.of(false, false), fan)));
        // a birth with no entries (never called) contributes nothing
        Assert.assertEquals(List.of(), ObjIdRules.callerUnion(List.of(Set.of()), List.of(false), fan));
    }

    /**
     * The declared-type closure on real AnalysisTypes: a slot holds what its declared type, an
     * array's component, and every reference field of the type or of a subtype may reach; Object = anything (null).
     */
    @Test
    public void pendingSlotClosure() {
        World w = new World(ALL);
        java.util.Set<AnalysisType> ints = ObjIdRules.slotClosure(List.of(w.type(IntsOnly.class)));
        Assert.assertNotNull(ints);
        Assert.assertFalse("an int-only class holds no Fn", ObjIdRules.mayHold(ints, w.type(Leaf.class)));
        Assert.assertTrue("it holds itself", ObjIdRules.mayHold(ints, w.type(IntsOnly.class)));
        java.util.Set<AnalysisType> raw = ObjIdRules.slotClosure(List.of(w.type(byte[].class)));
        Assert.assertEquals("byte[] reaches only itself", java.util.Set.of(w.type(byte[].class)), raw);
        Assert.assertFalse("byte[] holds no object", ObjIdRules.mayHold(raw, w.type(Leaf.class)));
        java.util.Set<AnalysisType> fn = ObjIdRules.slotClosure(List.of(w.type(HoldsFn.class)));
        Assert.assertTrue("a Fn field may hold a Fn implementation", ObjIdRules.mayHold(fn, w.type(Leaf.class)));
        Assert.assertFalse("a Fn field cannot hold a java.util.function.Function lambda", ObjIdRules.mayHold(fn, w.type(LAMBDA.getClass())));
        Assert.assertTrue("a field of a field (IntsOnly) is reached", ObjIdRules.mayHold(fn, w.type(IntsOnly.class)));
        java.util.Set<AnalysisType> arr = ObjIdRules.slotClosure(List.of(w.type(HoldsArr.class)));
        Assert.assertTrue("an array component's fields are reached", ObjIdRules.mayHold(arr, w.type(Leaf.class)));
        Assert.assertNull("an Object field holds anything", ObjIdRules.slotClosure(List.of(w.type(HoldsObject.class))));
        Assert.assertNull("Object[] holds anything", ObjIdRules.slotClosure(List.of(w.type(Object[].class))));
        Assert.assertTrue(ObjIdRules.mayHold(null, w.type(Leaf.class)));
        java.util.List<AnalysisType> unknown = new java.util.ArrayList<>();
        unknown.add(null);
        Assert.assertNull("an unknown declared type fails closed", ObjIdRules.slotClosure(unknown));
        java.util.Set<AnalysisType> iface = ObjIdRules.slotClosure(List.of(w.type(Fn.class)));
        Assert.assertNotNull("an interface root: its implementors declare no reference field", iface);
        Assert.assertTrue(ObjIdRules.mayHold(iface, w.type(Heir.class)));
        Assert.assertFalse(ObjIdRules.mayHold(iface, w.type(IntsOnly.class)));
        Assert.assertNull("several roots: the union", ObjIdRules.slotClosure(List.of(w.type(Fn.class), w.type(HoldsObject.class))));
    }

    private static final ContainerTables.RTrackRefusal R = ContainerTables.RTrackRefusal.MISSING_IR;
    private static final ObjIdRules.Registrar RAW = (list, key, onEntry, onRefusal) -> list.register(new ContainerTables.Waiter(key, onEntry, null, onRefusal));

    /** One wiring over real tables: the delivered entries (per list) and the number of fan runs. */
    private static final class Wired {
        final List<ContainerTables.Table> tables = new java.util.ArrayList<>();
        final List<ContainerTables.EntryList<String>> lists = new java.util.ArrayList<>();
        final List<String> delivered = java.util.Collections.synchronizedList(new java.util.ArrayList<>());
        final java.util.concurrent.atomic.AtomicInteger fans = new java.util.concurrent.atomic.AtomicInteger();

        Wired(int births) {
            for (int i = 0; i < births; i++) {
                ContainerTables.Table t = new ContainerTables.Table("birth" + i, false);
                tables.add(t);
                lists.add(new ContainerTables.EntryList<>(t, "entryPaths"));
            }
        }

        void wire() {
            ObjIdRules.wireUnion(lists, l -> l.table.owner, RAW, (l, idx) -> delivered.add(l.get(idx)), (l, r) -> fans.incrementAndGet());
        }
    }

    /**
     * The production wiring ({@link ObjIdRules#wireUnion}, called by both identity hooks) on real
     * {@code Table}/{@code EntryList}s: a refusal before registration, a late refusal after deliveries, an inherited
     * refusal, and several births refusing: always exactly one fan, and every entry (before and after) is kept.
     */
    @Test
    public void oneShotFanOnRealTables() {
        // a ForwardFixpoint solve elsewhere in the suite installs its queue as the process-wide DEFER hook
        // (RTrackPoolsTest): these tables run standalone, so the inline form (the class's own default) is reinstalled
        ContainerTables.DEFER = Runnable::run;
        // (a) a refusal before registration: replayed at registration
        Wired a = new Wired(2);
        a.lists.get(0).append("a@1", "a@1");
        a.tables.get(1).refuse(R);
        a.wire();
        Assert.assertEquals(1, a.fans.get());
        Assert.assertEquals(List.of("a@1"), a.delivered);
        a.lists.get(1).append("b@2", "b@2");
        Assert.assertEquals("a later entry is still delivered (a pure union)", List.of("a@1", "b@2"), a.delivered);
        // (b) a late refusal after deliveries
        Wired b = new Wired(1);
        b.wire();
        b.lists.get(0).append("x@3", "x@3");
        Assert.assertEquals(0, b.fans.get());
        b.tables.get(0).refuse(R);
        b.tables.get(0).refuse(ContainerTables.RTrackRefusal.CLASS_ESCAPE);
        Assert.assertEquals("one fan for two refusals", 1, b.fans.get());
        Assert.assertEquals(List.of("x@3"), b.delivered);
        // (c) an inherited refusal: a holder table's refusal reaches the birth table through a waiter, later
        Wired c = new Wired(2);
        ContainerTables.Table holder = new ContainerTables.Table("holder", false);
        ContainerTables.Table birth = c.tables.get(0);
        new ContainerTables.EntryList<String>(holder, "loads").register(new ContainerTables.Waiter("inh", i -> {
        }, null, birth::refuse, birth));
        c.wire();
        c.lists.get(1).append("y@4", "y@4");
        Assert.assertEquals(0, c.fans.get());
        holder.refuse(ContainerTables.RTrackRefusal.CLASS_ESCAPE);
        Assert.assertEquals(1, c.fans.get());
        Assert.assertEquals(List.of("y@4"), c.delivered);
        // (d) every birth refuses: still exactly one fan
        Wired d = new Wired(3);
        d.wire();
        for (ContainerTables.Table t : d.tables) {
            t.refuse(R);
        }
        Assert.assertEquals(1, d.fans.get());
        // (e) no refusal: no fan, exactly the entries
        Wired e = new Wired(2);
        e.lists.get(0).append("p@5", "p@5");
        e.wire();
        e.lists.get(1).append("q@6", "q@6");
        Assert.assertEquals(0, e.fans.get());
        Assert.assertEquals(List.of("p@5", "q@6"), e.delivered);
    }

    @Test
    public void knobDefaultAndKeySpace() {
        Object site = new Object();
        ObjectIdentityRule.IdSite id = new ObjectIdentityRule.IdSite(site);
        Assert.assertSame(site, id.site);
        Assert.assertNotEquals("its own key space: never equal to the wrapped site", site, id);
        Assert.assertTrue(id.toString().startsWith("objid:"));
    }

    @Test
    public void classEscapeIsTheClassObjectOnly() {
        // the class-observing node kinds (by exact class name, as the walk's OBSERVATIONS list); others are not class escapes
        Assert.assertTrue(RecursiveTracking.classEscapeKind("GetClassNode"));
        Assert.assertTrue(RecursiveTracking.classEscapeKind("LoadHubNode"));
        Assert.assertTrue(RecursiveTracking.classEscapeKind("LoadHubOrNullNode"));
        Assert.assertFalse(RecursiveTracking.classEscapeKind("InstanceOfNode"));
        Assert.assertFalse(RecursiveTracking.classEscapeKind("IsNullNode"));
        Assert.assertFalse(RecursiveTracking.classEscapeKind("IdentityHashCodeNode"));
    }

    // ------------------------------------------------------------------
    // The conditional premise G1-G5 and the allow-list.
    // Fixtures: real bytecode read through the host JVMCI (the production reader, ObjIdRules.bytecodeUses).
    // ------------------------------------------------------------------

    /** G1 fixture: configures a walker that shows hidden frames (never run). */
    static Object g1ShowHidden() {
        return StackWalker.getInstance(StackWalker.Option.SHOW_HIDDEN_FRAMES);
    }

    /** G1 fixture: enumerates the walker options through the class constant (never run). */
    static Object g1OptionClass() {
        return java.util.EnumSet.allOf(StackWalker.Option.class);
    }

    /** G1 control: a walker with RETAIN_CLASS_REFERENCE only. */
    static Object g1RetainOnly() {
        return StackWalker.getInstance(StackWalker.Option.RETAIN_CLASS_REFERENCE);
    }

    // G1 (c): walker constructions keyed on the construction. Allowed: a provably constant option set
    // without SHOW_HIDDEN_FRAMES at the call site. Everything else fails closed. (Fixtures, never run.)
    static Object g1cNoArg() {
        return StackWalker.getInstance();
    }

    static Object g1cEnumSetOf1() {
        return StackWalker.getInstance(java.util.EnumSet.of(StackWalker.Option.RETAIN_CLASS_REFERENCE));
    }

    static Object g1cEnumSetOf2() {
        return StackWalker.getInstance(java.util.EnumSet.of(StackWalker.Option.RETAIN_CLASS_REFERENCE, StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    static Object g1cSetOf1() {
        return StackWalker.getInstance(Set.of(StackWalker.Option.RETAIN_CLASS_REFERENCE));
    }

    static Object g1cSetOfEmpty() {
        return StackWalker.getInstance(Set.of());
    }

    static Object g1cSetOfDepth() {
        return StackWalker.getInstance(Set.of(StackWalker.Option.SHOW_REFLECT_FRAMES), 8);
    }

    /** A probe route: SHOW_HIDDEN_FRAMES never named. */
    static Object g1cComplement() {
        return StackWalker.getInstance(java.util.EnumSet.complementOf(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES)));
    }

    static final Set<StackWalker.Option> G1C_OPTS = Set.of(StackWalker.Option.RETAIN_CLASS_REFERENCE);

    static Object g1cFromField() {
        return StackWalker.getInstance(G1C_OPTS);
    }

    static Object g1cFromParameter(StackWalker.Option o) {
        return StackWalker.getInstance(o);
    }

    static Object g1cSetFromParameter(Set<StackWalker.Option> o, int depth) {
        return StackWalker.getInstance(o, depth);
    }

    /** A jump target between the option and the call (the linear predecessor is a constant, the other path is not). */
    static Object g1cTernary(boolean c, StackWalker.Option o) {
        return StackWalker.getInstance(c ? o : StackWalker.Option.RETAIN_CLASS_REFERENCE);
    }

    static Object g1cValues(int i) {
        return StackWalker.getInstance(StackWalker.Option.values()[i]);
    }

    /** A constant set through a local: not recognised (conservative). */
    static Object g1cViaLocal() {
        Set<StackWalker.Option> s = java.util.EnumSet.of(StackWalker.Option.RETAIN_CLASS_REFERENCE);
        return StackWalker.getInstance(s);
    }

    static Object g1cMethodHandle(Set<StackWalker.Option> o) throws Throwable {
        java.lang.invoke.MethodHandle mh = java.lang.invoke.MethodHandles.lookup().findStatic(StackWalker.class, "getInstance",
                        java.lang.invoke.MethodType.methodType(StackWalker.class, Set.class));
        return (StackWalker) mh.invokeExact(o);
    }

    static Object g1cReflective(Set<StackWalker.Option> o) throws Exception {
        return StackWalker.class.getMethod("getInstance", Set.class).invoke(null, o);
    }

    /** A method reference to a factory: its LMF class passes the run-time argument. */
    static final java.util.function.Function<Set<StackWalker.Option>, StackWalker> G1C_REF = StackWalker::getInstance;

    /** G3 fixture: calls the SVM caller-class walk directly (never run). */
    static Object g3CallerClass() {
        return com.oracle.svm.core.jdk.StackTraceUtils.getCallerClass(null, false);
    }

    interface Loader {
        Object load(String name) throws Exception;
    }

    /** G5 fixture: a method reference to a caller-sensitive method (its LMF class invokes Class.forName directly). */
    static final Loader CSM_REF = Class::forName;

    private static ResolvedJavaMethod hostMethod(MetaAccessProvider meta, Class<?> c, String name) {
        try {
            return meta.lookupJavaMethod(c.getDeclaredMethod(name));
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
    }

    /** The bytecode uses of every declared method of a (hidden) class, OR-ed. */
    private static ObjIdRules.BytecodeUses classUses(MetaAccessProvider meta, ObjIdRules.PremiseApis apis, Class<?> c) {
        ObjIdRules.BytecodeUses all = new ObjIdRules.BytecodeUses();
        for (ResolvedJavaMethod m : meta.lookupJavaType(c).getDeclaredMethods(false)) {
            ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(m, apis);
            all.showHidden |= u.showHidden;
            all.callerClass |= u.callerClass;
            all.callerSensitive |= u.callerSensitive;
            all.unreadable |= u.unreadable;
            all.walkerBuild |= u.walkerBuild;
        }
        return all;
    }

    @Test
    public void premiseVerdictTable() {
        Assert.assertEquals("PASS", ObjIdRules.premiseVerdict(0, 0, 0, 0, 0));
        Assert.assertEquals("PASS-WITH-FLAGS", ObjIdRules.premiseVerdict(0, 0, 0, 0, 1));
        for (int g = 0; g < 4; g++) {
            int[] v = new int[4];
            v[g] = g == 2 ? 3 : 1; // GCC_NONJDK is a count
            Assert.assertTrue("G" + (g + 1), ObjIdRules.premiseFails(v[0], v[1], v[2], v[3]));
            Assert.assertEquals("G" + (g + 1), "FAIL", ObjIdRules.premiseVerdict(v[0], v[1], v[2], v[3], 0));
            Assert.assertEquals("G" + (g + 1) + " wins over G5", "FAIL", ObjIdRules.premiseVerdict(v[0], v[1], v[2], v[3], 2));
        }
        Assert.assertFalse(ObjIdRules.premiseFails(0, 0, 0, 0));
    }

    /** G1: SHOW_HIDDEN_FRAMES (or the Option class) named by a non-walker method, an enumeration, a build-time walker. */
    @Test
    public void g1StackWalkerShowHidden() {
        World w = new World(ALL);
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(w.metaAccess);
        Assert.assertTrue(ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g1ShowHidden"), apis).showHidden);
        Assert.assertTrue(ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g1OptionClass"), apis).showHidden);
        Assert.assertFalse(ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g1RetainOnly"), apis).showHidden);
        // the walker's own option tests are not configuration
        Assert.assertTrue(ObjIdRules.isWalkerFamily(StackWalker.class));
        Assert.assertTrue(ObjIdRules.isWalkerFamily(StackWalker.Option.class));
        Assert.assertFalse(ObjIdRules.isWalkerFamily(ObjectIdentityTest.class));
        Assert.assertTrue(ObjIdRules.PremiseApis.isOptionEnumeration(StackWalker.Option.class, "values"));
        Assert.assertTrue(ObjIdRules.PremiseApis.isOptionEnumeration(StackWalker.Option.class, "valueOf"));
        Assert.assertFalse(ObjIdRules.PremiseApis.isOptionEnumeration(StackWalker.Option.class, "ordinal"));
        // (b) the build-time walkers
        Assert.assertTrue(ObjIdRules.showsHiddenFrames(StackWalker.getInstance(StackWalker.Option.SHOW_HIDDEN_FRAMES)));
        Assert.assertTrue(ObjIdRules.showsHiddenFrames(StackWalker.getInstance(Set.of(StackWalker.Option.RETAIN_CLASS_REFERENCE, StackWalker.Option.SHOW_HIDDEN_FRAMES))));
        Assert.assertFalse(ObjIdRules.showsHiddenFrames(StackWalker.getInstance(StackWalker.Option.RETAIN_CLASS_REFERENCE)));
        Assert.assertFalse(ObjIdRules.showsHiddenFrames(StackWalker.getInstance()));
    }

    /** G1 (c)/(d): walker construction; each allowed constant form and each fail-closed form. */
    @Test
    public void g1WalkerConstruction() {
        World w = new World(ALL);
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(w.metaAccess);
        for (String ok : new String[]{"g1cNoArg", "g1RetainOnly", "g1cEnumSetOf1", "g1cEnumSetOf2", "g1cSetOf1", "g1cSetOfEmpty", "g1cSetOfDepth"}) {
            ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, ok), apis);
            Assert.assertFalse(ok + " is a constant option set: " + u.walkerWhy, u.walkerBuild);
            Assert.assertFalse(ok, u.showHidden);
            Assert.assertEquals(ok + " proven", 1, u.provenWalkerBcis.size());
        }
        for (String bad : new String[]{"g1cComplement", "g1cFromField", "g1cFromParameter", "g1cSetFromParameter", "g1cTernary", "g1cValues", "g1cViaLocal"}) {
            ResolvedJavaMethod m = null;
            for (ResolvedJavaMethod d : w.metaAccess.lookupJavaType(ObjectIdentityTest.class).getDeclaredMethods(false)) {
                m = d.getName().equals(bad) ? d : m;
            }
            ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(m, apis);
            Assert.assertTrue(bad + " fails closed", u.walkerBuild);
            Assert.assertFalse(bad + " names no SHOW_HIDDEN_FRAMES", u.showHidden);
        }
        // G1 (d): a method-handle / reflective call has no proven construction, so an analysis invoke of a factory
        // positioned there (a build-time intrinsified handle) fails closed; a run-time one needs a root (registration)
        for (String mhOrRefl : new String[]{"g1cMethodHandle", "g1cReflective"}) {
            ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(hostMethod2(w.metaAccess, mhOrRefl, Set.class), apis);
            Assert.assertTrue(mhOrRefl, u.provenWalkerBcis.isEmpty());
        }
        ObjIdRules.BytecodeUses ref = classUses(w.metaAccess, apis, G1C_REF.getClass());
        Assert.assertTrue("StackWalker::getInstance(Set) as a Function", ref.walkerBuild);
        // the factories: the getInstance overloads and the package-private newInstance family; not the instance methods
        int factories = 0;
        for (ResolvedJavaMethod m : apis.stackWalker.getDeclaredMethods(false)) {
            if (apis.isWalkerFactory(m)) {
                factories++;
                Assert.assertTrue(m.format("%n(%p)"), m.getName().equals("getInstance") || m.getName().equals("newInstance"));
            }
        }
        Assert.assertTrue("4 getInstance + newInstance overloads", factories >= 5);
        Assert.assertNotNull("LiveStackFrame", apis.liveStackFrame);
        // the window rule: a jump target inside the window or at the call breaks the proof
        List<int[]> win = List.of(new int[]{0, 1, 0}, new int[]{3, 2, 1});
        Assert.assertTrue(ObjIdRules.provenConstantOptions("S", win, 6, Set.of()));
        Assert.assertTrue("the window's first instruction may be a target", ObjIdRules.provenConstantOptions("S", win, 6, Set.of(0)));
        Assert.assertFalse(ObjIdRules.provenConstantOptions("S", win, 6, Set.of(3)));
        Assert.assertFalse(ObjIdRules.provenConstantOptions("S", win, 6, Set.of(6)));
        Assert.assertFalse("a set of 1 needs 1 option", ObjIdRules.provenConstantOptions("S", List.of(new int[]{0, 0, 0}, new int[]{3, 2, 1}), 6, Set.of()));
        Assert.assertFalse("an unknown factory shape", ObjIdRules.provenConstantOptions(null, win, 6, Set.of()));
    }

    private static ResolvedJavaMethod hostMethod2(MetaAccessProvider meta, String name, Class<?>... ps) {
        try {
            return meta.lookupJavaMethod(ObjectIdentityTest.class.getDeclaredMethod(name, ps));
        } catch (NoSuchMethodException e) {
            throw new AssertionError(e);
        }
    }

    /**
     * The birth index's per-commit detection on a real graph. One commit holds two virtual instances; only the first has
     * its own AllocatedObject, the second lives only as its slot value: exactly the second is an unwalkable birth. A later commit materialising the second does
     * not hide the first commit's case.
     */
    @Test
    public void unwalkableBirthPerCommit() {
        jdk.graal.compiler.options.OptionValues options = new jdk.graal.compiler.options.OptionValues(EconomicMap.create());
        jdk.graal.compiler.debug.DebugContext debug = new jdk.graal.compiler.debug.DebugContext.Builder(options).build();
        jdk.graal.compiler.nodes.StructuredGraph g = new jdk.graal.compiler.nodes.StructuredGraph.Builder(options, debug).name("unwalkableBirthPerCommit").build();
        MetaAccessProvider meta = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        ResolvedJavaType obj = meta.lookupJavaType(Object.class);
        jdk.graal.compiler.nodes.virtual.VirtualInstanceNode holder = g.addWithoutUnique(new jdk.graal.compiler.nodes.virtual.VirtualInstanceNode(obj, true));
        jdk.graal.compiler.nodes.virtual.VirtualInstanceNode elem = g.addWithoutUnique(new jdk.graal.compiler.nodes.virtual.VirtualInstanceNode(obj, true));
        jdk.graal.compiler.nodes.virtual.CommitAllocationNode c1 = g.add(new jdk.graal.compiler.nodes.virtual.CommitAllocationNode());
        c1.getVirtualObjects().add(holder);
        c1.getVirtualObjects().add(elem);
        jdk.graal.compiler.nodes.virtual.AllocatedObjectNode a1 = g.addWithoutUnique(new jdk.graal.compiler.nodes.virtual.AllocatedObjectNode(holder));
        a1.setCommit(c1);
        Assert.assertEquals(List.of(elem), RecursiveTracking.unwalkableInstances(c1));
        jdk.graal.compiler.nodes.virtual.CommitAllocationNode c2 = g.add(new jdk.graal.compiler.nodes.virtual.CommitAllocationNode());
        c2.getVirtualObjects().add(elem);
        jdk.graal.compiler.nodes.virtual.AllocatedObjectNode a2 = g.addWithoutUnique(new jdk.graal.compiler.nodes.virtual.AllocatedObjectNode(elem));
        a2.setCommit(c2);
        Assert.assertEquals("materialised in its own commit", List.of(), RecursiveTracking.unwalkableInstances(c2));
        Assert.assertEquals("the first commit still lacks it", List.of(elem), RecursiveTracking.unwalkableInstances(c1));
    }

    /** G2: the class-context producers. */
    @Test
    public void g2ClassContext() {
        Assert.assertTrue(ObjIdRules.PremiseApis.isClassContext(SecurityManager.class, "getClassContext"));
        Assert.assertTrue(ObjIdRules.PremiseApis.isClassContext(com.oracle.svm.core.jdk.StackTraceUtils.class, "getClassContext"));
        Assert.assertFalse(ObjIdRules.PremiseApis.isClassContext(SecurityManager.class, "checkPermission"));
        Assert.assertFalse(ObjIdRules.PremiseApis.isClassContext(ObjectIdentityTest.class, "getClassContext"));
    }

    /** G3: a direct getCallerClass invoke, and what counts as application code. */
    @Test
    public void g3CallerClassFromApplicationCode() {
        World w = new World(ALL);
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(w.metaAccess);
        ObjIdRules.BytecodeUses u = ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g3CallerClass"), apis);
        Assert.assertTrue(u.callerClass);
        Assert.assertFalse(u.unreadable);
        Assert.assertFalse(ObjIdRules.bytecodeUses(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g1RetainOnly"), apis).callerClass);
        ClassLoader builder = ObjIdRules.class.getClassLoader();
        Assert.assertTrue("the JDK", ObjIdRules.isRuntimeClass(String.class, builder));
        Assert.assertTrue("the builder's own classes", ObjIdRules.isRuntimeClass(ObjIdRules.class, builder));
        ClassLoader other = new ClassLoader(null) {
        };
        Assert.assertFalse("application code (another loader)", ObjIdRules.isRuntimeClass(ObjectIdentityTest.class, other));
    }

    /** G4: an instantiated implementation of the interface. */
    @Test
    public void g4InstantiatedImplementor() {
        World w = new World(ALL);
        Assert.assertNotNull(ObjIdRules.firstInstantiated(w.type(Fn.class)));
        Assert.assertNull("the only implementor is never instantiated", ObjIdRules.firstInstantiated(w.type(Idle.class)));
    }

    /** G5: a lambda class whose own bytecode invokes a CallerSensitive method; an ordinary capturing lambda does not. */
    @Test
    public void g5LambdaCallsCallerSensitive() {
        World w = new World(ALL);
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(w.metaAccess);
        Assert.assertTrue(CSM_REF.getClass().isHidden());
        ObjIdRules.BytecodeUses csm = classUses(w.metaAccess, apis, CSM_REF.getClass());
        Assert.assertTrue("Class::forName", csm.callerSensitive);
        Assert.assertFalse(csm.unreadable);
        ObjIdRules.BytecodeUses plain = classUses(w.metaAccess, apis, LAMBDA.getClass());
        Assert.assertFalse("k -> loc + k", plain.callerSensitive);
        Assert.assertFalse(plain.unreadable);
        Assert.assertFalse(ObjIdRules.isCallerSensitive(hostMethod(w.metaAccess, ObjectIdentityTest.class, "g1RetainOnly")));
    }

    /**
     * The allow-list premise: every listed kind names a real field of a real class (the list cannot rot silently), and a
     * kind that may hold a Class or a lambda instance blocks unless listed (a new kind fails closed, printed as
     * {@code pendingNotAllowed=}).
     */
    @Test
    public void pendingAllowListIsRealAndFailsClosed() throws Exception {
        Assert.assertEquals("the 28 audited kinds + the 9 FieldStaticReadOnly.base kinds + jfrEventConfiguration", 38, ObjIdRules.PENDING_ALLOW.size());
        int a = 0;
        int b = 0;
        for (java.util.Map.Entry<String, String> e : ObjIdRules.PENDING_ALLOW.entrySet()) {
            String key = e.getKey();
            boolean isStatic = key.startsWith("static ");
            Assert.assertTrue(key, isStatic || key.startsWith("field "));
            String hn = key.substring(key.indexOf(' ') + 1);
            int dot = hn.lastIndexOf('.');
            Class<?> holder = Class.forName(hn.substring(0, dot), false, ObjIdRules.class.getClassLoader());
            java.lang.reflect.Field f = com.oracle.svm.util.ReflectionUtil.lookupField(true, holder, hn.substring(dot + 1)); // also filtered JDK fields
            if (f == null) {
                // a field of a @Substitute class (the universe shows it under the JDK holder): ClassValue.values
                Class<?> sub = Class.forName("com.oracle.svm.core.jdk.Target_" + holder.getName().replace('.', '_'), false, ObjIdRules.class.getClassLoader());
                com.oracle.svm.core.annotate.TargetClass tc = sub.getAnnotation(com.oracle.svm.core.annotate.TargetClass.class);
                Assert.assertEquals(key, holder, tc.value());
                f = sub.getDeclaredField(hn.substring(dot + 1));
            }
            Assert.assertEquals(key, isStatic, java.lang.reflect.Modifier.isStatic(f.getModifiers()));
            Assert.assertFalse(key + " is a reference slot", f.getType().isPrimitive());
            a += e.getValue().startsWith("A:") ? 1 : 0;
            b += e.getValue().startsWith("B:") ? 1 : 0;
        }
        Assert.assertEquals("23 contents-indexed kinds", 23, a);
        Assert.assertEquals("15 raw-memory kinds", 15, b);
        String listed = "field com.oracle.svm.core.code.ImageCodeInfo.classes";
        Assert.assertFalse("a listed kind never blocks", ObjIdRules.pendingSlotBlocks(true, true, listed));
        Assert.assertTrue("an unlisted kind that may hold the Class blocks", ObjIdRules.pendingSlotBlocks(true, false, "field a.New.slot"));
        Assert.assertTrue("an unlisted kind that may hold an instance blocks", ObjIdRules.pendingSlotBlocks(false, true, "static a.New.slot"));
        Assert.assertTrue("array / representation kinds are never listed", ObjIdRules.pendingSlotBlocks(true, true, "array java.lang.Object[]"));
        Assert.assertFalse("an unlisted kind that holds neither does not block", ObjIdRules.pendingSlotBlocks(false, false, "field a.New.bytes"));
    }

    /**
     * The hub companion's JFR event-configuration slot is a listed contents-indexed kind (so a
     * {@code --enable-monitoring=jfr} image does not refuse rule U image-wide): its only writers pass a JDK
     * {@code EventConfiguration} (a final record, never a Class, hub or companion), and only the exact key is listed.
     */
    @Test
    public void jfrEventConfigurationIsAllowedExactly() throws Exception {
        String k = ObjIdRules.JFR_EVENT_CONFIGURATION;
        Assert.assertEquals("field com.oracle.svm.core.hub.DynamicHubCompanion.jfrEventConfiguration", k);
        Assert.assertTrue(ObjIdRules.pendingAllow(k).startsWith("A:"));
        Assert.assertTrue(ObjIdRules.PENDING_NAMED.get(k).startsWith("HOLDS: contents indexed"));
        Assert.assertFalse(ObjIdRules.pendingSlotBlocks(true, true, k));
        Assert.assertTrue("another companion slot stays closed", ObjIdRules.pendingSlotBlocks(true, true, "field com.oracle.svm.core.hub.DynamicHubCompanion.classLoader"));
        Assert.assertTrue("no prefix match", ObjIdRules.pendingSlotBlocks(true, true, k + "X"));
        Class<?> ec = Class.forName("jdk.jfr.internal.event.EventConfiguration", false, ObjIdRules.class.getClassLoader());
        Assert.assertTrue("the value class is a final record", ec.isRecord() && java.lang.reflect.Modifier.isFinal(ec.getModifiers()));
        com.oracle.svm.core.annotate.TargetClass tc = com.oracle.svm.core.jfr.Target_jdk_jfr_internal_event_EventConfiguration.class.getAnnotation(com.oracle.svm.core.annotate.TargetClass.class);
        Assert.assertEquals("the run-time writer's parameter type is that record", ec.getName(), tc.className());
        java.lang.reflect.Method set = com.oracle.svm.core.jfr.Target_jdk_jfr_internal_JVM.class.getDeclaredMethod("setConfiguration", Class.class,
                        com.oracle.svm.core.jfr.Target_jdk_jfr_internal_event_EventConfiguration.class);
        Assert.assertNotNull(set);
    }

    /**
     * The writer set of {@code DynamicHubCompanion.jfrEventConfiguration} the PENDING_ALLOW row relies on, by a class-file
     * scan of the code sources of {@code DynamicHub} and {@code JfrEventFeature}: the only {@code putfield} is in
     * {@code DynamicHub.setJrfEventConfiguration}, called only by {@code JfrEventFeature.beforeCompilation} (build time)
     * and {@code SubstrateJVM.setConfiguration} (run time). A new writer or caller fails until re-audited. Reflective /
     * Unsafe writes are outside the scan (the accepted raw-memory residual).
     */
    @Test
    public void jfrEventConfigurationWriters() throws Exception {
        String companion = "com/oracle/svm/core/hub/DynamicHubCompanion";
        String hub = "com/oracle/svm/core/hub/DynamicHub";
        Set<String> writers = new java.util.TreeSet<>();
        Set<String> callers = new java.util.TreeSet<>();
        Set<java.net.URI> sources = new LinkedHashSet<>();
        sources.add(com.oracle.svm.core.hub.DynamicHub.class.getProtectionDomain().getCodeSource().getLocation().toURI());
        sources.add(com.oracle.svm.hosted.jfr.JfrEventFeature.class.getProtectionDomain().getCodeSource().getLocation().toURI());
        int classes = 0;
        for (java.net.URI src : sources) {
            java.util.Map<String, byte[]> files = new java.util.LinkedHashMap<>();
            java.io.File loc = new java.io.File(src);
            if (loc.isDirectory()) {
                try (java.util.stream.Stream<java.nio.file.Path> s = java.nio.file.Files.walk(loc.toPath())) {
                    for (java.nio.file.Path p : (Iterable<java.nio.file.Path>) s.filter(x -> x.toString().endsWith(".class"))::iterator) {
                        files.put(p.toString(), java.nio.file.Files.readAllBytes(p));
                    }
                }
            } else {
                try (java.util.jar.JarFile jf = new java.util.jar.JarFile(loc)) {
                    for (java.util.jar.JarEntry e : java.util.Collections.list(jf.entries())) {
                        if (e.getName().endsWith(".class")) {
                            try (java.io.InputStream in = jf.getInputStream(e)) {
                                files.put(e.getName(), in.readAllBytes());
                            }
                        }
                    }
                }
            }
            for (byte[] bytes : files.values()) {
                classes++;
                String text = new String(bytes, java.nio.charset.StandardCharsets.ISO_8859_1);
                if (!text.contains("jfrEventConfiguration") && !text.contains("setJrfEventConfiguration")) {
                    continue; // a field or method ref names the member in the constant pool
                }
                java.lang.classfile.ClassModel cm = java.lang.classfile.ClassFile.of().parse(bytes);
                String owner = cm.thisClass().asInternalName();
                for (java.lang.classfile.MethodModel mm : cm.methods()) {
                    String at = owner + "#" + mm.methodName().stringValue();
                    for (java.lang.classfile.CodeElement ce : mm.code().map(c -> c.elementList()).orElse(List.of())) {
                        if (ce instanceof java.lang.classfile.instruction.FieldInstruction fi && fi.opcode() == java.lang.classfile.Opcode.PUTFIELD &&
                                        fi.owner().asInternalName().equals(companion) && fi.name().stringValue().equals("jfrEventConfiguration")) {
                            writers.add(at);
                        } else if (ce instanceof java.lang.classfile.instruction.InvokeInstruction ii && ii.owner().asInternalName().equals(hub) &&
                                        ii.name().stringValue().equals("setJrfEventConfiguration")) {
                            callers.add(at);
                        }
                    }
                }
            }
        }
        Assert.assertTrue("the code sources were enumerated: " + classes + " " + sources, classes > 1000);
        Assert.assertEquals("the only writer of the slot", Set.of(hub + "#setJrfEventConfiguration"), writers);
        Assert.assertEquals("the callers of the writer (re-audit the PENDING_ALLOW row on a change)",
                        Set.of("com/oracle/svm/hosted/jfr/JfrEventFeature#beforeCompilation", "com/oracle/svm/core/jfr/SubstrateJVM#setConfiguration"), callers);
    }

    // ------------------------------------------------------------------
    // The G1 derived-factory rule. Fixtures: real bytecode (never run), read through the host JVMCI by
    // ObjIdRules.forwardFacts; the callers come from a synthetic world (in the image: the analysis invoke flows).
    // ------------------------------------------------------------------

    interface G1Fac {
        StackWalker make(Set<StackWalker.Option> o);

        StackWalker make2(Set<StackWalker.Option> o, Object scope, Object inner);
    }

    static final class G1FacImpl implements G1Fac {
        @Override
        public StackWalker make(Set<StackWalker.Option> o) {
            return StackWalker.getInstance(o);
        }

        @Override
        public StackWalker make2(Set<StackWalker.Option> o, Object scope, Object inner) {
            return StackWalker.getInstance(o);
        }
    }

    static final G1Fac FAC = new G1FacImpl();
    static Set<StackWalker.Option> lastSet;

    static Object scope() {
        return null;
    }

    static Object inner() {
        return null;
    }

    static int helper(Set<StackWalker.Option> o) {
        return o.size();
    }

    static StackWalker fwdChain1(Set<StackWalker.Option> o) {
        return fwdChain2(o, 3);
    }

    static StackWalker fwdChain2(Set<StackWalker.Option> o, int d) {
        return StackWalker.getInstance(o, d + 1);
    }

    /** The Continuation mirror: the set is not the last argument, a call follows it, an interface hop. */
    static StackWalker fwdMirror(Set<StackWalker.Option> o) {
        return FAC.make2(o, scope(), inner());
    }

    static StackWalker fwdMirrorTop(Set<StackWalker.Option> o) {
        return fwdMirror(o);
    }

    static StackWalker fwdMirrorOrigin() {
        return fwdMirrorTop(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    static StackWalker fwdOriginOf() {
        return fwdChain1(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    /** The receiver lies below the set. */
    static StackWalker fwdOriginIface(G1Fac f) {
        return f.make(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    static StackWalker fwdOriginSetOf2() {
        return fwdChain1(Set.of(StackWalker.Option.RETAIN_CLASS_REFERENCE, StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    static StackWalker fwdComplementOrigin() {
        return fwdChain1(java.util.EnumSet.complementOf(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES)));
    }

    static StackWalker fwdViaLocal() {
        Set<StackWalker.Option> s = java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES);
        return fwdChain1(s);
    }

    static StackWalker fwdTernaryParam(boolean c, Set<StackWalker.Option> o) {
        return fwdChain1(c ? o : Set.of());
    }

    static StackWalker fwdStoreParam(Set<StackWalker.Option> o) {
        o = java.util.EnumSet.copyOf(o);
        return StackWalker.getInstance(o);
    }

    static StackWalker fwdMutateInForwarder(Set<StackWalker.Option> o) {
        o.addAll(java.util.EnumSet.complementOf(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES)));
        return StackWalker.getInstance(o);
    }

    static StackWalker fwdHelperUse(Set<StackWalker.Option> o) {
        helper(o);
        return StackWalker.getInstance(o);
    }

    static StackWalker fwdDupParam(Set<StackWalker.Option> o) {
        return StackWalker.getInstance(lastSet = o);
    }

    static Set<StackWalker.Option> fwdReturnParam(Set<StackWalker.Option> o) {
        StackWalker.getInstance(o);
        return o;
    }

    /** A recursive forwarder: the downward closure meets the cycle. */
    static StackWalker fwdRec(Set<StackWalker.Option> o, int n) {
        return n > 0 ? fwdRec(o, n - 1) : StackWalker.getInstance(o);
    }

    // a forwarding chain longer than FWD_DEPTH
    static StackWalker fwdD1(Set<StackWalker.Option> o) {
        return fwdD2(o);
    }

    static StackWalker fwdD2(Set<StackWalker.Option> o) {
        return fwdD3(o);
    }

    static StackWalker fwdD3(Set<StackWalker.Option> o) {
        return fwdD4(o);
    }

    static StackWalker fwdD4(Set<StackWalker.Option> o) {
        return fwdD5(o);
    }

    static StackWalker fwdD5(Set<StackWalker.Option> o) {
        return fwdD6(o);
    }

    static StackWalker fwdD6(Set<StackWalker.Option> o) {
        return fwdD7(o);
    }

    static StackWalker fwdD7(Set<StackWalker.Option> o) {
        return fwdD8(o);
    }

    static StackWalker fwdD8(Set<StackWalker.Option> o) {
        return fwdChain1(o);
    }

    static StackWalker fwdDOrigin1() {
        return fwdD1(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    static StackWalker fwdDOrigin7() {
        return fwdD7(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    /** A covariant bridge {@code Object mk(Set)} and its impure target {@code StackWalker mk(Set)} print alike. */
    interface G1Mk<T> {
        T mk(Set<StackWalker.Option> o);
    }

    static final class G1MkBad implements G1Mk<StackWalker> {
        @Override
        public StackWalker mk(Set<StackWalker.Option> o) {
            o.addAll(java.util.EnumSet.complementOf(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES)));
            return StackWalker.getInstance(o);
        }
    }

    /** Overloads whose parameter types share a simple name ({@code Signature}): one pure, one impure. */
    static StackWalker fwdSame(java.security.Signature o) {
        return null;
    }

    static StackWalker fwdSame(jdk.vm.ci.meta.Signature o) {
        lastObj = o;
        return null;
    }

    /** A generic bridge {@code Object mk(Object)} forwarding through a checkcast to {@code StackWalker mk(Set)}. */
    interface G1MkC<T, S> {
        T mk(S o);
    }

    static final class G1MkCast implements G1MkC<StackWalker, Set<StackWalker.Option>> {
        @Override
        public StackWalker mk(Set<StackWalker.Option> o) {
            return StackWalker.getInstance(o);
        }
    }

    static Object fwdMkOrigin(G1MkC<StackWalker, Set<StackWalker.Option>> k) {
        return k.mk(java.util.EnumSet.of(StackWalker.Option.SHOW_REFLECT_FRAMES));
    }

    @SuppressWarnings("unchecked")
    static StackWalker fwdCast(Object o) {
        return StackWalker.getInstance((Set<StackWalker.Option>) o);
    }

    static Object lastObj;

    /** An invokedynamic capture of the set: an escape. */
    static StackWalker fwdIndy(Set<StackWalker.Option> o) {
        java.util.function.Supplier<Object> s = () -> o;
        lastObj = s;
        return StackWalker.getInstance(o);
    }

    static StackWalker fwdHandler(Set<StackWalker.Option> o) {
        try {
            return StackWalker.getInstance(o);
        } catch (IllegalArgumentException e) {
            return fwdChain1(o);
        }
    }

    static void stash(Set<StackWalker.Option> o) {
        lastSet = o;
    }

    /** {@code stash} inlined before the analysis leaves only its inner flows at the call position. */
    static StackWalker fwdInlinedHelper(Set<StackWalker.Option> o) {
        stash(o);
        return StackWalker.getInstance(o);
    }

    /** The declared method of that name that is (or is not) a bridge. */
    private static ResolvedJavaMethod bridgeOrTarget(MetaAccessProvider meta, Class<?> c, String name, boolean bridge) {
        ResolvedJavaMethod m = null;
        for (ResolvedJavaMethod d : meta.lookupJavaType(c).getDeclaredMethods(false)) {
            if (d.getName().equals(name) && d.isBridge() == bridge) {
                Assert.assertNull("unique " + name, m);
                m = d;
            }
        }
        Assert.assertNotNull(name, m);
        return m;
    }

    private static MetaAccessProvider hostMeta() {
        return HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    }

    /** The single declared method of that name (fixtures have unique names). */
    private static ResolvedJavaMethod named(MetaAccessProvider meta, Class<?> c, String name) {
        ResolvedJavaMethod m = null;
        for (ResolvedJavaMethod d : meta.lookupJavaType(c).getDeclaredMethods(false)) {
            if (d.getName().equals(name)) {
                Assert.assertNull("unique " + name, m);
                m = d;
            }
        }
        Assert.assertNotNull(name, m);
        return m;
    }

    /** The bci of the (single) invoke in {@code f} whose target has that name. */
    private static int bciOf(ObjIdRules.FwdFacts f, String target) {
        int bci = -1;
        for (java.util.Map.Entry<Integer, ResolvedJavaMethod> e : f.target.entrySet()) {
            if (e.getValue().getName().equals(target)) {
                Assert.assertEquals("one invoke of " + target, -1, bci);
                bci = e.getKey();
            }
        }
        Assert.assertTrue(target, bci >= 0);
        return bci;
    }

    /** A synthetic world: real bytecode facts, configured callers / roots / virtual callees. */
    private static final class FwdTestWorld implements ObjIdRules.FwdWorld {
        final ObjIdRules.PremiseApis apis;
        final java.util.Map<ResolvedJavaMethod, List<ObjIdRules.FwdSite>> callers = new java.util.HashMap<>();
        final Set<ResolvedJavaMethod> roots = new java.util.HashSet<>();
        final java.util.Map<ObjIdRules.FwdSite, List<ResolvedJavaMethod>> callees = new java.util.HashMap<>();
        /** When set: the callees come from this flow index (the image's wiring) instead of {@link #callees}. */
        ObjIdRules.FwdIndex index;

        FwdTestWorld(ObjIdRules.PremiseApis apis) {
            this.apis = apis;
        }

        @Override
        public ObjIdRules.FwdFacts facts(ResolvedJavaMethod m) {
            return ObjIdRules.forwardFacts(m, apis);
        }

        @Override
        public java.util.Collection<ObjIdRules.FwdSite> callers(ResolvedJavaMethod m) {
            return callers.getOrDefault(m, List.of());
        }

        @Override
        public boolean root(ResolvedJavaMethod m) {
            if (roots.contains(m)) {
                return true;
            }
            for (ResolvedJavaMethod o : ObjIdRules.overridden(m)) {
                if (roots.contains(o)) {
                    return true;
                }
            }
            return false;
        }

        @Override
        public java.util.Collection<ResolvedJavaMethod> calleesAt(ResolvedJavaMethod m, int bci, ResolvedJavaMethod t) {
            return index != null ? index.calleesAt(m, bci, t) : callees.get(new ObjIdRules.FwdSite(m, bci));
        }

        @Override
        public int factorySetParam(ResolvedJavaMethod t) {
            return apis.setParamIndex(t);
        }

        /** caller -> callee: the caller's (single) invoke of the callee. */
        void call(ResolvedJavaMethod caller, ResolvedJavaMethod callee) {
            int bci = bciOf(facts(caller), callee.getName());
            callers.computeIfAbsent(callee, k -> new java.util.ArrayList<>()).add(new ObjIdRules.FwdSite(caller, bci));
        }
    }

    /** The derived-factory rule: origins and purity of the per-method simulation. */
    @Test
    public void g1FwdFacts() {
        MetaAccessProvider meta = hostMeta();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(meta);
        java.util.function.Function<String, ObjIdRules.FwdFacts> facts = n -> ObjIdRules.forwardFacts(named(meta, ObjectIdentityTest.class, n), apis);
        int reflect = 1 << StackWalker.Option.SHOW_REFLECT_FRAMES.ordinal();
        int retain = 1 << StackWalker.Option.RETAIN_CLASS_REFERENCE.ordinal();

        ObjIdRules.FwdFacts c2 = facts.apply("fwdChain2");
        Assert.assertTrue("a forwarder to getInstance(Set,int)", c2.localPure(0));
        Assert.assertFalse("an int parameter is not tracked", c2.reference[1]);
        Assert.assertEquals(1, c2.uses.get(0).size());
        Assert.assertEquals(bciOf(c2, "getInstance"), c2.uses.get(0).get(0)[0]);
        Assert.assertEquals(0, c2.uses.get(0).get(0)[1]);
        ObjIdRules.FwdFacts c1 = facts.apply("fwdChain1");
        Assert.assertTrue(c1.localPure(0));
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.PARAM, 0), c1.arg(bciOf(c1, "fwdChain2"), 0));
        ObjIdRules.FwdFacts mirror = facts.apply("fwdMirror");
        Assert.assertTrue("set not last, calls after it, receiver below it", mirror.localPure(0));
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.PARAM, 0), mirror.arg(bciOf(mirror, "make2"), 0));
        Assert.assertFalse("an interface call is not bound", mirror.bound.contains(bciOf(mirror, "make2")));

        ObjIdRules.FwdFacts of = facts.apply("fwdOriginOf");
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.CONST, reflect), of.arg(bciOf(of, "fwdChain1"), 0));
        ObjIdRules.FwdFacts iface = facts.apply("fwdOriginIface");
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.CONST, reflect), iface.arg(bciOf(iface, "make"), 0));
        ObjIdRules.FwdFacts of2 = facts.apply("fwdOriginSetOf2");
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.CONST, reflect | retain), of2.arg(bciOf(of2, "fwdChain1"), 0));

        for (String other : new String[]{"fwdComplementOrigin", "fwdViaLocal", "fwdTernaryParam"}) {
            ObjIdRules.FwdFacts f = facts.apply(other);
            Assert.assertEquals(other, ObjIdRules.FwdVal.OTHER, f.arg(bciOf(f, "fwdChain1"), 0).kind());
        }
        Assert.assertFalse("a parameter live across a block boundary escapes", facts.apply("fwdTernaryParam").localPure(1));
        for (String impure : new String[]{"fwdStoreParam", "fwdMutateInForwarder", "fwdDupParam", "fwdReturnParam"}) {
            Assert.assertFalse(impure, facts.apply(impure).localPure(0));
        }
        Assert.assertTrue("helper(o) is an invoke use: decided by the downward closure", facts.apply("fwdHelperUse").localPure(0));
        Assert.assertEquals("the arithmetic after the set is modelled", ObjIdRules.FwdVal.PARAM, facts.apply("fwdRec").arg(bciOf(facts.apply("fwdRec"), "getInstance"), 0).kind());
        // abstract / native: no facts
        Assert.assertTrue(ObjIdRules.forwardFacts(named(meta, G1Fac.class, "make"), apis).unreadable);
        // the factories' option-set parameter and the constructors
        int ctors = 0;
        for (ResolvedJavaMethod c : apis.stackWalker.getDeclaredConstructors(false)) {
            Assert.assertTrue(apis.isWalkerConstructor(c));
            Assert.assertEquals("a constructor is not a factory", -2, apis.setParamIndex(c));
            ctors++;
        }
        Assert.assertTrue("the private StackWalker constructors", ctors >= 3);
        for (ResolvedJavaMethod m : apis.stackWalker.getDeclaredMethods(false)) {
            Assert.assertFalse(apis.isWalkerConstructor(m));
            if (apis.isWalkerFactory(m)) {
                String p0 = m.getSignature().getParameterCount(false) == 0 ? "" : m.getSignature().getParameterType(0, null).getName();
                Assert.assertEquals(m.format("%n(%p)"), p0.equals("Ljava/util/Set;") ? 0 : -1, apis.setParamIndex(m));
            } else {
                Assert.assertEquals(-2, apis.setParamIndex(m));
            }
        }
        Assert.assertFalse(apis.isWalkerConstructor(named(meta, ObjectIdentityTest.class, "fwdChain1")));
    }

    /** The derived-factory rule: the derivation over a synthetic world. */
    @Test
    public void g1FwdDerivation() {
        MetaAccessProvider meta = hostMeta();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(meta);
        java.util.function.Function<String, ResolvedJavaMethod> m = n -> named(meta, ObjectIdentityTest.class, n);
        ResolvedJavaMethod chain2 = m.apply("fwdChain2");
        ResolvedJavaMethod chain1 = m.apply("fwdChain1");
        int pend2 = bciOf(ObjIdRules.forwardFacts(chain2, apis), "getInstance");

        // the interface hop, depth 3: G1FacImpl.make2 <= fwdMirror (invokeinterface G1Fac.make2) <= fwdMirrorTop <= fwdMirrorOrigin
        FwdTestWorld w = new FwdTestWorld(apis);
        ResolvedJavaMethod impl = named(meta, G1FacImpl.class, "make2");
        w.call(m.apply("fwdMirror"), impl); // the declared target is G1Fac.make2, implemented by impl
        w.callees.put(new ObjIdRules.FwdSite(m.apply("fwdMirror"), bciOf(w.facts(m.apply("fwdMirror")), "make2")), List.of(impl));
        w.call(m.apply("fwdMirrorTop"), m.apply("fwdMirror"));
        w.call(m.apply("fwdMirrorOrigin"), m.apply("fwdMirrorTop"));
        ObjIdRules.FwdVerdict v = new ObjIdRules.FwdProver(w).provePending(impl, bciOf(w.facts(impl), "getInstance"));
        Assert.assertNull(v.chain(), v.reason());
        Assert.assertEquals(3, v.depth());
        Assert.assertTrue(v.chain(), v.chain().endsWith("CONST{SHOW_REFLECT_FRAMES}"));
        // the same with the interface method a virtual root (it may be called from outside the flow graph)
        w.roots.add(named(meta, G1Fac.class, "make2"));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(impl, bciOf(w.facts(impl), "getInstance")).reason().startsWith("fwd:root@"));
        w.roots.clear();
        // no virtual callees known at the interface hop: fwdMirror is not provably pure (fails closed, its own reason)
        w.callees.clear();
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(impl, bciOf(w.facts(impl), "getInstance")).reason().startsWith("fwd:no-callees@"));

        // the static chain: one good caller proven at depth 2; a second, non-constant caller fails it
        w = new FwdTestWorld(apis);
        w.call(chain1, chain2);
        w.call(m.apply("fwdOriginOf"), chain1);
        v = new ObjIdRules.FwdProver(w).provePending(chain2, pend2);
        Assert.assertTrue(v.reason(), v.ok());
        Assert.assertEquals(2, v.depth());
        w.call(m.apply("fwdOriginSetOf2"), chain1);
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).ok());
        w.call(m.apply("fwdComplementOrigin"), chain1);
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:non-constant@"));
        // a root forwarder
        w = new FwdTestWorld(apis);
        w.call(chain1, chain2);
        w.call(m.apply("fwdOriginOf"), chain1);
        w.roots.add(chain1);
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:root@"));
        // invoked with zero known callers
        w = new FwdTestWorld(apis);
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:unknown-caller@"));
        // a caller position whose bytecode does not invoke the method (an inlined call / an intrinsified handle) or no position
        w = new FwdTestWorld(apis);
        w.callers.put(chain2, List.of(new ObjIdRules.FwdSite(m.apply("fwdOriginOf"), bciOf(w.facts(m.apply("fwdOriginOf")), "fwdChain1"))));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:position@"));
        w.callers.put(chain2, List.of(new ObjIdRules.FwdSite(null, 3)));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:position@"));
        // fan: 17 caller sites
        w = new FwdTestWorld(apis);
        List<ObjIdRules.FwdSite> fan = new java.util.ArrayList<>();
        for (int i = 0; i <= ObjIdRules.FWD_FANCAP; i++) {
            fan.add(new ObjIdRules.FwdSite(chain1, 1000 + i));
        }
        w.callers.put(chain2, fan);
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(chain2, pend2).reason().startsWith("fwd:fan@"));
        // depth: fwdD7 -> fwdD8 -> fwdChain1 -> fwdChain2 proven at 4; from fwdD1 the proof exceeds FWD_DEPTH
        w = new FwdTestWorld(apis);
        w.call(chain1, chain2);
        w.call(m.apply("fwdD8"), chain1);
        for (int i = 1; i <= 7; i++) {
            w.call(m.apply("fwdD" + i), m.apply("fwdD" + (i + 1)));
        }
        w.call(m.apply("fwdDOrigin7"), m.apply("fwdD7"));
        Assert.assertFalse("two callers of fwdD7: fwdD6 is still open", new ObjIdRules.FwdProver(w).provePending(chain2, pend2).ok());
        w.callers.put(m.apply("fwdD7"), new java.util.ArrayList<>(List.of(new ObjIdRules.FwdSite(m.apply("fwdDOrigin7"), bciOf(w.facts(m.apply("fwdDOrigin7")), "fwdD7")))));
        v = new ObjIdRules.FwdProver(w).provePending(chain2, pend2);
        Assert.assertTrue(v.reason(), v.ok());
        Assert.assertEquals(4, v.depth());
        w.call(m.apply("fwdD6"), m.apply("fwdD7"));
        w.call(m.apply("fwdDOrigin1"), m.apply("fwdD1"));
        v = new ObjIdRules.FwdProver(w).provePending(chain2, pend2);
        Assert.assertEquals("fwd:depth@" + ObjIdRules.FwdProver.name(m.apply("fwdD2")) + "@" + bciOf(w.facts(m.apply("fwdD2")), "fwdD3"), v.reason());
        // cycles: a recursive forwarder is impure (the downward closure meets the cycle); a method already on the path
        w = new FwdTestWorld(apis);
        ResolvedJavaMethod rec = m.apply("fwdRec");
        w.callers.put(rec, List.of(new ObjIdRules.FwdSite(rec, bciOf(w.facts(rec), "fwdRec"))));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).provePending(rec, bciOf(w.facts(rec), "getInstance")).reason().startsWith("fwd:impure-param@"));
        w = new FwdTestWorld(apis);
        w.call(chain1, chain2);
        Set<ResolvedJavaMethod> path = new LinkedHashSet<>(List.of(chain2));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).proveArg(chain2, pend2, 0, 0, path).reason().startsWith("fwd:cycle@"));
        // downward purity: helper(o) is not a forwarder; a forwarder whose callee is impure is impure
        w = new FwdTestWorld(apis);
        ResolvedJavaMethod hu = m.apply("fwdHelperUse");
        Assert.assertFalse(new ObjIdRules.FwdProver(w).isPure(hu, 0, 0, new java.util.HashSet<>()));
        Assert.assertTrue(new ObjIdRules.FwdProver(w).isPure(chain1, 0, 0, new java.util.HashSet<>()));
        Assert.assertTrue("a non-set argument of a factory is impure", !new ObjIdRules.FwdProver(w).isPure(m.apply("g1cFromParameter"), 0, 0, new java.util.HashSet<>()));
    }

    /** Identity memo keys, per-declared-target callees, bytecode corner cases, the flow index. */
    @Test
    public void g1FwdReview6() {
        MetaAccessProvider meta = hostMeta();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(meta);
        java.util.function.Function<String, ResolvedJavaMethod> m = n -> named(meta, ObjectIdentityTest.class, n);
        java.util.function.Function<String, ObjIdRules.FwdFacts> facts = n -> ObjIdRules.forwardFacts(m.apply(n), apis);

        // false PROVEN direction: the pure overload's memo must not answer for the impure one (both print fwdSame(Signature))
        ResolvedJavaMethod sameU = null;
        ResolvedJavaMethod sameS = null;
        for (ResolvedJavaMethod d : meta.lookupJavaType(ObjectIdentityTest.class).getDeclaredMethods(false)) {
            if (d.getName().equals("fwdSame")) {
                boolean jvmci = d.getSignature().getParameterType(0, null).getName().equals("Ljdk/vm/ci/meta/Signature;");
                sameS = jvmci ? d : sameS;
                sameU = jvmci ? sameU : d;
            }
        }
        Assert.assertEquals("the printable names collide", ObjIdRules.FwdProver.name(sameU), ObjIdRules.FwdProver.name(sameS));
        FwdTestWorld w = new FwdTestWorld(apis);
        ObjIdRules.FwdProver pr = new ObjIdRules.FwdProver(w);
        Assert.assertTrue(pr.isPure(sameU, 0, 0, new java.util.HashSet<>()));
        Assert.assertFalse("the memo is per method object", pr.isPure(sameS, 0, 0, new java.util.HashSet<>()));
        meta.lookupJavaType(G1MkBad.class).link(); // an unlinked class has no bytecode in JVMCI
        meta.lookupJavaType(G1MkCast.class).link();
        // bridge / target: the bridge is pure (its virtual call has no callee in this world), its same-named target
        // is not; a name-keyed memo answered the target from the bridge
        ResolvedJavaMethod bridge = bridgeOrTarget(meta, G1MkBad.class, "mk", true);
        ResolvedJavaMethod target = bridgeOrTarget(meta, G1MkBad.class, "mk", false);
        Assert.assertEquals("the printable names collide", ObjIdRules.FwdProver.name(bridge), ObjIdRules.FwdProver.name(target));
        w.callees.put(new ObjIdRules.FwdSite(bridge, bciOf(w.facts(bridge), "mk")), List.of());
        Assert.assertTrue(pr.isPure(bridge, 0, 0, new java.util.HashSet<>()));
        Assert.assertFalse("the memo is per method object", pr.isPure(target, 0, 0, new java.util.HashSet<>()));

        // a generic bridge with a checkcast forwards: G1MkCast.mk(Set)@getInstance <= bridge mk(Object) <= fwdMkOrigin
        ResolvedJavaMethod cb = bridgeOrTarget(meta, G1MkCast.class, "mk", true);
        ResolvedJavaMethod ct = bridgeOrTarget(meta, G1MkCast.class, "mk", false);
        w = new FwdTestWorld(apis);
        int cbb = bciOf(w.facts(cb), "mk");
        Assert.assertEquals("checkcast is identity", new ObjIdRules.FwdVal(ObjIdRules.FwdVal.PARAM, 0), w.facts(cb).arg(cbb, 0));
        w.call(cb, ct);
        w.callees.put(new ObjIdRules.FwdSite(cb, cbb), List.of(ct));
        w.callers.put(cb, List.of(new ObjIdRules.FwdSite(m.apply("fwdMkOrigin"), bciOf(w.facts(m.apply("fwdMkOrigin")), "mk"))));
        ObjIdRules.FwdVerdict v = new ObjIdRules.FwdProver(w).provePending(ct, bciOf(w.facts(ct), "getInstance"));
        Assert.assertTrue(v.reason(), v.ok());
        Assert.assertEquals(2, v.depth());
        // checkcast is identity; an invokedynamic capture is an escape; a handler start is a block start
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.PARAM, 0), facts.apply("fwdCast").arg(bciOf(facts.apply("fwdCast"), "getInstance"), 0));
        Assert.assertTrue(facts.apply("fwdCast").localPure(0));
        Assert.assertFalse("an invokedynamic capture escapes", facts.apply("fwdIndy").localPure(0));
        ResolvedJavaMethod hd = m.apply("fwdHandler");
        Assert.assertEquals(1, hd.getExceptionHandlers().length);
        Assert.assertTrue("the handler start is a block start", ObjIdRules.jumpTargets(hd.getCode(), hd).contains(hd.getExceptionHandlers()[0].getHandlerBCI()));
        Assert.assertTrue(facts.apply("fwdHandler").localPure(0));

        // the flow index (the image wiring): callees per declared target; callers = callee flows + declared + CHA superset
        ResolvedJavaMethod mirror = m.apply("fwdMirror");
        ResolvedJavaMethod decl = named(meta, G1Fac.class, "make2");
        ResolvedJavaMethod impl = named(meta, G1FacImpl.class, "make2");
        int mb = bciOf(w.facts(mirror), "make2");
        ObjIdRules.FwdIndex ix = new ObjIdRules.FwdIndex();
        ix.add(decl, mirror, mb, List.of(impl));
        ix.add(m.apply("scope"), mirror, mb, List.of()); // an inlined body's inner call at the same (outermost) position
        Assert.assertEquals(List.of(impl), List.copyOf(ix.calleesAt(mirror, mb, decl)));
        Assert.assertNull("no flow declaring inner()", ix.calleesAt(mirror, mb, m.apply("inner")));
        Assert.assertEquals(List.of(), List.copyOf(ix.calleesAt(mirror, mb, m.apply("scope"))));
        Assert.assertEquals(List.of(new ObjIdRules.FwdSite(mirror, mb)), List.copyOf(ix.callers(impl)));
        ResolvedJavaMethod top = m.apply("fwdMirrorTop");
        int tb = bciOf(w.facts(top), "fwdMirror");
        ix.add(impl, top, tb, null); // a devirtualised flow (declared = the override) with unknown callees
        Assert.assertNull("unknown callees", ix.calleesAt(top, tb, decl));
        Assert.assertTrue("declared-target callers", ix.callers(impl).contains(new ObjIdRules.FwdSite(top, tb)));
        ix.add(decl, top, tb + 1000, List.of());
        Assert.assertTrue("the CHA superset", ix.callers(impl).contains(new ObjIdRules.FwdSite(top, tb + 1000)));
        ix.add(impl, top, tb + 2000, List.of(impl));
        Assert.assertEquals("a flow declaring an override of the bytecode target", List.of(impl), List.copyOf(ix.calleesAt(top, tb + 2000, decl)));

        // bound: stash(o) inlined, only its inner flow at the position: the bytecode target stash is checked (impure)
        ResolvedJavaMethod ih = m.apply("fwdInlinedHelper");
        w = new FwdTestWorld(apis);
        w.index = new ObjIdRules.FwdIndex();
        w.index.add(m.apply("scope"), ih, bciOf(w.facts(ih), "stash"), List.of());
        Assert.assertFalse("an inlined bound helper is checked by its bytecode target", new ObjIdRules.FwdProver(w).isPure(ih, 0, 0, new java.util.HashSet<>()));
        // virtual: the interface hop with only a foreign flow at its position fails closed
        w = new FwdTestWorld(apis);
        w.index = new ObjIdRules.FwdIndex();
        w.index.add(m.apply("scope"), mirror, mb, List.of());
        w.call(mirror, impl);
        w.call(top, mirror);
        w.call(m.apply("fwdMirrorOrigin"), top);
        v = new ObjIdRules.FwdProver(w).provePending(impl, bciOf(w.facts(impl), "getInstance"));
        Assert.assertEquals("fwd:no-callees@" + ObjIdRules.FwdProver.name(mirror) + "@" + mb, v.reason());
        // ... and is proven with the interface flow present
        w.index.add(decl, mirror, mb, List.of(impl));
        v = new ObjIdRules.FwdProver(w).provePending(impl, bciOf(w.facts(impl), "getInstance"));
        Assert.assertTrue(v.reason(), v.ok());
    }

    /** Which G1 (c) failures become pending. */
    @Test
    public void g1FwdPendingAndKnob() {
        MetaAccessProvider meta = hostMeta();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(meta);
        Assert.assertTrue(ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(named(meta, ObjectIdentityTest.class, "g1cSetFromParameter"), apis), apis));
        Assert.assertTrue(ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(named(meta, ObjectIdentityTest.class, "fwdChain2"), apis), apis));
        Assert.assertTrue("a pending site is then decided by the derivation", ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(named(meta, ObjectIdentityTest.class, "g1cComplement"), apis),
                        apis));
        Assert.assertFalse("getInstance(Option) keeps today's rule", ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(named(meta, ObjectIdentityTest.class, "g1cFromParameter"), apis),
                        apis));
        Assert.assertFalse("a method handle is no factory call in the bytecode", ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(hostMethod2(meta, "g1cMethodHandle", Set.class), apis),
                        apis));
        Assert.assertFalse("a proven site is not pending", ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(named(meta, ObjectIdentityTest.class, "g1cEnumSetOf1"), apis), apis));
    }

    /**
     * The real JDK chain (labs-openjdk's Continuation.getStackTrace -> stackWalker(Set) -> stackWalker(Set, Scope) ->
     * JavaLangAccess.newStackWalkerInstance = System$1 -> StackWalker.newInstance). Fails loudly if the JDK shape changes.
     */
    @Test
    public void g1FwdJdkContinuation() throws Exception {
        MetaAccessProvider meta = hostMeta();
        ObjIdRules.PremiseApis apis = new ObjIdRules.PremiseApis(meta);
        ResolvedJavaType cont = meta.lookupJavaType(Class.forName("jdk.internal.vm.Continuation"));
        ResolvedJavaMethod getStackTrace = null;
        ResolvedJavaMethod sw1 = null;
        ResolvedJavaMethod sw2 = null;
        for (ResolvedJavaMethod d : cont.getDeclaredMethods(false)) {
            int n = d.getSignature().getParameterCount(false);
            getStackTrace = d.getName().equals("getStackTrace") && n == 0 ? d : getStackTrace;
            sw1 = d.getName().equals("stackWalker") && n == 1 ? d : sw1;
            sw2 = d.getName().equals("stackWalker") && n == 2 ? d : sw2;
        }
        ResolvedJavaMethod nsi = named(meta, Class.forName("java.lang.System$1"), "newStackWalkerInstance");
        Assert.assertNotNull(getStackTrace);
        Assert.assertNotNull(sw1);
        Assert.assertNotNull(sw2);
        ObjIdRules.FwdFacts gst = ObjIdRules.forwardFacts(getStackTrace, apis);
        Assert.assertEquals(new ObjIdRules.FwdVal(ObjIdRules.FwdVal.CONST, 1 << StackWalker.Option.SHOW_REFLECT_FRAMES.ordinal()), gst.arg(7, 0));
        Assert.assertEquals(sw1, gst.target.get(7));
        ObjIdRules.FwdFacts f1 = ObjIdRules.forwardFacts(sw1, apis);
        ObjIdRules.FwdFacts f2 = ObjIdRules.forwardFacts(sw2, apis);
        ObjIdRules.FwdFacts fn = ObjIdRules.forwardFacts(nsi, apis);
        Assert.assertTrue(f1.localPure(0));
        Assert.assertTrue(f2.localPure(0));
        Assert.assertTrue(fn.localPure(0));
        Assert.assertEquals(sw2, f1.target.get(6));
        Assert.assertEquals("newStackWalkerInstance", f2.target.get(9).getName());
        Assert.assertEquals(0, apis.setParamIndex(fn.target.get(4)));
        Assert.assertEquals(List.of(4), fn.uses.get(0).stream().map(u -> u[0]).toList());
        // the bytecode-only part does not prove it (the local window rule): the derivation does
        Assert.assertTrue(ObjIdRules.bytecodeUses(nsi, apis).walkerBuild);
        Assert.assertTrue(ObjectIdentityRule.allSetFactories(ObjIdRules.bytecodeUses(nsi, apis), apis));
        FwdTestWorld w = new FwdTestWorld(apis);
        w.callers.put(nsi, List.of(new ObjIdRules.FwdSite(sw2, 9)));
        w.callees.put(new ObjIdRules.FwdSite(sw2, 9), List.of(nsi));
        w.callers.put(sw2, List.of(new ObjIdRules.FwdSite(sw1, 6)));
        w.callees.put(new ObjIdRules.FwdSite(sw1, 6), List.of(sw2)); // an invokevirtual: the points-to callees in the image
        w.callers.put(sw1, List.of(new ObjIdRules.FwdSite(getStackTrace, 7)));
        ObjIdRules.FwdVerdict v = new ObjIdRules.FwdProver(w).provePending(nsi, 4);
        Assert.assertTrue(v.reason(), v.ok());
        Assert.assertEquals(3, v.depth());
    }
}
