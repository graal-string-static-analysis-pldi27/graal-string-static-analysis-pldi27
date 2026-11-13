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
import java.util.List;

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
 * Pins of the receiver-aware dispatch rule ({@link DispatchResolution#receiverDispatchTargets},
 * {@link DispatchResolution#receiverDispatchTarget}), on real AnalysisTypes. The rule serves three facts: the atom's own
 * exact type at the receiver position (the exactrecv rule, its one-type case), the receiver sink's atoms at a
 * backward invoke result, and the call's final points-to receiver state at argument and result
 * positions. Pinned: narrowing to the receivers' resolutions in fan order; every doubt keeps the committed fan
 * (null); the rule never adds a target.
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
public class ReceiverDispatchTest {

    interface Shape {
        void draw();
    }

    static final class Circle implements Shape {
        @Override
        public void draw() {
        }
    }

    static final class Square implements Shape {
        @Override
        public void draw() {
        }
    }

    static final class Tri implements Shape {
        @Override
        public void draw() {
        }
    }

    static class Base implements Shape {
        @Override
        public void draw() {
        }
    }

    static final class Heir extends Base {
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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), ReceiverDispatchTest.class.getClassLoader()) {
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
                return "ReceiverDispatchTest.NoOpBigBang";
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

    private static List<String> names(List<DispatchResolution.ResolvedTarget> ts) {
        if (ts == null) {
            return null;
        }
        List<String> out = new ArrayList<>();
        for (DispatchResolution.ResolvedTarget t : ts) {
            String holder = t.method().getDeclaringClass().toJavaName(false);
            out.add(holder.substring(holder.lastIndexOf('$') + 1) + "." + t.method().getName());
        }
        return out;
    }

    private static final Class<?>[] ALL = {Shape.class, Circle.class, Square.class, Tri.class, Base.class, Heir.class};

    /** One receiver type selects its own resolution; several keep the fan's order; an inherited method is its heir's target. */
    @Test
    public void receiverTypesNarrowToTheirResolutionsInFanOrder() {
        World w = new World(ALL);
        AnalysisMethod draw = w.method(Shape.class, "draw");
        List<DispatchResolution.ResolvedTarget> fan = List.of(target(w.method(Circle.class, "draw")), target(w.method(Square.class, "draw")),
                        target(w.method(Tri.class, "draw")), target(w.method(Base.class, "draw")));
        Assert.assertEquals(List.of("Square.draw"), names(DispatchResolution.receiverDispatchTargets(List.of(w.type(Square.class)), draw, fan)));
        Assert.assertEquals("fan order, not type order", List.of("Circle.draw", "Tri.draw"),
                        names(DispatchResolution.receiverDispatchTargets(List.of(w.type(Tri.class), w.type(Circle.class)), draw, fan)));
        Assert.assertEquals("an heir that inherits dispatches to its ancestor's method", List.of("Base.draw"),
                        names(DispatchResolution.receiverDispatchTargets(List.of(w.type(Heir.class)), draw, fan)));
        Assert.assertEquals("repeated types select once", List.of("Circle.draw"),
                        names(DispatchResolution.receiverDispatchTargets(List.of(w.type(Circle.class), w.type(Circle.class)), draw, fan)));
    }

    /** Every doubt keeps the committed fan (null): the caller then takes the fan (or its committed cap refusal). */
    @Test
    public void everyDoubtKeepsTheCommittedFan() {
        World w = new World(ALL);
        AnalysisMethod draw = w.method(Shape.class, "draw");
        List<DispatchResolution.ResolvedTarget> fan = List.of(target(w.method(Circle.class, "draw")), target(w.method(Square.class, "draw")));
        Assert.assertNull("no receiver type", DispatchResolution.receiverDispatchTargets(List.of(), draw, fan));
        Assert.assertNull("no receiver types at all", DispatchResolution.receiverDispatchTargets(null, draw, fan));
        Assert.assertNull("an unknown (null) type among the receivers", DispatchResolution.receiverDispatchTargets(Arrays.asList(w.type(Circle.class), null), draw, fan));
        Assert.assertNull("a resolution outside the committed fan", DispatchResolution.receiverDispatchTargets(List.of(w.type(Circle.class), w.type(Tri.class)), draw, fan));
        Assert.assertNull("a type with no resolution of the callee", DispatchResolution.receiverDispatchTargets(List.of(w.type(Object.class)), draw, fan));
        Assert.assertNull("no narrowing: every fan target selected", DispatchResolution.receiverDispatchTargets(List.of(w.type(Square.class), w.type(Circle.class)), draw, fan));
        Assert.assertNull("a fan of one: nothing to narrow", DispatchResolution.receiverDispatchTargets(List.of(w.type(Circle.class)), draw, fan.subList(0, 1)));
        Assert.assertNull("no callee", DispatchResolution.receiverDispatchTargets(List.of(w.type(Circle.class)), null, fan));
        Assert.assertNull("the per-type form: outside the fan", DispatchResolution.receiverDispatchTarget(w.type(Tri.class), draw, fan));
        Assert.assertNull("the per-type form: unknown type", DispatchResolution.receiverDispatchTarget(null, draw, fan));
        Assert.assertEquals("the per-type form: inside the fan", w.method(Square.class, "draw"), DispatchResolution.receiverDispatchTarget(w.type(Square.class), draw, fan));
    }

    /** The rule never adds a target: over every subset of receiver types, the result is null or a strict subset of the fan. */
    @Test
    public void theRuleNeverAddsATarget() {
        World w = new World(ALL);
        AnalysisMethod draw = w.method(Shape.class, "draw");
        List<DispatchResolution.ResolvedTarget> fan = List.of(target(w.method(Circle.class, "draw")), target(w.method(Tri.class, "draw")),
                        target(w.method(Base.class, "draw")));
        AnalysisType[] types = {w.type(Circle.class), w.type(Square.class), w.type(Tri.class), w.type(Heir.class), w.type(Object.class)};
        for (int mask = 1; mask < 1 << types.length; mask++) {
            List<AnalysisType> sel = new ArrayList<>();
            for (int i = 0; i < types.length; i++) {
                if ((mask & 1 << i) != 0) {
                    sel.add(types[i]);
                }
            }
            List<DispatchResolution.ResolvedTarget> out = DispatchResolution.receiverDispatchTargets(sel, draw, fan);
            if (out != null) {
                Assert.assertTrue("a strict narrowing " + sel, out.size() < fan.size() && !out.isEmpty());
                Assert.assertTrue("a subset of the fan " + sel, fan.containsAll(out));
            }
            boolean anyOutside = (mask & (1 << 1 | 1 << 4)) != 0; // Square (not in the fan) or Object (no resolution)
            if (anyOutside) {
                Assert.assertNull("a doubt keeps the fan " + sel, out);
            }
        }
    }

    /** The receiver-position case (exactrecv): one exact type keeps every fan entry of its resolution. */
    @Test
    public void theOneTypeCaseKeepsEveryEntryOfItsResolution() {
        World w = new World(ALL);
        AnalysisMethod draw = w.method(Shape.class, "draw");
        AnalysisMethod circle = w.method(Circle.class, "draw");
        List<DispatchResolution.ResolvedTarget> fan = List.of(target(circle), target(w.method(Square.class, "draw")),
                        new DispatchResolution.ResolvedTarget(circle, null, null, false, "a second entry of the same method"));
        List<DispatchResolution.ResolvedTarget> out = DispatchResolution.receiverDispatchTargets(List.of(w.type(Circle.class)), draw, fan);
        Assert.assertEquals(2, out.size());
        Assert.assertSame(fan.get(0), out.get(0));
        Assert.assertSame(fan.get(2), out.get(1));
    }
}
