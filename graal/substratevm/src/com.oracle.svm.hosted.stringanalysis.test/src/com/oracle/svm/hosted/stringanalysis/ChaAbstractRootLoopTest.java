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
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

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
 * Pins that the rule "an abstract class's own resolution is never a runtime target"
 * holds in the subtype loop of {@link DispatchResolution#computeDeterministicChaTargets}, pinned on real AnalysisTypes.
 * {@code getAllSubtypes()} includes the root itself and every abstract intermediate, so the loop must not re-add what
 * the root clause skips. Each test builds a fresh universe, instantiates exactly the named concrete classes, and pins
 * the full target set.
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
public class ChaAbstractRootLoopTest {

    // --- shape 1: the TermsHashPerField shape; every concrete subtype overrides (plus an overriding abstract middle)
    abstract static class AbsRoot {
        void start() {
        }
    }

    static final class SubA extends AbsRoot {
        @Override
        void start() {
        }
    }

    static final class SubB extends AbsRoot {
        @Override
        void start() {
        }
    }

    abstract static class AbsMid extends AbsRoot {
        @Override
        void start() {
        }
    }

    static final class MidLeaf extends AbsMid {
        @Override
        void start() {
        }
    }

    // --- shape 2: an inherited, non-overridden method of an abstract class (directly and below an abstract middle)
    abstract static class AbsInh {
        void run() {
        }
    }

    static final class InhOverride extends AbsInh {
        @Override
        void run() {
        }
    }

    static final class InhHeir extends AbsInh {
    }

    abstract static class AbsInhMid extends AbsInh {
    }

    static final class InhMidHeir extends AbsInhMid {
    }

    // --- shape 3: an interface default method, inherited by abstract classes
    interface Greeter {
        default void greet() {
        }
    }

    abstract static class AbsGreeter implements Greeter {
    }

    static final class GreeterHeir extends AbsGreeter {
    }

    abstract static class AbsGreeterAll implements Greeter {
    }

    static final class GreeterAllOverride extends AbsGreeterAll {
        @Override
        public void greet() {
        }
    }

    /** A JVMCI-backed analysis universe (the StringAtomEndToEndTest shape) whose types can be instantiated. */
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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), ChaAbstractRootLoopTest.class.getClassLoader()) {
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
             * registerAsInstantiated and method creation (prepareMethodImplementations resolves on every subtype,
             * interfaces included: the fallback resolution) call the analysis. A no-op stand-in answers null/false (the
             * fixture runs no analysis). Every type exists by now: a type created later would register itself with the
             * stand-in and fail loudly (it is no PointsToAnalysis).
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

        void instantiate(Class<?>... classes) {
            for (Class<?> c : classes) {
                type(c).registerAsInstantiated("ChaAbstractRootLoopTest fixture");
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
                return "ChaAbstractRootLoopTest.NoOpBigBang";
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

    private static void assertTargets(String what, AnalysisMethod callee, AnalysisType root, String... expected) {
        Set<String> got = new TreeSet<>();
        for (AnalysisMethod m : DispatchResolution.computeDeterministicChaTargets(callee, root)) {
            String holder = m.getDeclaringClass().toJavaName(false);
            got.add(holder.substring(holder.lastIndexOf('$') + 1) + "." + m.getName());
        }
        Assert.assertEquals(what, new TreeSet<>(Arrays.asList(expected)), got);
    }

    /** Every concrete subtype overrides: neither the abstract root's nor the abstract middle's own method is a target. */
    @Test
    public void abstractRootFullyOverriddenIsNoTarget() {
        World w = new World(AbsRoot.class, SubA.class, SubB.class, AbsMid.class, MidLeaf.class);
        w.instantiate(SubA.class, SubB.class, MidLeaf.class);
        AnalysisType root = w.type(AbsRoot.class);
        Assert.assertTrue("the premise: getAllSubtypes includes the root itself", root.getAllSubtypes().contains(root));
        Assert.assertTrue("the premise: the abstract root passes isAnySubtypeInstantiated", root.isAnySubtypeInstantiated());
        AnalysisMethod start = w.method(AbsRoot.class, "start");
        assertTargets("root AbsRoot", start, root, "SubA.start", "SubB.start", "MidLeaf.start");
        assertTargets("root AbsMid (an abstract root that overrides)", start, w.type(AbsMid.class), "MidLeaf.start");
        assertTargets("root SubA (concrete)", start, w.type(SubA.class), "SubA.start");
    }

    /** An inherited, non-overridden method stays a target through its concrete heir, and only through it. */
    @Test
    public void inheritedMethodKeptThroughConcreteHeir() {
        Class<?>[] all = {AbsInh.class, InhOverride.class, InhHeir.class, AbsInhMid.class, InhMidHeir.class};
        World w = new World(all);
        w.instantiate(InhOverride.class, InhHeir.class);
        AnalysisMethod run = w.method(AbsInh.class, "run");
        assertTargets("direct heir", run, w.type(AbsInh.class), "AbsInh.run", "InhOverride.run");

        World w2 = new World(all);
        w2.instantiate(InhOverride.class, InhMidHeir.class);
        AnalysisMethod run2 = w2.method(AbsInh.class, "run");
        assertTargets("heir below an abstract middle", run2, w2.type(AbsInh.class), "AbsInh.run", "InhOverride.run");
        assertTargets("root the abstract middle", run2, w2.type(AbsInhMid.class), "AbsInh.run");

        World w3 = new World(all);
        w3.instantiate(InhOverride.class);
        AnalysisMethod run3 = w3.method(AbsInh.class, "run");
        assertTargets("no concrete heir inherits it", run3, w3.type(AbsInh.class), "InhOverride.run");
    }

    /** An interface default method: kept through a concrete heir; dropped where every concrete heir overrides it. */
    @Test
    public void interfaceDefaultMethod() {
        Class<?>[] all = {Greeter.class, AbsGreeter.class, GreeterHeir.class, AbsGreeterAll.class, GreeterAllOverride.class};
        World w = new World(all);
        w.instantiate(GreeterHeir.class, GreeterAllOverride.class);
        AnalysisMethod greet = w.method(Greeter.class, "greet");
        assertTargets("root the interface", greet, w.type(Greeter.class), "Greeter.greet", "GreeterAllOverride.greet");
        assertTargets("root an abstract class that inherits the default", greet, w.type(AbsGreeter.class), "Greeter.greet");
        assertTargets("root an abstract class whose heirs all override", greet, w.type(AbsGreeterAll.class), "GreeterAllOverride.greet");

        World w2 = new World(all);
        w2.instantiate(GreeterAllOverride.class);
        AnalysisMethod greet2 = w2.method(Greeter.class, "greet");
        assertTargets("root the interface, no heir inherits the default", greet2, w2.type(Greeter.class), "GreeterAllOverride.greet");
    }

    /**
     * A virtual callee without an invoke flow (a scope invoke to which the call-site identity
     * rule gives none, {@code ForwardFixpoint.callFlowAt}) resolves over the cone of its declaring class: every
     * instantiated override, not the declared method alone (no invokespecial shortcut).
     */
    @Test
    public void virtualCalleeWithoutFlowTakesTheDeclaringClassCone() {
        World w = new World(AbsRoot.class, SubA.class, SubB.class, AbsMid.class, MidLeaf.class);
        w.instantiate(SubA.class, SubB.class, MidLeaf.class);
        AnalysisMethod start = w.method(AbsRoot.class, "start");
        Assert.assertFalse("the premise: a virtual callee", start.isStatic() || start.canBeStaticallyBound());
        Set<String> got = new TreeSet<>();
        for (AnalysisMethod m : DispatchResolution.computeDeterministicChaTargets(start, (com.oracle.graal.pointsto.flow.InvokeTypeFlow) null)) {
            String holder = m.getDeclaringClass().toJavaName(false);
            got.add(holder.substring(holder.lastIndexOf('$') + 1) + "." + m.getName());
        }
        Assert.assertEquals(new TreeSet<>(Arrays.asList("SubA.start", "SubB.start", "MidLeaf.start")), got);
        assertTargets("= the declaring class as the root", start, w.type(AbsRoot.class), "SubA.start", "SubB.start", "MidLeaf.start");
    }

    /** Arrays are excepted: JVMCI reports them ABSTRACT|FINAL, but an array is the exact type of its objects. */
    @Test
    public void arraysAreExcepted() {
        World w = new World(AbsRoot.class, Object[].class, AbsRoot[].class);
        w.instantiate(AbsRoot[].class);
        AnalysisType array = w.type(AbsRoot[].class);
        Assert.assertTrue("the premise: JVMCI reports an array abstract", Modifier.isAbstract(array.getModifiers()));
        AnalysisType cloneable = w.type(Cloneable.class);
        Assert.assertTrue("the premise: the array is in Cloneable's subtype loop", cloneable.getAllSubtypes().contains(array));
        AnalysisMethod toStr = w.method(Object.class, "toString");
        assertTargets("an interface root whose only instantiated subtype is an array (the loop)", toStr, cloneable, "Object.toString");
        assertTargets("the array root itself (the root clause)", toStr, array, "Object.toString");
    }
}
