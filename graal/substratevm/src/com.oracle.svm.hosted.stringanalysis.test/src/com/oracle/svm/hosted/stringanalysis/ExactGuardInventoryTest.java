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
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.java.GraphBuilderPhase;
import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.OptimisticOptimizations;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.runtime.JVMCIBackend;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;

/**
 * Exact-guard inventory pins (the {@code Field.binaryValue} shape: the dominating {@code instanceof BytesRef} folds
 * exact in the decoded graph, so skipping exact instanceofs would leave the guard inventory empty and no class-check
 * coverage test could fire). Exact instanceofs are collected with {@link LocalFlowGraph.TypeGuard#exact}, usable only
 * in the never direction (exact-pass ⊆ target-assignability: a key population with no target-assignable member passes
 * it for no member and no substituted rep). The vacuous (always-succeeds) direction stays non-exact only: an assignable
 * member can still fail an exact test, so assignability does not derive "always passes". The record-time consumer
 * ({@code classCheckUsageSkipped}'s never direction) is pinned by the class-check skip tests.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class ExactGuardInventoryTest {

    /** The minimal JVMCI-backed universe. */
    private static final class UniverseFixture {
        final MetaAccessProvider metaAccess;
        final AnalysisUniverse universe;

        UniverseFixture() {
            JVMCIBackend backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
            this.metaAccess = backend.getMetaAccess();
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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), ExactGuardInventoryTest.class.getClassLoader()) {
                @Override
                public void onTypeReachable(com.oracle.graal.pointsto.BigBang bb, AnalysisType type) {
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
            DefaultAnalysisPolicy policy = new DefaultAnalysisPolicy(new OptionValues(EconomicMap.create()));
            this.universe = new AnalysisUniverse(host, JavaKind.Object, policy, SubstitutionProcessor.IDENTITY,
                            metaAccess, new PointsToAnalysisFactory(), annotations);
            lookup(Object.class);
            lookup(Cloneable.class);
            lookup(String.class);
            lookup(Number.class);
            lookup(Integer.class);
        }

        AnalysisType lookup(Class<?> clazz) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(clazz));
        }

        Function<ResolvedJavaType, AnalysisType> resolver() {
            return universe::lookup;
        }
    }

    /**
     * The {@code Field.binaryValue} shape in miniature: param → an instanceof IfNode; the true (covered) arm hosts the
     * class-check root (a GetClassNode on the param, anchored at the arm's ReturnNode), the false arm returns null. With
     * an exact condition on a String-incompatible target this is
     * {@code if (fieldsData instanceof BytesRef) { …getClass/checkcast… } else return null}: for a {String} population
     * the covered arm is provably dead.
     */
    private static final class ExactGuardGraph {
        final StructuredGraph graph;
        final StartNode start;
        final ParameterNode param;
        final IfNode guardIf;
        final BeginNode trueArm;
        final GetClassNode getClassRoot;

        static ExactGuardGraph make(UniverseFixture universe, AnalysisMethod methodForGraph,
                        Class<?> guardTarget, boolean exact, boolean rootOnCoveredArm) {
            OptionValues options = new OptionValues(EconomicMap.create());
            DebugContext debug = new DebugContext.Builder(options).build();
            StructuredGraph graph = new StructuredGraph.Builder(options, debug)
                            .name("ExactGuardInventoryTest").method(methodForGraph).build();
            StartNode start = graph.add(new StartNode());
            graph.setStart(start);
            Stamp objectStamp = StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(
                            (ResolvedJavaType) universe.metaAccess.lookupJavaType(Object.class)));
            ParameterNode param = graph.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(objectStamp)));
            ResolvedJavaType target = (ResolvedJavaType) universe.metaAccess.lookupJavaType(guardTarget);
            // createWithoutAssumptions is exact iff the target is a leaf (Integer is);
            // createExactTrusted forces exact for non-leaf targets; the non-exact control
            // uses String (de-finalized in the builder JDK — a non-leaf).
            TypeReference targetRef = exact
                            ? TypeReference.createExactTrusted(target)
                            : TypeReference.createWithoutAssumptions(target);
            InstanceOfNode condition = (InstanceOfNode) graph.addOrUnique(InstanceOfNode.create(targetRef, param));
            BeginNode trueArm = graph.add(new BeginNode());
            BeginNode falseArm = graph.add(new BeginNode());
            IfNode guardIf = graph.add(new IfNode(condition, trueArm, falseArm, null));
            Stamp classStamp = StampFactory.object(TypeReference.createWithoutAssumptions(
                            (ResolvedJavaType) universe.metaAccess.lookupJavaType(Class.class)));
            GetClassNode getClass = graph.addWithoutUnique(new GetClassNode(classStamp, param));
            ReturnNode rootRet = graph.addWithoutUnique(new ReturnNode(getClass));
            ReturnNode otherRet = graph.addWithoutUnique(new ReturnNode(null));
            trueArm.setNext(rootOnCoveredArm ? rootRet : otherRet);
            falseArm.setNext(rootOnCoveredArm ? otherRet : rootRet);
            start.setNext(guardIf);
            return new ExactGuardGraph(graph, start, param, guardIf, trueArm, getClass);
        }

        private ExactGuardGraph(StructuredGraph graph, StartNode start, ParameterNode param,
                        IfNode guardIf, BeginNode trueArm, GetClassNode getClassRoot) {
            this.graph = graph;
            this.start = start;
            this.param = param;
            this.guardIf = guardIf;
            this.trueArm = trueArm;
            this.getClassRoot = getClassRoot;
        }
    }

    @SuppressWarnings("unused")
    private static final class Holder {
        public Object exactGuardMethod(Object v) {
            return v;
        }
    }

    private static AnalysisMethod holderMethod(UniverseFixture f) throws Exception {
        return f.universe.lookup(
                        (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                                        Holder.class.getDeclaredMethod("exactGuardMethod", Object.class)));
    }

    /**
     * Pin 1: an exact-instanceof IfNode is collected into the guard inventory, keyed on the Pi-skipped tested value, with
     * {@code exact=true} and the resolved target.
     */
    @Test
    public void exactGuardIsCollectedIntoInventory() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ExactGuardGraph g = ExactGuardGraph.make(f, holderMethod(f), Integer.class, true, true);
        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LfgWalk.collectGuardsInto(lfg, g.graph, f.resolver());
        List<LocalFlowGraph.TypeGuard> guards = lfg.guardsForValue(g.param);
        Assert.assertEquals("the exact instanceof guard IS collected (keyed on the tested value)",
                        1, guards.size());
        Assert.assertTrue("the collected guard carries exact=true", guards.get(0).exact);
        Assert.assertEquals("the target resolves to the checked class",
                        f.lookup(Integer.class), guards.get(0).targetType);
    }

    /**
     * Pin 2 (the never direction): a class check whose anchors are only reachable through the exact guard's covered arm
     * gets the guard in the never list (dead-arm evidence for a key population with no target-assignable member) and not
     * in the vacuous list.
     */
    @Test
    public void exactGuardCoversNeverDirectionOnly() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ExactGuardGraph g = ExactGuardGraph.make(f, holderMethod(f), Integer.class, true, true);
        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LfgWalk.collectGuardsInto(lfg, g.graph, f.resolver());
        List<Node> anchors = LocalFlowGraph.fixedAnchorsOfRoot(g.getClassRoot);
        Assert.assertFalse("precondition: the class-check root has fixed anchors", anchors.isEmpty());
        List<LocalFlowGraph.TypeGuard> vacuous = new java.util.ArrayList<>();
        List<LocalFlowGraph.TypeGuard> never = new java.util.ArrayList<>();
        LfgWalk.guardListsFor(g.start, anchors, lfg.guardsForValue(g.param), vacuous, never);
        Assert.assertEquals("the exact guard lands in the NEVER list (covered arm dead for a " +
                        "non-assignable population)", 1, never.size());
        Assert.assertTrue(never.get(0).exact);
        Assert.assertEquals("the exact guard NEVER lands in the vacuous list (the " +
                        "covered-direction exclusion)", 0, vacuous.size());
    }

    /**
     * Pin 3 (the non-exact-only corner): an exact guard whose target is assignable from every block member (Object) must
     * not produce a vacuous (always-succeeds) skip even in the dead-arm shape: an assignable member can still fail the
     * exact test, so "always passes" is not derivable.
     */
    @Test
    public void exactGuardNeverFiresVacuousEvenWhenAssignable() throws Exception {
        UniverseFixture f = new UniverseFixture();
        // root on the dead arm (the vacuous shape) + an exact-Object guard: assignability
        // would "cover" every population, the exact test still fails for String.
        ExactGuardGraph g = ExactGuardGraph.make(f, holderMethod(f), Object.class, true, false);
        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LfgWalk.collectGuardsInto(lfg, g.graph, f.resolver());
        Assert.assertEquals(1, lfg.guardsForValue(g.param).size());
        Assert.assertTrue(lfg.guardsForValue(g.param).get(0).exact);
        List<Node> anchors = LocalFlowGraph.fixedAnchorsOfRoot(g.getClassRoot);
        List<LocalFlowGraph.TypeGuard> vacuous = new java.util.ArrayList<>();
        List<LocalFlowGraph.TypeGuard> never = new java.util.ArrayList<>();
        LfgWalk.guardListsFor(g.start, anchors, lfg.guardsForValue(g.param), vacuous, never);
        Assert.assertEquals("NO vacuous skip through an exact guard (the covered-direction exclusion, preserved)",
                        0, vacuous.size());
    }

    /**
     * Pin 4: a non-exact instanceof (String, de-finalized in the builder JDK, hence a non-leaf) is still collected, and
     * the dead-arm shape still produces the vacuous list.
     */
    @Test
    public void nonExactGuardKeepsBothDirections() throws Exception {
        UniverseFixture f = new UniverseFixture();
        ExactGuardGraph g = ExactGuardGraph.make(f, holderMethod(f), String.class, false, false);
        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LfgWalk.collectGuardsInto(lfg, g.graph, f.resolver());
        List<LocalFlowGraph.TypeGuard> guards = lfg.guardsForValue(g.param);
        Assert.assertEquals(1, guards.size());
        Assert.assertFalse("the String guard stays NON-exact (the de-finalized builder JDK)",
                        guards.get(0).exact);
        List<Node> anchors = LocalFlowGraph.fixedAnchorsOfRoot(g.getClassRoot);
        List<LocalFlowGraph.TypeGuard> vacuous = new java.util.ArrayList<>();
        List<LocalFlowGraph.TypeGuard> never = new java.util.ArrayList<>();
        LfgWalk.guardListsFor(g.start, anchors, guards, vacuous, never);
        Assert.assertEquals("the dead-arm (vacuous) direction still collects the non-exact guard",
                        1, vacuous.size());
    }
}
