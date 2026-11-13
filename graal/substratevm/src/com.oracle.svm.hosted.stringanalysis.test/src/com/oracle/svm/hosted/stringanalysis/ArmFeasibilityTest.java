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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.graph.Node;

import jdk.graal.compiler.nodes.BeginNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
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
import jdk.vm.ci.runtime.JVMCIBackend;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;

/**
 * Pins of the value-relative arm-feasibility predicate ({@code ForwardFixpoint.armDeadDirection}, applied by
 * {@code StrackSites.armDead} to the STRING atoms' usage anchors): the guard-kind table (exact vs hierarchy x
 * in-cone/out-of-cone x member split), the TOP decline, the unwired-vertex keep, and the per-entry grain (one usage
 * site skips for one carried block and keeps for another). Each pin is a pure function of (guard kind, tested type,
 * carried block, closed-world types).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class ArmFeasibilityTest {

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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), ArmFeasibilityTest.class.getClassLoader()) {
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

        java.util.function.Function<ResolvedJavaType, AnalysisType> resolver() {
            return universe::lookup;
        }
    }

    /** A usage anchor with the given vacuous/never guard lists (in production computed by {@code LfgWalk.guardListsFor}). */
    private static Site siteWith(List<LocalFlowGraph.TypeGuard> vacuous,
                    List<LocalFlowGraph.TypeGuard> never) {
        return new Site(vacuous, never);
    }

    /** One usage anchor's guard lists (the pair {@code StrackSites.armDead} computes per anchor). */
    private record Site(List<LocalFlowGraph.TypeGuard> vacuous, List<LocalFlowGraph.TypeGuard> never) {
    }

    /** The predicate under test: the anchor's usage is dead for {@code block}. */
    private static boolean armDead(Site site, ForwardFixpoint.Block block) {
        return ForwardFixpoint.armDeadDirection(site.vacuous(), site.never(), block) != 0;
    }

    /** A guard on the fixture's shared param node (identity key irrelevant at predicate grain). */
    private static LocalFlowGraph.TypeGuard guard(UniverseFixture f, Class<?> target, boolean exact) {
        // the TypeGuard constructor requires non-null arm nodes; the predicate ignores them
        BeginNode trueArm = new BeginNode();
        BeginNode falseArm = new BeginNode();
        return new LocalFlowGraph.TypeGuard(trueArm, trueArm, f.lookup(target), exact, false, trueArm, falseArm);
    }

    @SuppressWarnings("unused")
    private static final class Holder {
        public Object exactGuardMethod(Object v) {
            return v;
        }

        public Object orShapeMethod(Object v) {
            return v;
        }
    }

    private static ForwardFixpoint.Block blockOf(AnalysisType... types) {
        Set<AnalysisType> set = new LinkedHashSet<>();
        for (AnalysisType t : types) {
            set.add(t);
        }
        return ForwardFixpoint.Block.of(set);
    }

    /**
     * PIN 1 (the storedValue shape — the vacuous/hierarchy direction): a non-exact
     * hierarchy {@code instanceof String} guard whose dead arm hosts the site's
     * anchors, with a {String} block — every member (and every substituted rep —
     * the widened cone is the block) is String-assignable, the test provably
     * always-succeeds, the dead arm is unreachable for this entry → the usage is
     * not a usage of this value → skip. This suppresses the phantom
     * {@code getClass @ Field#storedValue@-1}.
     */
    @Test
    public void hierarchyStringGuardSkipsStringBlock() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(List.of(guard(f, String.class, false)), List.of());
        Assert.assertTrue("the {String} entry skips the dead (else) arm behind instanceof String",
                        armDead(site, blockOf(f.lookup(String.class))));
    }

    /**
     * PIN 2 (member split): the same vacuous String guard, but the carried block is {String, Integer}: the members
     * disagree (Integer is not String-assignable, so the test does not provably always succeed) → no proof → keep.
     */
    @Test
    public void splitBlockMemberDisagreementKeepsBothArms() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(List.of(guard(f, String.class, false)), List.of());
        Assert.assertFalse("a member-split block keeps both arms (no proof)",
                        armDead(site, blockOf(f.lookup(String.class), f.lookup(Integer.class))));
    }

    /**
     * PIN 3 (the never direction — the binaryValue shape): a guard whose COVERED
     * arm hosts the site's anchors, with a {String} block and an out-of-cone
     * target (Integer): no member is assignable → the test provably always-fails
     * (for String and for every rep — the two-sided a-fortiori argument) → the
     * covered arm is dead for this entry → skip.
     */
    @Test
    public void outOfConeTargetNeverDirectionSkips() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(List.of(), List.of(guard(f, Integer.class, false)));
        Assert.assertTrue("the {String} entry skips the covered arm of instanceof Integer",
                        armDead(site, blockOf(f.lookup(String.class))));
    }

    /**
     * PIN 4 (the never direction's assignable side — keep): the same covered-arm
     * site, but the carried block is assignable ({Integer}): the members may pass
     * the test → no proof → keep.
     */
    @Test
    public void assignableBlockKeepsCoveredArm() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(List.of(), List.of(guard(f, Integer.class, false)));
        Assert.assertFalse("an assignable member keeps the covered arm",
                        armDead(site, blockOf(f.lookup(Integer.class))));
    }

    /**
     * PIN 5 (the exact rep-divergence rule): an exact {@code instanceof String}-shaped guard (the class-mirror fold)
     * can never give a vacuous proof: a rep fails an exact String test even though it is assignable. With the exact
     * guard in the never list and {String} carried, the skip does not fire; with an out-of-cone block it does
     * (not assignable implies the exact test fails too).
     */
    @Test
    public void exactStringTestKeepsBothArmsForInConeBlocks() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(List.of(), List.of(guard(f, String.class, true)));
        Assert.assertFalse("an exact String test with an in-cone block keeps both arms (rep divergence)",
                        armDead(site, blockOf(f.lookup(String.class))));
        // out-of-cone block: no member assignable → exact fails for all → skip fires
        Assert.assertTrue("the same exact site skips for a provably out-of-cone block",
                        armDead(site, blockOf(f.lookup(Integer.class))));
    }

    /**
     * PIN 6 (the TOP decline): a ⊤ block proves nothing; every usage is kept.
     */
    @Test
    public void topBlockDeclinesEveryProof() {
        UniverseFixture f = new UniverseFixture();
        Site vacuousSite = siteWith(List.of(guard(f, String.class, false)), List.of());
        Site neverSite = siteWith(List.of(), List.of(guard(f, Integer.class, false)));
        Assert.assertFalse("TOP keeps the vacuous-dead arm",
                        armDead(vacuousSite, ForwardFixpoint.Block.TOP));
        Assert.assertFalse("TOP keeps the never-dead arm",
                        armDead(neverSite, ForwardFixpoint.Block.TOP));
    }

    /**
     * PIN 7 (the unwired vertex): a usage-site vertex with no guard lists (never wired by the walk phase) keeps its
     * usage for every block.
     */
    @Test
    public void unwiredSiteKeepsEveryBlock() {
        UniverseFixture f = new UniverseFixture();
        Site site = siteWith(null, null);
        Assert.assertFalse("an unwired vertex keeps its usage",
                        armDead(site, blockOf(f.lookup(String.class))));
    }

    /**
     * PIN 8 (the per-entry grain): one usage site, two entries with different carried blocks: the {String} entry skips
     * the instanceof-String dead arm; the {Integer} entry keeps it (the vacuous String guard does not cover Integer, and
     * the never-listed Integer guard does not fire for an Integer member). Feasibility is a function of the carried
     * block, never of the method alone.
     */
    @Test
    public void sameSiteDifferentBlocksDecideIndependently() {
        UniverseFixture f = new UniverseFixture();
        // the site sits behind instanceof String's dead arm (vacuous) and behind
        // instanceof Integer's covered arm (never): a two-guard chain, the
        // storedValue else-arm shape.
        Site site = siteWith(
                        List.of(guard(f, String.class, false)),
                        List.of(guard(f, Integer.class, false)));
        ForwardFixpoint.Block stringBlock = blockOf(f.lookup(String.class));
        ForwardFixpoint.Block integerBlock = blockOf(f.lookup(Integer.class));
        // the String entry: vacuous (all members String-assignable) → skip
        Assert.assertTrue("the {String} entry skips (the String arm is taken)",
                        armDead(site, stringBlock));
        // the Integer entry: the never guard does not fire (the Integer member is Integer-assignable) and the vacuous
        // guard does not cover it → keep
        Assert.assertFalse("the {Integer} entry keeps the site (its arm differs)",
                        armDead(site, integerBlock));
        // the widened Number block (the production contract: Block.of over widenType —
        // every instantiated subtype is a member): Integer is a member and is
        // Integer-assignable, so the never direction declines; Number is not
        // String-assignable, so the vacuous direction declines → keep (a bare
        // {Number} member alone cannot occur in production — the widening is the
        // closed-world guarantee the predicate's soundness contract rides).
        Assert.assertFalse("the widened {Number} block keeps the site (no proof either direction)",
                        armDead(site,
                                        blockOf(f.lookup(Number.class), f.lookup(Integer.class))));
    }

    /**
     * PIN 9 (crossing merges, the OR shape): the stringValue shape,
     * `if (v instanceof Number || v instanceof String) { v.toString(); } else
     * return null;` — javac compiles the short-circuit OR as two chained
     * single-instanceof IfNodes whose true arms MERGE before the merged region's
     * usage (the anchors sit past the merge). A reachability walk that dies
     * at EndNodes (plain {@code successors()} — an EndNode has no declared
     * successor edges) would make blocking either arm of either guard spuriously
     * report the anchors unreachable and put both guards in both lists —
     * the never consumption would then wrongly skip the live-arm usage (e.g.
     * luindex stringValue@24 / calcUTF16toUTF8Length@94/@19). With
     * {@code cfgSuccessors()} (the walk crosses EndNode→merge), the true-arm path through the merge
     * keeps the anchors reachable when either guard's decided arm is blocked:
     * both guards produce no list entries and the live-arm usage is kept.
     */
    @Test
    public void orShortCircuitMergeKeepsLiveArmUsage() throws Exception {
        UniverseFixture f = new UniverseFixture();
        AnalysisMethod method = f.universe.lookup(
                        (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                                        Holder.class.getDeclaredMethod("orShapeMethod", Object.class)));
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug)
                        .name("OrShapeArmFeasibility").method(method).build();
        StartNode start = graph.add(new StartNode());
        graph.setStart(start);
        Stamp objectStamp = StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(
                        (ResolvedJavaType) f.metaAccess.lookupJavaType(Object.class)));
        ParameterNode param = graph.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(objectStamp)));
        InstanceOfNode ion1 = (InstanceOfNode) graph.addOrUnique(InstanceOfNode.create(
                        TypeReference.createWithoutAssumptions(
                                        (ResolvedJavaType) f.metaAccess.lookupJavaType(Number.class)), param));
        InstanceOfNode ion2 = (InstanceOfNode) graph.addOrUnique(InstanceOfNode.create(
                        TypeReference.createWithoutAssumptions(
                                        (ResolvedJavaType) f.metaAccess.lookupJavaType(String.class)), param));
        // Structure: If1(ion1: true -> e1End, false -> b2); b2 -> If2(ion2:
        // true -> e2End, false -> else); merge(e1End, e2End) -> usage; else -> null.
        EndNode e1 = graph.add(new EndNode());
        BeginNode b2 = graph.add(new BeginNode());
        IfNode if1 = graph.add(new IfNode(ion1, e1Begin(graph, e1), b2, null));
        EndNode e2 = graph.add(new EndNode());
        BeginNode elseB = graph.add(new BeginNode());
        IfNode if2 = graph.add(new IfNode(ion2, e2Begin(graph, e2), elseB, null));
        b2.setNext(if2);
        MergeNode merge = graph.add(new MergeNode());
        merge.addForwardEnd(e1);
        merge.addForwardEnd(e2);
        ReturnNode retToString = graph.addWithoutUnique(new ReturnNode(param)); // the merged-region usage anchor
        merge.setNext(retToString);
        ReturnNode retNull = graph.addWithoutUnique(new ReturnNode(null));
        elseB.setNext(retNull);
        start.setNext(if1);

        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LfgWalk.collectGuardsInto(lfg, graph, f.resolver());
        List<LocalFlowGraph.TypeGuard> guards = lfg.guardsForValue(param);
        Assert.assertEquals("both OR guards are collected on the tested value", 2, guards.size());
        List<Node> anchors = LocalFlowGraph.fixedAnchorsOfRoot(retToString);
        List<LocalFlowGraph.TypeGuard> vacuous = new java.util.ArrayList<>(2);
        List<LocalFlowGraph.TypeGuard> never = new java.util.ArrayList<>(2);
        LfgWalk.guardListsFor(start, anchors, guards, vacuous, never);
        Assert.assertEquals("NO guard proves the merged-region usage dead (the OR shape keeps both arms)",
                        0, vacuous.size() + never.size());
    }

    private static BeginNode e1Begin(StructuredGraph graph, EndNode e1) {
        BeginNode b = graph.add(new BeginNode());
        b.setNext(e1);
        return b;
    }

    private static BeginNode e2Begin(StructuredGraph graph, EndNode e2) {
        BeginNode b = graph.add(new BeginNode());
        b.setNext(e2);
        return b;
    }
}