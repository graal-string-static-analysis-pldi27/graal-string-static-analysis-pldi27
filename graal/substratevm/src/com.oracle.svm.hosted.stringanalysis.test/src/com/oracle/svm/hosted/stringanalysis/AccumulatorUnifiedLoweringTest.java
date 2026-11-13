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

import java.io.StringWriter;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FixedGuardNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ReturnNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.LoadHubNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.phases.util.Providers;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Unified accumulator lowering: every accumulator {@code toString} extraction, whatever its declared owner, is lowered
 * on the profile entry's exact class alone, behind the zero-cost exact filter, to {@code StringView.create(<class>)};
 * no run-time class check is left.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases.tiers",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.util",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common",
                "jdk.graal.compiler/jdk.graal.compiler.phases.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.graal.compiler/jdk.graal.compiler.api.replacements",
                "jdk.graal.compiler/jdk.graal.compiler.core.common",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.spi"})
public class AccumulatorUnifiedLoweringTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    private static Class<?> asb() throws ClassNotFoundException {
        return Class.forName("java.lang.AbstractStringBuilder");
    }

    /** The declared owners an extraction can name, and the accumulator classes each can hold. */
    private static Class<?>[] owners() throws ClassNotFoundException {
        return new Class<?>[]{StringBuilder.class, StringBuffer.class, StringWriter.class, asb(), CharSequence.class, Appendable.class, Writer.class, Object.class};
    }

    @Test
    public void everyDeclaredOwnerSelectsTheProfileClass() throws ClassNotFoundException {
        for (Class<?> owner : owners()) {
            for (Class<?> acc : StringRepresentationReplacementPlugin.ACCUMULATOR_CLASSES) {
                Class<?> got = StringRepresentationReplacementPlugin.accumulatorFactoryClass(acc.getName(), owner::isAssignableFrom);
                Assert.assertEquals(owner + " / " + acc, owner.isAssignableFrom(acc) ? acc : null, got);
            }
            // no class in the entry, or a class that is no accumulator: never lowered
            Assert.assertNull(StringRepresentationReplacementPlugin.accumulatorFactoryClass(null, owner::isAssignableFrom));
            Assert.assertNull(StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.lang.String", owner::isAssignableFrom));
        }
        // the owner/class pairs real extraction sites name
        Assert.assertSame(StringBuilder.class, StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.lang.StringBuilder", Object.class::isAssignableFrom));
        Assert.assertSame(StringBuilder.class, StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.lang.StringBuilder", CharSequence.class::isAssignableFrom));
        Assert.assertSame(StringBuffer.class, StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.lang.StringBuffer", asb()::isAssignableFrom));
        Assert.assertSame(StringWriter.class, StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.io.StringWriter", Writer.class::isAssignableFrom));
        Assert.assertNull(StringRepresentationReplacementPlugin.accumulatorFactoryClass("java.io.StringWriter", CharSequence.class::isAssignableFrom));
    }

    /** Each accumulator class has its snapshot factory {@code StringView.create(<class>)}, and it is the original's content. */
    @Test
    public void everyAccumulatorClassHasItsSnapshotFactory() throws ReflectiveOperationException {
        for (Class<?> acc : StringRepresentationReplacementPlugin.ACCUMULATOR_CLASSES) {
            Assert.assertSame(acc.getName(), String.class, StringView.class.getDeclaredMethod("create", acc).getReturnType()); // a view or the compact copy
        }
        StringWriter w = new StringWriter(4); // sized so the view shares (under half full is the exact-String copy)
        w.write("abĀ");
        w.append('c');
        StringView v = (StringView) StringView.create(w);
        RepEq.assertRepEquals(w.toString(), v.toString());
        Assert.assertEquals(4, v.length());
        Assert.assertEquals('Ā', v.charAt(2));
    }

    @Test
    public void theExactClassIsOneClassOrNone() {
        Assert.assertEquals("java.lang.StringBuilder", AccumulatorHeuristic.exactClassOf(List.of("java.lang.StringBuilder")));
        Assert.assertEquals("java.lang.StringBuilder", AccumulatorHeuristic.exactClassOf(List.of("java.lang.StringBuilder", "java.lang.StringBuilder")));
        Assert.assertNull(AccumulatorHeuristic.exactClassOf(List.of("java.lang.StringBuilder", "java.lang.StringBuffer")));
        Assert.assertNull(AccumulatorHeuristic.exactClassOf(List.of()));
        Assert.assertNull(AccumulatorHeuristic.exactClassOf(Arrays.asList("java.io.StringWriter", null)));
    }

    /** The child writes the class as the fourth token; the parent's loader reads it back; no other type takes four. */
    @Test
    public void theProfileCarriesTheExactClass() throws Exception {
        Path tmp = Files.createTempFile("acc_unified", ".txt");
        try {
            StringUtilizationGraph graph = new StringUtilizationGraph();
            SugVertex x = graph.newVertex();
            x.setSourceLocation("W#bench()Ljava/lang/String;@14");
            SugVertex y = graph.newVertex();
            y.setSourceLocation("B#run()V@3");
            List<InstrumentationDecision> ds = new ArrayList<>();
            ds.add(new InstrumentationDecision(x, OptimizationType.STRING_VIEW, "ACCUMULATOR_VIEW", "java.io.StringWriter"));
            ds.add(new InstrumentationDecision(y, OptimizationType.STRING_VIEW, null));
            StringAnalysisFeature.dumpProfile(ds, tmp.toString());
            List<String> lines = Files.readAllLines(tmp);
            Assert.assertTrue(lines.toString(), lines.contains("W#bench()Ljava/lang/String;@14 STRING_VIEW ACCUMULATOR_VIEW java.io.StringWriter"));
            RepresentationProfile p = RepresentationProfileLoader.load(tmp.toString());
            ProfileEntry e = p.getEntry("W#bench()Ljava/lang/String;@14", OptimizationType.STRING_VIEW);
            Assert.assertEquals("ACCUMULATOR_VIEW", e.getVariant());
            Assert.assertEquals("java.io.StringWriter", e.getAccumulatorClass());
            Assert.assertNull(p.getEntry("B#run()V@3", OptimizationType.STRING_VIEW).getAccumulatorClass());
            Files.write(tmp, List.of("B#run()V@3 LAZY_CONCAT ROPE java.lang.StringBuilder"));
            try {
                RepresentationProfileLoader.load(tmp.toString());
                Assert.fail("a four-token line other than STRING_VIEW ACCUMULATOR_VIEW must be refused");
            } catch (IllegalArgumentException expected) {
                // refused
            }
        } finally {
            Files.deleteIfExists(tmp);
        }
    }

    @SuppressWarnings("unused")
    static Object holder(Object x) {
        return x;
    }

    /** Appends fixed nodes in sequence after the start (the parse position), floating nodes uniquely. */
    private static final class Seq implements InlineCacheTrivialMethodNodePlugin.NodeAdder {
        final StructuredGraph g;
        FixedWithNextNode last;

        Seq(StructuredGraph g) {
            this.g = g;
            this.last = g.start();
        }

        @Override
        public <T extends Node> T add(T node) {
            if (node instanceof FixedWithNextNode) {
                T added = g.add(node);
                last.setNext((FixedWithNextNode) added);
                last = (FixedWithNextNode) added;
                return added;
            }
            return g.addOrUniqueWithInputs(node);
        }
    }

    private static Providers providers() {
        var backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
        return new Providers(META, backend.getCodeCache(), backend.getConstantReflection(), null, null, null, null, null, null, null, null, null, null, null);
    }

    private static long count(StructuredGraph g, Class<? extends Node> c) {
        return g.getNodes().filter(c).count();
    }

    /**
     * Per declared owner (the receiver's stamp) and accumulator class: the lowering's filter is emitted (a marked guard
     * + Pi of the exact class) unless the stamp already proves the class, and after the strengthen sequence (the
     * {@code SubstrateStrengthenGraphs.simplifyDelegate} hook) no guard, no instanceof, no hub load and no object compare
     * is left: the returned value is typed exactly the accumulator class with no run-time check.
     */
    @Test
    public void theFilterIsEmittedAndRemovedForEveryDeclaredOwner() throws Exception {
        Assert.assertEquals("default mode", 1, InlineCacheTrivialMethodNodePlugin.EXACT_PI_MODE);
        int emittedShapes = 0;
        for (Class<?> owner : owners()) {
            for (Class<?> acc : StringRepresentationReplacementPlugin.ACCUMULATOR_CLASSES) {
                if (!owner.isAssignableFrom(acc)) {
                    continue;
                }
                InlineCacheTrivialMethodNodePlugin.resetCensus();
                DebugContext debug = new DebugContext.Builder(OPTIONS).build();
                StructuredGraph g = new StructuredGraph.Builder(OPTIONS, debug).method(META.lookupJavaMethod(AccumulatorUnifiedLoweringTest.class.getDeclaredMethod("holder", Object.class))).build();
                ResolvedJavaType ownerType = META.lookupJavaType(owner);
                ResolvedJavaType accType = META.lookupJavaType(acc);
                ParameterNode p = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.object(TypeReference.createTrustedWithoutAssumptions(ownerType)))));
                Seq seq = new Seq(g);
                ValueNode narrowed = InlineCacheTrivialMethodNodePlugin.trustedExactFilter(g, seq, p, accType);
                String shape = owner.getName() + " / " + acc.getName();
                Assert.assertNotNull(shape, narrowed);
                boolean stampProves = owner == acc && java.lang.reflect.Modifier.isFinal(acc.getModifiers());
                if (stampProves) {
                    Assert.assertSame(shape + ": nothing to state", p, narrowed);
                    Assert.assertEquals(shape, 0, count(g, FixedGuardNode.class));
                } else {
                    emittedShapes++;
                    Assert.assertTrue(shape, narrowed instanceof PiNode);
                    Assert.assertEquals(shape, 1, count(g, FixedGuardNode.class));
                    FixedGuardNode guard = g.getNodes().filter(FixedGuardNode.class).first();
                    Assert.assertTrue(shape + ": marked", InlineCacheTrivialMethodNodePlugin.isTrustedFilter(guard));
                    Assert.assertTrue(shape, guard.condition() instanceof InstanceOfNode io && io.type().isExact() && io.type().getType().equals(accType) && io.allowsNull());
                    Assert.assertEquals(shape, 1, InlineCacheTrivialMethodNodePlugin.EMITTED_ACC.get());
                }
                Assert.assertTrue(shape + ": points-to sees exactly the class", narrowed.stamp(
                                jdk.graal.compiler.nodes.NodeView.DEFAULT) instanceof jdk.graal.compiler.core.common.type.ObjectStamp os &&
                                os.type().equals(accType) && (os.isExactType() || java.lang.reflect.Modifier.isFinal(acc.getModifiers())));
                seq.last.setNext(g.add(new ReturnNode(narrowed)));
                InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, true);
                CanonicalizerPhase.create().copyWithCustomSimplification((Node n, jdk.graal.compiler.nodes.spi.SimplifierTool tool) -> {
                    if (n instanceof FixedGuardNode guard && InlineCacheTrivialMethodNodePlugin.isTrustedFilter(guard)) {
                        InlineCacheTrivialMethodNodePlugin.strengthenTrustedFilter(guard, tool);
                    }
                }).apply(g, providers());
                InlineCacheTrivialMethodNodePlugin.countTrustedFilters(g, false);
                Assert.assertEquals(shape, 0, count(g, FixedGuardNode.class));
                Assert.assertEquals(shape, 0, count(g, InstanceOfNode.class));
                Assert.assertEquals(shape, 0, count(g, LoadHubNode.class));
                Assert.assertEquals(shape, 0, count(g, ObjectEqualsNode.class));
                Assert.assertEquals(shape, 0, InlineCacheTrivialMethodNodePlugin.SURVIVING.get());
                String summary = InlineCacheTrivialMethodNodePlugin.trustedFilterSummary();
                Assert.assertTrue(summary, summary.endsWith("attributed=ok"));
            }
        }
        // every wider owner (and the non-final StringWriter) needs the filter: Object x3, CharSequence x2, Appendable x3,
        // AbstractStringBuilder x2, Writer x1, StringWriter x1
        Assert.assertEquals(12, emittedShapes);
    }
}
