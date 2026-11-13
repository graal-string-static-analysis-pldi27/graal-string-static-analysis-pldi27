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

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The must-not-stop half of {@link RecursiveTracking#typedStopType}, typedrecv's type-only sink stop.
 * The stop is soundness-critical in both directions: a stamp that bounds its run-time class (a final class, or
 * {@code String} whose analysed cone in the child is {String}) may stop the sink, but an interface, abstract, array or
 * non-final stamp must not stop (its cone is open: stopping there would silently widen every typed sink into the whole
 * CHA fan and bypass the refusals behind the un-walked part), and an alwaysNull or primitive stamp yields no stop. This
 * pins the predicate on real {@link AnalysisType}s over real stamps (the same minimal-universe fixture as
 * {@code LocalBlockPassthroughTest}); the knob's default is pinned by {@code SinkAndExceptionFlowRulesTest}.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta", "jdk.internal.vm.ci/jdk.vm.ci.common",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.options", "jdk.graal.compiler/jdk.graal.compiler.java",
                "jdk.graal.compiler/jdk.graal.compiler.phases", "jdk.graal.compiler/jdk.graal.compiler.nodeinfo",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class TypedStopPremiseTest {

    /** The minimal JVMCI-backed analysis universe (the LocalBlockPassthroughTest shape). */
    private static final class Universe {
        final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        final AnalysisUniverse universe;

        Universe() {
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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), TypedStopPremiseTest.class.getClassLoader()) {
                @Override
                public void onTypeReachable(com.oracle.graal.pointsto.BigBang bb, AnalysisType type) {
                    // no-op
                }

                @Override
                public boolean isInitialized(AnalysisType type) {
                    return true;
                }

                @Override
                public jdk.graal.compiler.java.GraphBuilderPhase.Instance createGraphBuilderPhase(com.oracle.graal.pointsto.meta.HostedProviders providers,
                                jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration config,
                                jdk.graal.compiler.phases.OptimisticOptimizations optimizations,
                                jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext intrinsicContext) {
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
        }

        AnalysisType type(Class<?> c) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(c));
        }
    }

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("TypedStopPremiseTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    /** A node whose stamp is exactly {@code type} (non-null object stamp of that type). */
    private static ParameterNode nodeOf(StructuredGraph g, AnalysisType type) {
        return g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(type)))));
    }

    @Test
    public void boundingStampsStopAndReturnTheirType() {
        Universe u = new Universe();
        StructuredGraph g = graph();
        AnalysisType integer = u.type(Integer.class); // final in the builder JDK
        AnalysisType string = u.type(String.class);  // not final there (the reps subclass it); the name clause stops
        Assert.assertTrue("fixture: Integer is final", integer.isFinalFlagSet());
        Assert.assertFalse("fixture: String is de-finalized in the builder JDK (the reps subclass it)", string.isFinalFlagSet());
        Assert.assertSame("a final class stops and yields its type", integer, RecursiveTracking.typedStopType(nodeOf(g, integer)));
        Assert.assertSame("String counts as final (its child cone is {String}, step K)", string, RecursiveTracking.typedStopType(nodeOf(g, string)));
    }

    @Test
    public void openConesDoNotStop() {
        Universe u = new Universe();
        StructuredGraph g = graph();
        Assert.assertNull("an interface stamp continues (the fan behind it is open)", RecursiveTracking.typedStopType(nodeOf(g, u.type(Runnable.class))));
        Assert.assertNull("a second interface", RecursiveTracking.typedStopType(nodeOf(g, u.type(CharSequence.class))));
        Assert.assertNull("an abstract class stamp continues", RecursiveTracking.typedStopType(nodeOf(g, u.type(Number.class))));
        Assert.assertNull("a second abstract class", RecursiveTracking.typedStopType(nodeOf(g, u.type(java.util.AbstractList.class))));
        Assert.assertNull("a non-final concrete class continues", RecursiveTracking.typedStopType(nodeOf(g, u.type(java.util.ArrayList.class))));
        Assert.assertNull("java.lang.Object continues (its cone is everything)", RecursiveTracking.typedStopType(nodeOf(g, u.type(Object.class))));
        Assert.assertNull("an array stamp continues", RecursiveTracking.typedStopType(nodeOf(g, u.type(String[].class))));
        Assert.assertNull("a primitive-array stamp continues", RecursiveTracking.typedStopType(nodeOf(g, u.type(int[].class))));
    }

    @Test
    public void nullAndPrimitiveStampsDoNotStop() {
        StructuredGraph g = graph();
        ParameterNode alwaysNull = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.alwaysNull())));
        Assert.assertNull("an alwaysNull stamp names no type (a null receiver NPEs before any usage)", RecursiveTracking.typedStopType(alwaysNull));
        Assert.assertNull("a primitive stamp names no type", RecursiveTracking.typedStopType(jdk.graal.compiler.nodes.ConstantNode.forInt(7)));
        Assert.assertNull("a null node is not a stop", RecursiveTracking.typedStopType(null));
    }
}
