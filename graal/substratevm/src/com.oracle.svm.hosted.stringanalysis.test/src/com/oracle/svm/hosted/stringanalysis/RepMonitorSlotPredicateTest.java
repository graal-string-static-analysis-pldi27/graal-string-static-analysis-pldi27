/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it under the terms of the GNU
 * General Public License version 2 only, as published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
 * even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version 2 along with this
 * work; if not, write to the Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
 * Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA or visit
 * www.oracle.com if you need additional information or have any questions.
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
import com.oracle.svm.hosted.HostedConfiguration;

import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * {@link HostedConfiguration#isProperStringSubclass}, the predicate that keeps the proper subclasses
 * of {@code String} (the reps) free of an inline monitor field, like {@code String} itself
 * ({@code HostedConfiguration.maybeSetMonitorField}). The minimal-universe fixture is the one of
 * {@code TypedStopPremiseTest}.
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
public class RepMonitorSlotPredicateTest {

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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), RepMonitorSlotPredicateTest.class.getClassLoader()) {
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

    @Test
    public void repsAreProperStringSubclasses() throws ClassNotFoundException {
        Universe u = new Universe();
        for (String rep : new String[]{"StringView", "RopeString", "ThreeWayString", "FixedConcat4", "ArrayLazyString", "InterleavedStringArray",
                        "SingleByteString", "TrivialString"}) {
            AnalysisType t = u.type(Class.forName("com.oracle.svm.core.stringrep." + rep));
            Assert.assertTrue(rep + " is a proper String subclass", HostedConfiguration.isProperStringSubclass(t));
        }
    }

    @Test
    public void stringItselfAndNonStringTypesAreNot() {
        Universe u = new Universe();
        for (Class<?> c : new Class<?>[]{String.class, Object.class, Integer.class, StringBuilder.class, CharSequence.class, String[].class, Object[].class}) {
            Assert.assertFalse(c.getName() + " is not a proper String subclass", HostedConfiguration.isProperStringSubclass(u.type(c)));
        }
    }
}
