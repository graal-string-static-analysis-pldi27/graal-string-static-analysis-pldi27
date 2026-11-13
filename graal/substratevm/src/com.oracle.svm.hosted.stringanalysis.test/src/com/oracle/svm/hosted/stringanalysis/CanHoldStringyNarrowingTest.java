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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.api.HostVM;
import com.oracle.graal.pointsto.infrastructure.SubstitutionProcessor;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisFactory;
import com.oracle.graal.pointsto.typestate.DefaultAnalysisPolicy;

import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.runtime.JVMCIBackend;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.impl.AnnotationExtractor;

/**
 * The {@code canHoldStringy} closed-world narrowing: a value of declared type {@code t} can be stringy iff some stringy
 * type is a subtype of {@code t} in the closed world (holder set = stringy ∪ supertypes(stringy); no interface or
 * non-final modifier fallback). Both directions are pinned: the holders that must survive ({@code String},
 * {@code StringBuilder}, a rep subtype, {@code CharSequence}, {@code Comparable}, {@code Appendable}, {@code Object},
 * null) and the fake holders that must disappear ({@code Function}, a named non-final class with no stringy subtype, an
 * anonymous class).
 *
 * <p>The holder set is computed once per universe at the first {@code canHoldStringy} call, so every type asserted on
 * is looked up during fixture construction, before the first assertion.</p>
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class CanHoldStringyNarrowingTest {

    /** A named non-final class with NO stringy subtype — a non-final modifier fallback would hold it. */
    @SuppressWarnings("unused")
    private static class PlainCarrier {
        @Override
        public String toString() {
            return "plain";
        }
    }

    /** A final non-stringy leaf — a non-holder under the closed-world predicate and the modifier fallbacks alike. */
    @SuppressWarnings("unused")
    private static final class FinalLeaf {
    }

    /** The minimal JVMCI-backed universe. */
    private static final class UniverseFixture {
        final MetaAccessProvider metaAccess;
        final AnalysisUniverse universe;

        UniverseFixture(Class<?>... lookups) {
            JVMCIBackend backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
            this.metaAccess = backend.getMetaAccess();
            AnnotationExtractor annotations = new AnnotationExtractor() {
                @Override
                public boolean hasAnnotation(AnnotatedElement element, Class<? extends Annotation> annotationType) {
                    return element.isAnnotationPresent(annotationType);
                }

                @Override
                @SuppressWarnings("unchecked")
                public <T extends Annotation> T extractAnnotation(AnnotatedElement element, Class<T> annotationType, boolean declaredOnly) {
                    return declaredOnly ? element.getDeclaredAnnotation(annotationType) : element.getAnnotation(annotationType);
                }

                @Override
                @SuppressWarnings("unchecked")
                public Class<? extends Annotation>[] getAnnotationTypes(AnnotatedElement element) {
                    return Arrays.stream(element.getAnnotations()).map(Annotation::annotationType).toArray(Class[]::new);
                }
            };
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), UniverseFixture.class.getClassLoader()) {
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
                                jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration config, jdk.graal.compiler.phases.OptimisticOptimizations optimizations,
                                jdk.graal.compiler.nodes.graphbuilderconf.IntrinsicContext intrinsicContext) {
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
            // Universe bootstrap discipline: Object first, Cloneable before any instance class.
            lookup(Object.class);
            lookup(Cloneable.class);
            lookup(String.class);
            for (Class<?> cls : lookups) {
                lookup(cls);
            }
        }

        AnalysisType lookup(Class<?> clazz) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(clazz));
        }

        AnalysisType lookupArray(Class<?> arrayClass) {
            return universe.lookup((ResolvedJavaType) metaAccess.lookupJavaType(arrayClass));
        }
    }

    private static void assertHolder(AnalysisType t, boolean expected, String what) {
        Assert.assertEquals(what + " (declared " + (t != null ? t.toJavaName(true) : "null") + ")",
                        expected, SugNameTables.canHoldStringy(t));
    }

    /** null (unknown declared type) conservatively holds. */
    @Test
    public void nullTypeHolds() {
        assertHolder(null, true, "null declared type");
    }

    /**
     * The base members and their supertypes stay holders: String, StringBuilder, CharSequence, Comparable, Appendable,
     * Object, Writer (StringWriter's superclass; StringWriter is a base member).
     */
    @Test
    public void baseMembersAndSupertypesHold() {
        UniverseFixture u = new UniverseFixture(StringBuilder.class, java.io.StringWriter.class,
                        CharSequence.class, Comparable.class, Appendable.class, java.io.Writer.class);
        assertHolder(u.lookup(String.class), true, "java.lang.String (base member)");
        assertHolder(u.lookup(StringBuilder.class), true, "java.lang.StringBuilder (base member)");
        assertHolder(u.lookup(java.io.StringWriter.class), true, "java.io.StringWriter (base member)");
        assertHolder(u.lookup(CharSequence.class), true, "java.lang.CharSequence (supertype of String)");
        assertHolder(u.lookup(Comparable.class), true, "java.lang.Comparable (supertype of String)");
        assertHolder(u.lookup(Appendable.class), true, "java.lang.Appendable (supertype of StringBuilder)");
        assertHolder(u.lookup(Object.class), true, "java.lang.Object (supertype of every stringy type)");
        assertHolder(u.lookup(java.io.Writer.class), true, "java.io.Writer (supertype of StringWriter)");
    }

    /**
     * A rep subtype is a holder: StringView extends the de-finalized builder-JDK String, so it is a stringy runtime type,
     * and its own supertype chain is marked.
     */
    @Test
    public void repSubtypeHolds() throws ClassNotFoundException {
        Class<?> stringView = Class.forName("com.oracle.svm.core.stringrep.StringView", false,
                        CanHoldStringyNarrowingTest.class.getClassLoader());
        UniverseFixture u = new UniverseFixture(stringView);
        assertHolder(u.lookup(stringView), true, "com.oracle.svm.core.stringrep.StringView (rep subtype)");
    }

    /**
     * An interface not on any stringy chain is not a holder: no stringy type is a subtype of
     * {@code java.util.function.Function} in the closed world (a modifier fallback would answer true for it).
     */
    @Test
    public void interfaceNotOnStringyChainNotHolder() {
        UniverseFixture u = new UniverseFixture(java.util.function.Function.class);
        assertHolder(u.lookup(java.util.function.Function.class), false,
                        "java.util.function.Function (interface, no stringy subtype)");
    }

    /**
     * A named non-final class with no stringy subtype is not a holder: finality is irrelevant in the closed world, only
     * whether some stringy type is below it (a non-final modifier fallback would answer true).
     */
    @Test
    public void plainNonFinalClassNotHolder() {
        UniverseFixture u = new UniverseFixture(PlainCarrier.class);
        assertHolder(u.lookup(PlainCarrier.class), false,
                        "PlainCarrier (non-final, no stringy subtype)");
    }

    /**
     * An anonymous class (the javac {@code $1} shape) is not a holder: it extends Object and has no stringy subtype
     * (anonymous classes carry no ACC_FINAL, so a non-final modifier fallback would answer true).
     */
    @Test
    public void anonymousClassNotHolder() {
        Class<?> anon = (new Object() {
        }).getClass();
        UniverseFixture u = new UniverseFixture(anon);
        assertHolder(u.lookup(anon), false, "the anonymous Object subclass (" + anon.getName() + ")");
    }

    /**
     * A final non-stringy class and array types are non-holders (an array is a container keyed by its component type,
     * never a stringy value).
     */
    @Test
    public void finalLeafAndArraysNotHolders() {
        UniverseFixture u = new UniverseFixture(FinalLeaf.class);
        assertHolder(u.lookup(FinalLeaf.class), false, "FinalLeaf (final, no stringy subtype)");
        assertHolder(u.lookupArray(String[].class), false, "String[] (array — component-keyed container)");
        assertHolder(u.lookupArray(Object[].class), false, "Object[] (array — component-keyed container)");
    }
}
