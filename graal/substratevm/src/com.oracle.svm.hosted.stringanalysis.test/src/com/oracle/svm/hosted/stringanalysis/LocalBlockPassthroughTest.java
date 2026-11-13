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
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import com.oracle.svm.hosted.stringanalysis.ForwardFixpoint.Block;

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
 * The passthrough branch of {@link ForwardFixpoint#localBlock}, which reads the creator pointer
 * {@code LocalVertex.from} (not the in-edge list).
 * <ul>
 * <li>A passthrough-of-passthrough chain over a seed carries the seed's block (not the passthroughs' own declared
 * widening); a creator-less passthrough falls back to its own identity; a ⊤ creator gives ⊤.</li>
 * <li>A creator block of more than 64 members gives ⊤ even under a {@code fwd.blockcap} above 64 (the in-edge
 * union cap), via {@link ForwardFixpoint#passthroughBlock}, the helper the passthrough branch calls.</li>
 * </ul>
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.options", "jdk.graal.compiler/jdk.graal.compiler.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf", "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.internal.vm.ci/jdk.vm.ci.common", "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class LocalBlockPassthroughTest {

    /** The minimal JVMCI-backed analysis universe (the StringAtomEndToEndTest shape). */
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
            HostVM host = new HostVM(new OptionValues(EconomicMap.create()), LocalBlockPassthroughTest.class.getClassLoader()) {
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

    /** 65+ distinct plain JDK types: the members of a wide block. */
    private static final List<Class<?>> WIDE = List.of(Integer.class, Long.class, Short.class, Byte.class, Character.class, Boolean.class,
                    Float.class, Double.class, Number.class, Math.class, StringBuilder.class, StringBuffer.class, Thread.class, Runnable.class,
                    Throwable.class, Exception.class, RuntimeException.class, Error.class, Void.class, Iterable.class, AutoCloseable.class,
                    Comparable.class, CharSequence.class, Appendable.class, Readable.class, IllegalArgumentException.class,
                    IllegalStateException.class, NullPointerException.class, ArithmeticException.class, ClassCastException.class,
                    IndexOutOfBoundsException.class, UnsupportedOperationException.class, java.util.ArrayList.class, java.util.LinkedList.class,
                    java.util.HashMap.class, java.util.TreeMap.class, java.util.HashSet.class, java.util.TreeSet.class, java.util.LinkedHashMap.class,
                    java.util.LinkedHashSet.class, java.util.ArrayDeque.class, java.util.PriorityQueue.class, java.util.Vector.class,
                    java.util.Stack.class, java.util.Hashtable.class, java.util.Optional.class, java.util.Objects.class, java.util.Arrays.class,
                    java.util.Collections.class, java.util.Random.class, java.util.StringJoiner.class, java.util.UUID.class, java.util.BitSet.class,
                    java.util.Locale.class, java.util.Date.class, java.util.EnumMap.class, java.util.IdentityHashMap.class, java.util.WeakHashMap.class,
                    java.util.List.class, java.util.Map.class, java.util.Set.class, java.util.Collection.class, java.util.Iterator.class,
                    java.util.Deque.class, java.util.Queue.class, java.util.Comparator.class, java.util.AbstractList.class, java.util.AbstractMap.class);

    private static Set<AnalysisType> wide(Universe u, int n) {
        Set<AnalysisType> out = new LinkedHashSet<>();
        for (Class<?> c : WIDE) {
            if (out.size() == n) {
                break;
            }
            out.add(u.type(c));
        }
        Assert.assertEquals("fixture: distinct types", n, out.size());
        return out;
    }

    private static LocalFlowGraph.LocalVertex internal(LocalFlowGraph g, String label, AnalysisType declared, LocalFlowGraph.LocalVertex from) {
        LocalFlowGraph.LocalVertex v = g.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        v.label = label;
        v.declaredType = declared;
        v.from = from;
        return v;
    }

    /** The {@code from}-based block: a passthrough chain carries its creator's block; ⊤ propagates; no creator = own. */
    @Test
    public void passthroughChainCarriesTheCreatorBlock() {
        Universe u = new Universe();
        AnalysisType string = u.type(String.class);
        AnalysisType object = u.type(Object.class);
        LocalFlowGraph g = new LocalFlowGraph(null);
        ForwardFixpoint ff = new ForwardFixpoint(new StringUtilizationGraph(), Map.of(), Map.of(), null, null);

        LocalFlowGraph.LocalVertex seed = internal(g, "string-constant", string, null);
        // The passthroughs declare Object: their own widening would be {Object}; the creator chain must win.
        LocalFlowGraph.LocalVertex p1 = internal(g, "pi", object, seed);
        LocalFlowGraph.LocalVertex p2 = internal(g, "phi", object, p1);
        Block seedBlock = ff.localBlock(null, seed, new HashSet<>());
        Assert.assertEquals(Set.of(string), seedBlock.types);
        Assert.assertSame(seedBlock, ff.localBlock(null, p1, new HashSet<>()));
        Assert.assertSame(seedBlock, ff.localBlock(null, p2, new HashSet<>()));

        // No creator: the passthrough's own identity, widened.
        LocalFlowGraph.LocalVertex own = internal(g, "pi", object, null);
        Assert.assertEquals(Set.of(object), ff.localBlock(null, own, new HashSet<>()).types);

        // A ⊤ creator (no identity at all) gives ⊤ down the chain, whatever the passthrough declares.
        LocalFlowGraph.LocalVertex unknown = internal(g, "pi", null, null);
        LocalFlowGraph.LocalVertex p3 = internal(g, "pi", string, unknown);
        LocalFlowGraph.LocalVertex p4 = internal(g, "phi", string, p3);
        Assert.assertTrue(ff.localBlock(null, unknown, new HashSet<>()).isTop());
        Assert.assertTrue(ff.localBlock(null, p4, new HashSet<>()).isTop());
    }

    /**
     * The in-edge union cap. Under a {@code fwd.blockcap} above 64 (here 100), a 64-member creator block passes
     * through finite, and a 65-member one is ⊤. Without the cap the 65-member block would pass through finite (the ADMIT
     * direction: receiver filtering and arm-dead proofs on a block that must be unknown).
     */
    @Test
    public void passthroughOfMoreThan64MembersIsTopAboveTheDefaultBlockcap() {
        Universe u = new Universe();
        int cap = 100;
        Block src64 = Block.of(wide(u, 64), cap);
        Block src65 = Block.of(wide(u, 65), cap);
        Assert.assertFalse("fixture: a 65-member block is finite under blockcap 100", src65.isTop());
        Assert.assertSame(src64, ForwardFixpoint.passthroughBlock(src64, cap));
        Assert.assertTrue("65 members > HEAD's 64-member union cap", ForwardFixpoint.passthroughBlock(src65, cap).isTop());
        Assert.assertTrue(ForwardFixpoint.passthroughBlock(Block.TOP, cap).isTop());
        // At the default blockcap (32) the member cap already makes both ⊤: the 64-cap is unreachable there.
        if (Block.BLOCK_MEMBER_CAP <= 64) {
            Assert.assertTrue(ForwardFixpoint.passthroughBlock(src64, Block.BLOCK_MEMBER_CAP).isTop());
        }
    }
}
