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

import org.graalvm.collections.EconomicMap;
import org.graalvm.word.LocationIdentity;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndAddNode;
import jdk.graal.compiler.nodes.memory.address.OffsetAddressNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.word.WordCastNode;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Pins: the container walk's final fallback names a raw-memory use {@code UNSAFE_ACCESS} (the raw-access name of both
 * atom kinds) and any other use {@code UNCLASSIFIED_ACCESS}; {@code AtomicReadAndAdd} counts in the base role only.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                // the superclasses/interfaces of the SVM raw-memory classes isRawMemoryClass loads (as RawMemoryUseTest)
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.nodes.debug"})
public class UnsafeBaseRoleTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("UnsafeBaseRoleTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    private ParameterNode objectParam(StructuredGraph graph, int index) {
        ResolvedJavaType object = (ResolvedJavaType) metaAccess.lookupJavaType(Object.class);
        return graph.addWithoutUnique(new ParameterNode(index, StampPair.createSingle(
                        StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(object)))));
    }

    /** A raw-memory use of the walked reference is UNSAFE_ACCESS. */
    @Test
    public void r2UsesAreUnsafeAccess() {
        StructuredGraph graph = graph();
        ParameterNode o = objectParam(graph, 0);
        WordCastNode cast = graph.addWithoutUnique(WordCastNode.objectToUntrackedPointer(o, JavaKind.Long));
        OffsetAddressNode addr = graph.addWithoutUnique(new OffsetAddressNode(o, ConstantNode.forLong(8, graph)));
        Assert.assertEquals(RTrackRefusal.UNSAFE_ACCESS, RecursiveTracking.fallbackRefusal(cast, o));
        Assert.assertEquals(RTrackRefusal.UNSAFE_ACCESS, RecursiveTracking.fallbackRefusal(addr, o));
    }

    /** AtomicReadAndAdd: the base role is a raw-memory use; the numeric delta is not (it keeps the generic name). */
    @Test
    public void atomicReadAndAddBaseRoleOnly() {
        StructuredGraph graph = graph();
        ParameterNode o = objectParam(graph, 0);
        ParameterNode delta = graph.addWithoutUnique(new ParameterNode(1, StampPair.createSingle(StampFactory.forKind(JavaKind.Int))));
        AtomicReadAndAddNode rra = graph.addWithoutUnique(new AtomicReadAndAddNode(o, ConstantNode.forLong(8, graph), delta,
                        JavaKind.Int, LocationIdentity.any()));
        Assert.assertEquals(RTrackRefusal.UNSAFE_ACCESS, RecursiveTracking.fallbackRefusal(rra, o));
        Assert.assertEquals(RTrackRefusal.UNCLASSIFIED_ACCESS, RecursiveTracking.fallbackRefusal(rra, delta));
    }

    /** A use outside the raw-memory set keeps UNCLASSIFIED_ACCESS. */
    @Test
    public void otherUsesStayUnclassified() {
        StructuredGraph graph = graph();
        ParameterNode o = objectParam(graph, 0);
        IsNullNode isNull = graph.addWithoutUnique(new IsNullNode(o));
        ConditionalNode cond = graph.addWithoutUnique(new ConditionalNode(isNull, ConstantNode.forLong(1, graph), ConstantNode.forLong(0, graph)));
        Assert.assertEquals(RTrackRefusal.UNCLASSIFIED_ACCESS, RecursiveTracking.fallbackRefusal(cond, isNull));
        Assert.assertEquals(RTrackRefusal.UNCLASSIFIED_ACCESS, RecursiveTracking.fallbackRefusal(isNull, o));
    }
}
