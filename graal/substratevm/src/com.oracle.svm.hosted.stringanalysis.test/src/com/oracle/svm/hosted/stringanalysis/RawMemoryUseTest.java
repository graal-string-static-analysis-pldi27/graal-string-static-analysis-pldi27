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

import java.util.HashSet;

import org.graalvm.collections.EconomicMap;
import org.graalvm.word.LocationIdentity;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.LocalFlowGraph.LocalVertex;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.core.common.memory.BarrierType;
import jdk.graal.compiler.core.common.memory.MemoryOrderMode;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.calc.IsNullNode;
import jdk.graal.compiler.nodes.extended.JavaReadNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndAddNode;
import jdk.graal.compiler.nodes.memory.address.OffsetAddressNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.graal.compiler.word.WordCastNode;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Walk pins for the raw-memory uses (lowered raw memory / word / address): the LFG walk does not
 * continue through such a use of a walked value (the use is not registered, nothing is walked behind it);
 * {@code AtomicReadAndAdd} only in the base role. The engine's refusal ({@code UNSAFE_ACCESS} on the IR) is
 * pinned by {@code UnsafeBaseRoleTest}. No dedicated refusal vertex is minted.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                // the superclasses/interfaces of the SVM raw-memory classes isRawMemoryClass loads (CInterfaceWrite -> WriteNode, ...)
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.nodes.debug"})
public class RawMemoryUseTest {

    private final SugBuilderV2 builder = new SugBuilderV2(null);
    private final LocalFlowGraph lfg = new LocalFlowGraph(null);
    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("RawMemoryUseTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    private ParameterNode stringParam(StructuredGraph graph, int index) {
        ResolvedJavaType string = (ResolvedJavaType) metaAccess.lookupJavaType(String.class);
        return graph.addWithoutUnique(new ParameterNode(index, StampPair.createSingle(
                        StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(string)))));
    }

    private LocalVertex walkFrom(Node start) {
        LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.label = "seed";
        seed.irNode = start;
        builder.lfgWalk.walkSSAFromParam(lfg, start, seed, null, new HashSet<>());
        return seed;
    }

    /** The walk stops at the raw-memory use: no vertex for it, not registered (so nothing behind it is walked). */
    private void assertRefused(LocalVertex seed, Node use) {
        Assert.assertTrue(LfgWalk.isRawMemoryClass(use));
        Assert.assertNull("the refused use is not registered as the node's vertex (the walk ends there)", lfg.vertexForNode(use));
        Assert.assertEquals("the walk makes no vertex for the refused use", java.util.List.of(seed), lfg.getVertices());
    }

    /** PIN 1: {@code Word.objectToUntrackedPointer(s)} — the reference becomes an address. */
    @Test
    public void wordCastOfWalkedValueStopsTheWalk() {
        StructuredGraph graph = graph();
        ParameterNode s = stringParam(graph, 0);
        WordCastNode cast = graph.addWithoutUnique(WordCastNode.objectToUntrackedPointer(s, JavaKind.Long));
        assertRefused(walkFrom(s), cast);
    }

    /** PIN 2: the walked value as the base of a raw address (the JavaWrite/JavaRead substrate). */
    @Test
    public void offsetAddressOnWalkedValueStopsTheWalk() {
        StructuredGraph graph = graph();
        ParameterNode s = stringParam(graph, 0);
        OffsetAddressNode addr = graph.addWithoutUnique(new OffsetAddressNode(s, ConstantNode.forLong(8, graph)));
        assertRefused(walkFrom(s), addr);
    }

    /** PIN 3: {@code AtomicReadAndAdd} refuses in the base role only; a numeric delta passes through. */
    @Test
    public void atomicReadAndAddRefusesOnlyTheBaseRole() {
        StructuredGraph graph = graph();
        ParameterNode s = stringParam(graph, 0);
        ParameterNode delta = graph.addWithoutUnique(new ParameterNode(1, StampPair.createSingle(StampFactory.forKind(JavaKind.Int))));
        AtomicReadAndAddNode rra = graph.addWithoutUnique(new AtomicReadAndAddNode(s, ConstantNode.forLong(8, graph), delta,
                        JavaKind.Int, LocationIdentity.any()));
        Assert.assertTrue(LfgWalk.isRawMemoryUse(rra, s));
        Assert.assertFalse(LfgWalk.isRawMemoryUse(rra, delta));
        assertRefused(walkFrom(s), rra);
        // Fresh LFG for the delta walk: the delta role is the ordinary passthrough (registered, no irNode).
        LocalFlowGraph lfg2 = new LocalFlowGraph(null);
        LocalVertex seed = lfg2.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        seed.irNode = delta;
        builder.lfgWalk.walkSSAFromParam(lfg2, delta, seed, null, new HashSet<>());
        LocalVertex pt = lfg2.vertexForNode(rra);
        Assert.assertNotNull("the delta role passes through", pt);
        Assert.assertNull("a passthrough vertex carries no irNode", pt.irNode);
    }

    /**
     * Every exact-class-name entry of the raw-memory set (the genscavenge classes this
     * module cannot reference by type) resolves to a graph Node class, so a rename fails here loudly.
     */
    @Test
    public void exactClassNameEntriesResolve() throws ClassNotFoundException {
        Assert.assertEquals(5, LfgWalk.RAW_MEMORY_EXACT_CLASS_NAMES.size());
        for (String name : LfgWalk.RAW_MEMORY_EXACT_CLASS_NAMES) {
            Class<?> c = Class.forName(name, false, LfgWalk.class.getClassLoader());
            Assert.assertTrue(name + " must be a graph Node", Node.class.isAssignableFrom(c));
            Assert.assertEquals(name, c.getName());
        }
    }

    /**
     * {@code OffsetAddress(base = Pi(Pi(Pi(s))), offset = (s == null ? 1 : 0))}
     * with a {@code JavaRead} at that address. The BFS reaches the address first through the primitive offset
     * (exempt: a passthrough, the walk continues to the read, whose address role is exempt too), and later
     * through the String base, which is refused by the predicate. (No refusal vertex is minted for the late role; the registry
     * keeps the first, exempt role's passthrough.)
     */
    @Test
    public void primitiveAndAddressRolesAreExemptButTheLaterBaseRoleIsRefused() {
        // the exemption of non-stringy references from the raw-memory refusal is unconditional (no knob)
        StructuredGraph graph = graph();
        ParameterNode s = stringParam(graph, 0);
        IsNullNode isNull = graph.addWithoutUnique(new IsNullNode(s));
        ConditionalNode prim = graph.addWithoutUnique(new ConditionalNode(isNull, ConstantNode.forLong(1, graph), ConstantNode.forLong(0, graph)));
        PiNode pi1 = graph.addWithoutUnique(new PiNode(s, s.stamp(NodeView.DEFAULT)));
        PiNode pi2 = graph.addWithoutUnique(new PiNode(pi1, s.stamp(NodeView.DEFAULT)));
        PiNode pi3 = graph.addWithoutUnique(new PiNode(pi2, s.stamp(NodeView.DEFAULT)));
        OffsetAddressNode addr = graph.addWithoutUnique(new OffsetAddressNode(pi3, prim));
        JavaReadNode read = graph.addWithoutUnique(new JavaReadNode(JavaKind.Int, addr, LocationIdentity.any(), BarrierType.NONE,
                        MemoryOrderMode.PLAIN, false));
        Assert.assertTrue(LfgWalk.rawMemExempt(addr, prim));
        Assert.assertFalse(LfgWalk.rawMemExempt(addr, pi3));
        Assert.assertTrue(LfgWalk.rawMemExempt(read, addr));
        walkFrom(s);
        LocalVertex addrPt = lfg.vertexForNode(addr);
        Assert.assertNotNull("the primitive offset role passes through (registered)", addrPt);
        Assert.assertNull("a passthrough vertex carries no irNode", addrPt.irNode);
        LocalVertex readPt = lfg.vertexForNode(read);
        Assert.assertNotNull("the address role of the read passes through", readPt);
        Assert.assertSame("the read's passthrough is created by the address's", addrPt, readPt.from);
        LocalVertex pi3v = lfg.vertexForNode(pi3);
        Assert.assertNotNull(pi3v);
        Assert.assertTrue("the String-base role of the address is refused (m1: the predicate on the base role)",
                        LfgWalk.isRefusedMemoryUse(addr, pi3));
        for (LocalVertex v : lfg.getVertices()) {
            Assert.assertNotSame("the refused (already visited) base role mints nothing", pi3v, v.from);
        }
    }

}
