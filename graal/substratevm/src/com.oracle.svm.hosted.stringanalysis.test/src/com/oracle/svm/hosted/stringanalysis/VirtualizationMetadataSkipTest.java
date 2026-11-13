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
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.LocalFlowGraph.LocalVertex;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.MaterializedObjectState;
import jdk.graal.compiler.nodes.virtual.VirtualInstanceNode;
import jdk.graal.compiler.nodes.virtual.VirtualObjectNode;
import jdk.graal.compiler.nodes.virtual.VirtualObjectState;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.runtime.JVMCIBackend;
import org.graalvm.collections.EconomicMap;

/**
 * The virtualization-metadata walk skip: {@link MaterializedObjectState} / {@link VirtualObjectState} (partial-escape
 * deoptimization bookkeeping for a virtualized allocation) never execute at runtime (like {@code FrameState}), so the
 * walk from a virtualized-allocation seed ({@code AllocatedObjectNode}) makes no vertex for them and does not continue
 * through them. The pins assert the vertices the walk makes (the registry and the invoke set that feed the atom keys
 * and {@code callersOf}). Pin 3: an invoke with no resolvable type flow makes no call vertex and is not walked through.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi", "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options"})
public class VirtualizationMetadataSkipTest {

    /** The walk fixture: a SugBuilderV2 shell + a hand-built decoded-graph shape. */
    private static final class Fixture {
        final SugBuilderV2 builder = new SugBuilderV2(null);
        final LfgWalk walk;
        final LocalFlowGraph lfg = new LocalFlowGraph(null);
        final MetaAccessProvider metaAccess;

        Fixture() {
            this.walk = builder.lfgWalk;
            JVMCIBackend backend = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend();
            this.metaAccess = backend.getMetaAccess();
        }

        /** A virtualized {@code new holder(...)} allocation: von + AllocatedObjectNode. */
        AllocatedObjectNode virtualizedAllocation(StructuredGraph graph) {
            ResolvedJavaType holder = (ResolvedJavaType) metaAccess.lookupJavaType(Object.class);
            VirtualObjectNode von = graph.addOrUnique(new VirtualInstanceNode(holder, true));
            return graph.addWithoutUnique(new AllocatedObjectNode(von));
        }

        StructuredGraph graph() {
            OptionValues options = new OptionValues(EconomicMap.create());
            DebugContext debug = new DebugContext.Builder(options).build();
            StructuredGraph graph = new StructuredGraph.Builder(options, debug)
                            .name("VirtualizationMetadataSkipTest").build();
            graph.setStart(graph.add(new StartNode()));
            return graph;
        }

        /** Walks from {@code start} like the container-instance seed walk (method=null: every by-bci resolution fails). */
        LocalVertex walkFrom(Node start) {
            LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
            seed.label = "container-instance";
            seed.irNode = start;
            walk.walkSSAFromParam(lfg, start, seed, null, new HashSet<>());
            return seed;
        }
    }

    /**
     * PIN 1: a {@link MaterializedObjectState} consuming the virtualized allocation (the
     * {@code Field.storedValue} shape, pos=null) makes no vertex.
     */
    @Test
    public void materializedObjectStateUseMakesNoVertex() {
        Fixture f = new Fixture();
        StructuredGraph graph = f.graph();
        AllocatedObjectNode aon = f.virtualizedAllocation(graph);
        graph.addWithoutUnique(new MaterializedObjectState(aon.getVirtualObject(), aon));
        LocalVertex seed = f.walkFrom(aon);
        Assert.assertEquals("virtualization metadata (MaterializedObjectState) makes no vertex", List.of(seed), f.lfg.getVertices());
        Assert.assertEquals("only the seed node is registered", 1, f.lfg.registrySize());
    }

    /** A one-field holder: the virtual object's single slot carries the walked value. */
    private static class ValueHolder {
        @SuppressWarnings("unused") Object slot;
    }

    /** PIN 2: the sibling {@link VirtualObjectState} (field-value bookkeeping) — same skip. */
    @Test
    public void virtualObjectStateUseMakesNoVertex() {
        Fixture f = new Fixture();
        StructuredGraph graph = f.graph();
        ResolvedJavaType holderType = (ResolvedJavaType) f.metaAccess.lookupJavaType(ValueHolder.class);
        jdk.vm.ci.meta.ResolvedJavaField[] fields = holderType.getInstanceFields(true);
        VirtualObjectNode von = graph.addOrUnique(new VirtualInstanceNode(holderType, fields, true));
        AllocatedObjectNode aon = graph.addWithoutUnique(new AllocatedObjectNode(von));
        // The virtual object's one field slot is the walked allocation — the VOS is a use of it.
        graph.addWithoutUnique(new VirtualObjectState(von, new ValueNode[]{aon}));
        LocalVertex seed = f.walkFrom(aon);
        Assert.assertEquals(List.of(seed), f.lfg.getVertices());
        Assert.assertEquals(1, f.lfg.registrySize());
    }

    /**
     * PIN 3: an invoke whose type flow cannot be resolved by bci (in production an unresolvable native/intrinsic invoke)
     * makes no INVOKE_CALLSITE vertex (so it never joins {@code callersOf}) and is not walked through.
    
     */
    @Test
    public void unresolvableInvokeUseMakesNoCallVertex() throws Exception {
        Fixture f = new Fixture();
        StructuredGraph graph = f.graph();
        AllocatedObjectNode aon = f.virtualizedAllocation(graph);
        ResolvedJavaMethod toString = (ResolvedJavaMethod) f.metaAccess.lookupJavaMethod(
                        Object.class.getMethod("toString"));
        ResolvedJavaType object = (ResolvedJavaType) f.metaAccess.lookupJavaType(Object.class);
        StampPair returnStamp = StampPair.createSingle(StampFactory.object(
                        TypeReference.createWithoutAssumptions(object)));
        MethodCallTargetNode mctn = graph.addWithoutUnique(new MethodCallTargetNode(
                        InvokeKind.Virtual, toString, new ValueNode[]{aon}, returnStamp, null));
        graph.addWithoutUnique(new InvokeNode(mctn, 42));
        LocalVertex seed = f.walkFrom(aon);
        Assert.assertTrue("an unresolvable invoke makes no call vertex", f.lfg.getInvokeVertices().isEmpty());
        Assert.assertEquals(List.of(seed), f.lfg.getVertices());
        Assert.assertEquals("the invoke's result is not registered (no continuation)", 1, f.lfg.registrySize());
    }

    /** PIN 4 (the adjacent precedent, regression-guarded): a FrameState local-slot use never flags. */
    @Test
    public void frameStateUseMakesNoVertex() {
        Fixture f = new Fixture();
        StructuredGraph graph = f.graph();
        ResolvedJavaType holder = (ResolvedJavaType) f.metaAccess.lookupJavaType(Object.class);
        ParameterNode param = graph.addWithoutUnique(new ParameterNode(0,
                        StampPair.createSingle(StampFactory.objectNonNull(
                                        TypeReference.createWithoutAssumptions(holder)))));
        graph.addWithoutUnique(new FrameState(null, null, 0,
                        new ValueNode[]{param}, new ValueNode[0], 0,
                        new JavaKind[0], new ValueNode[0], new ValueNode[0],
                        null, FrameState.StackState.BeforePop));
        LocalVertex seed = f.walkFrom(param);
        Assert.assertEquals(List.of(seed), f.lfg.getVertices());
        Assert.assertEquals(1, f.lfg.registrySize());
    }
}
