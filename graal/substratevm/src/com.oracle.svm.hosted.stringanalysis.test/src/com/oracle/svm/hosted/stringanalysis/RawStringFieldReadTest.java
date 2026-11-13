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
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.LocalFlowGraph.LocalVertex;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.memory.address.OffsetAddressNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Pins: a raw read of {@code String.value}/{@code coder} on a walked value
 * is a usage (a class-check-shaped usage vertex carrying the field name), decided per representation by the
 * whitelists; {@code hash}/{@code hashIsZero} are not usages; non-String references are exempt from the raw-memory refusal.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.word", "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc", "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory", "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.nodes.debug"})
public class RawStringFieldReadTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("RawStringFieldReadTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    private ParameterNode param(StructuredGraph graph, int index, Class<?> type) {
        ResolvedJavaType t = metaAccess.lookupJavaType(type);
        return graph.addWithoutUnique(new ParameterNode(index, StampPair.createSingle(
                        StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(t)))));
    }

    private ResolvedJavaField stringField(String name) {
        for (ResolvedJavaField f : metaAccess.lookupJavaType(String.class).getInstanceFields(false)) {
            if (f.getName().equals(name)) {
                return f;
            }
        }
        throw new AssertionError("no String." + name);
    }

    /** Pin 1: the usage names; hash/hashIsZero are not usages (the hash-cache protocol holds on every rep). */
    @Test
    public void usageNamesPerField() {
        Assert.assertEquals("value(raw)", SugNameTables.rawStringFieldUsageName("value"));
        Assert.assertEquals("coder(raw)", SugNameTables.rawStringFieldUsageName("coder"));
        Assert.assertNull(SugNameTables.rawStringFieldUsageName("hash"));
        Assert.assertNull(SugNameTables.rawStringFieldUsageName("hashIsZero"));
    }

    /**
     * Pin 2: the per-rep verdict. value(raw) is whitelisted by neither W_view (StringView, the accumulator view) nor
     * W_lazy (every lazy rep has value == null); coder(raw) by both (the rep's coder field is its coder() answer).
     */
    @Test
    public void whitelistsDecideTheRawReadPerRepresentation() {
        Assert.assertFalse(StringViewWhitelist.isWhitelisted("value(raw)", "java.lang.String", ""));
        Assert.assertFalse(LazyConcatWhitelist.isWhitelisted("value(raw)", "java.lang.String", ""));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("coder(raw)", "java.lang.String", ""));
        Assert.assertTrue(LazyConcatWhitelist.isWhitelisted("coder(raw)", "java.lang.String", ""));
        Assert.assertFalse("declared by String only", StringViewWhitelist.isWhitelisted("coder(raw)", "java.lang.Object", ""));
        Assert.assertFalse("the plain accessor name stays a non-site", StringViewWhitelist.isWhitelisted("value", "java.lang.String", ""));
    }

    /** Pin 3: the usage vertex shape: CLASS_CHECK kind, field-marked, anchored at the load, no irNode. */
    @Test
    public void rawReadVertexShape() {
        StructuredGraph graph = graph();
        ParameterNode s = param(graph, 0, String.class);
        LoadFieldNode load = graph.addWithoutUnique(LoadFieldNode.create(null, s, stringField("value")));
        LocalFlowGraph lfg = new LocalFlowGraph(null);
        LocalVertex seed = lfg.newVertex(LocalFlowGraph.VertexKind.INTERNAL);
        LfgWalk.mintRawStringFieldReadUsage(lfg, seed, load, s);
        LocalVertex rv = null;
        for (LocalVertex v : lfg.getVertices()) {
            if (v.from == seed) {
                rv = v;
            }
        }
        Assert.assertNotNull("the usage vertex's creator is the walked vertex", rv);
        Assert.assertEquals(LocalFlowGraph.VertexKind.CLASS_CHECK, rv.kind);
        Assert.assertEquals("value", rv.rawStringField);
        Assert.assertSame(load, rv.armAnchor);
        Assert.assertNull("the LOAD vertex owns the node", rv.irNode);
        Assert.assertNull(lfg.vertexForNode(load));
    }

    /**
     * Pin 5: the exemption (an isAssignableFrom test against String and the builder family): a non-stringy reference
     * walked value (a String's byte[] value, an Integer) is exempt from the raw-memory refusal; a String, an
     * Object/CharSequence/Appendable, a representation type, a builder (StringBuilder, StringBuffer,
     * AbstractStringBuilder) and an unknown type stay strict.
     */
    @Test
    public void k2ExemptsOnlyNonStringyReferences() {
        // the exemption is unconditional (no knob)
        ResolvedJavaType[] stringy = new ResolvedJavaType[LfgWalk.STRINGY_RAW_MEM_TYPE_NAMES.length];
        for (int i = 0; i < stringy.length; i++) {
            try {
                stringy[i] = metaAccess.lookupJavaType(Class.forName(LfgWalk.STRINGY_RAW_MEM_TYPE_NAMES[i]));
            } catch (ClassNotFoundException e) {
                throw new AssertionError(e);
            }
        }
        StructuredGraph graph = graph();
        ParameterNode bytes = param(graph, 0, byte[].class);
        ParameterNode integer = param(graph, 1, Integer.class);
        ParameterNode str = param(graph, 2, String.class);
        ParameterNode obj = param(graph, 3, Object.class);
        ParameterNode cs = param(graph, 4, CharSequence.class);
        ParameterNode rep = param(graph, 5, com.oracle.svm.core.stringrep.StringView.class);
        ParameterNode unknown = graph.addWithoutUnique(new ParameterNode(6, StampPair.createSingle(StampFactory.object())));
        ParameterNode sb = param(graph, 7, StringBuilder.class);
        ParameterNode sbuf = param(graph, 8, StringBuffer.class);
        ParameterNode app = param(graph, 9, Appendable.class);
        Assert.assertTrue(LfgWalk.isNonStringyReference(bytes, stringy));
        Assert.assertTrue(LfgWalk.isNonStringyReference(integer, stringy));
        for (ParameterNode p : new ParameterNode[]{str, obj, cs, rep, unknown, sb, sbuf, app}) {
            Assert.assertFalse(p.stamp(jdk.graal.compiler.nodes.NodeView.DEFAULT).toString(), LfgWalk.isNonStringyReference(p, stringy));
        }
        Assert.assertFalse("no stringy set: strict", LfgWalk.isNonStringyReference(bytes, null));
        LfgWalk.stringyRawMemTypes = stringy;
        try {
            OffsetAddressNode onBytes = graph.addWithoutUnique(new OffsetAddressNode(bytes, ConstantNode.forLong(16, graph)));
            OffsetAddressNode onString = graph.addWithoutUnique(new OffsetAddressNode(str, ConstantNode.forLong(16, graph)));
            OffsetAddressNode onBuilder = graph.addWithoutUnique(new OffsetAddressNode(sb, ConstantNode.forLong(16, graph)));
            Assert.assertFalse(LfgWalk.isRefusedMemoryUse(onBytes, bytes));
            Assert.assertTrue(LfgWalk.isRefusedMemoryUse(onString, str));
            Assert.assertTrue("builders stay strict", LfgWalk.isRefusedMemoryUse(onBuilder, sb));
        } finally {
            LfgWalk.stringyRawMemTypes = null;
        }
    }
}
