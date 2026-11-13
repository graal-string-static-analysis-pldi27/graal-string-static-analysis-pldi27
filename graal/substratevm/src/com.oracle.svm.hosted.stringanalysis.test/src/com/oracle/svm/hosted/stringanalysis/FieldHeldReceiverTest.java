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

import com.oracle.svm.hosted.stringanalysis.ClosedFieldEscape.FieldOpen;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.virtual.AllocatedObjectNode;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.nodes.virtual.VirtualInstanceNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Pins of the field-held accumulator receiver: (1) the store-closed rule's decision table (static, every write-side
 * {@link FieldOpen} reason, an image-heap holder); (2) the write index keys IR writes by the declaring field (a
 * {@code StoreField}'s value; a committed virtual instance's Object slots, a nested virtual value mapped to its
 * materialization, none = an unresolvable value); primitive and static writes are not indexed; an unresolvable write
 * reports its name; (3) the unframed scan finds every {@code putfield} name:type; (4) the receiver is recognised as a
 * field load through pis only.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators", "jdk.graal.compiler/jdk.graal.compiler.core.common.memory",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended", "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type", "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual"})
public class FieldHeldReceiverTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** Fixture: H declares the accumulator field; K inherits it; P is the payload type of a nested virtual value. */
    static class H {
        StringBuilder accum = new StringBuilder();
        int p;
        static StringBuilder st;

        void reset() {
            accum = new StringBuilder(); // putfield H.accum
        }
    }

    static class K extends H {
        void viaSubclass() {
            accum = new StringBuilder(); // javac: putfield K.accum, resolved to H.accum
        }
    }

    static final class P {
    }

    @Test
    public void storeRuleDecisionTable() {
        Assert.assertNull("a closed instance field without a heap holder", ClosedFieldEscape.fieldStoreRule(false, null, false));
        Assert.assertEquals("STATIC", ClosedFieldEscape.fieldStoreRule(true, null, false));
        Assert.assertEquals("IMAGE_HEAP_HOLDER", ClosedFieldEscape.fieldStoreRule(false, null, true));
        for (FieldOpen o : FieldOpen.values()) {
            Assert.assertEquals(o.name(), ClosedFieldEscape.fieldStoreRule(false, o, false));
            Assert.assertEquals(o.name(), ClosedFieldEscape.fieldStoreRule(false, o, true));
            Assert.assertEquals("STATIC", ClosedFieldEscape.fieldStoreRule(true, o, true));
        }
    }

    private static StructuredGraph graph() {
        OptionValues options = new OptionValues(EconomicMap.create());
        DebugContext debug = new DebugContext.Builder(options).build();
        StructuredGraph graph = new StructuredGraph.Builder(options, debug).name("FieldHeldReceiverTest").build();
        graph.setStart(graph.add(new StartNode()));
        return graph;
    }

    @Test
    public void writeIndexKeysByDeclaringField() throws Exception {
        StructuredGraph g = graph();
        ResolvedJavaType ht = metaAccess.lookupJavaType(K.class);
        ParameterNode o = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(ht)))));
        ParameterNode val = g.addWithoutUnique(new ParameterNode(1, StampPair.createSingle(StampFactory.object())));
        ResolvedJavaField acc = metaAccess.lookupJavaField(H.class.getDeclaredField("accum"));
        ResolvedJavaField p = metaAccess.lookupJavaField(H.class.getDeclaredField("p"));
        ResolvedJavaField st = metaAccess.lookupJavaField(H.class.getDeclaredField("st"));
        StoreFieldNode s1 = g.add(new StoreFieldNode(o, acc, val));
        g.add(new StoreFieldNode(o, p, ConstantNode.forInt(1, g))); // primitive: not indexed
        g.add(new StoreFieldNode(null, st, val)); // static: not indexed
        // a commit of a virtual H whose accum slot holds a nested virtual P (materialized here) ...
        ResolvedJavaType hType = metaAccess.lookupJavaType(H.class);
        ResolvedJavaType pType = metaAccess.lookupJavaType(P.class);
        VirtualInstanceNode vh = g.add(new VirtualInstanceNode(hType, new ResolvedJavaField[]{p, acc}, true));
        VirtualInstanceNode vp = g.add(new VirtualInstanceNode(pType, new ResolvedJavaField[0], true));
        CommitAllocationNode can = g.add(new CommitAllocationNode());
        can.getVirtualObjects().add(vh);
        can.getVirtualObjects().add(vp);
        can.getValues().add(ConstantNode.forInt(0, g));
        can.getValues().add(vp);
        AllocatedObjectNode aonP = g.addWithoutUnique(new AllocatedObjectNode(vp));
        aonP.setCommit(can);
        // ... and a second commit whose accum slot holds a constant null and a third whose nested virtual is never materialized
        VirtualInstanceNode vh2 = g.add(new VirtualInstanceNode(hType, new ResolvedJavaField[]{acc}, true));
        CommitAllocationNode can2 = g.add(new CommitAllocationNode());
        can2.getVirtualObjects().add(vh2);
        ConstantNode nul = ConstantNode.forConstant(JavaConstant.NULL_POINTER, metaAccess, g);
        can2.getValues().add(nul);
        VirtualInstanceNode vh3 = g.add(new VirtualInstanceNode(hType, new ResolvedJavaField[]{acc}, true));
        VirtualInstanceNode vp3 = g.add(new VirtualInstanceNode(pType, new ResolvedJavaField[0], true));
        CommitAllocationNode can3 = g.add(new CommitAllocationNode());
        can3.getVirtualObjects().add(vh3);
        can3.getVirtualObjects().add(vp3);
        can3.getValues().add(vp3);

        List<String> got = new ArrayList<>();
        List<String> unresolved = new ArrayList<>();
        ClosedFieldEscape.collectStores(g, f -> f, (k, store, v) -> {
            Assert.assertEquals("keyed by the declaring field", acc, k);
            got.add((store == s1 ? "s1" : store == can ? "can" : store == can2 ? "can2" : store == can3 ? "can3" : "?") + "=" +
                            (v == val ? "val" : v == aonP ? "aonP" : v == nul ? "null" : v == null ? "UNRESOLVED" : "?"));
        }, unresolved::add);
        got.sort(null);
        Assert.assertEquals(List.of("can2=null", "can3=UNRESOLVED", "can=aonP", "s1=val"), got);
        Assert.assertTrue(unresolved.isEmpty());
        // an unresolvable write reports its name (fail closed for every field of that name)
        List<String> names = new ArrayList<>();
        ClosedFieldEscape.collectStores(g, f -> null, (k, store, v) -> Assert.fail("nothing resolves"), names::add);
        names.sort(null);
        Assert.assertEquals("primitive writes are filtered before resolving", List.of("accum", "accum", "accum", "accum"), names);
    }

    @Test
    public void unframedScanFindsEveryPutfield() throws Exception {
        new K().viaSubclass(); // the fixture runs (its references resolve)
        new H().reset();
        Set<String> out = new HashSet<>();
        Assert.assertTrue(ClosedFieldEscape.putfieldsOf(metaAccess.lookupJavaMethod(K.class.getDeclaredMethod("viaSubclass")), out));
        Assert.assertTrue(ClosedFieldEscape.putfieldsOf(metaAccess.lookupJavaMethod(H.class.getDeclaredMethod("reset")), out));
        Assert.assertEquals(Set.of("accum:Ljava/lang/StringBuilder;"), out);
        Set<String> ctor = new HashSet<>();
        Assert.assertTrue(ClosedFieldEscape.putfieldsOf(metaAccess.lookupJavaMethod(H.class.getDeclaredConstructor()), ctor));
        Assert.assertEquals("the field initializer is a putfield of <init>", Set.of("accum:Ljava/lang/StringBuilder;"), ctor);
    }

    @Test
    public void receiverIsAFieldLoadThroughPis() throws Exception {
        StructuredGraph g = graph();
        ResolvedJavaType ht = metaAccess.lookupJavaType(H.class);
        ParameterNode o = g.addWithoutUnique(new ParameterNode(0, StampPair.createSingle(StampFactory.objectNonNull(TypeReference.createWithoutAssumptions(ht)))));
        ResolvedJavaField acc = metaAccess.lookupJavaField(H.class.getDeclaredField("accum"));
        ResolvedJavaField st = metaAccess.lookupJavaField(H.class.getDeclaredField("st"));
        LoadFieldNode ld = g.add(LoadFieldNode.create(null, o, acc));
        ValueNode pi = g.addWithoutUnique(new PiNode(ld, StampFactory.objectNonNull()));
        Assert.assertSame(ld, ForwardFixpoint.fieldLoadOf(ld));
        Assert.assertSame("through a null-check pi", ld, ForwardFixpoint.fieldLoadOf(pi));
        Assert.assertNull("a parameter is not a field load", ForwardFixpoint.fieldLoadOf(o));
        Assert.assertNull("a static field is not a field-held receiver", ForwardFixpoint.fieldLoadOf(g.add(LoadFieldNode.create(null, null, st))));
        Assert.assertNull(ForwardFixpoint.fieldLoadOf(null));
    }
}
