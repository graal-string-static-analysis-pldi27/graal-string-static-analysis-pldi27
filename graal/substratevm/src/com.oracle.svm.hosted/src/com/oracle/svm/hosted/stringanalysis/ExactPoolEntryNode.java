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

import com.oracle.svm.core.BuildPhaseProvider;

import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeClass;
import jdk.graal.compiler.nodeinfo.NodeCycles;
import jdk.graal.compiler.nodeinfo.NodeInfo;
import jdk.graal.compiler.nodeinfo.NodeSize;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.FloatingNode;
import jdk.graal.compiler.nodes.spi.Canonicalizable;
import jdk.graal.compiler.nodes.spi.CanonicalizerTool;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The value of {@code SingleByteString.exactPoolEntry(POOL[i])}: an element of the {@code String[]} pool, stamped exact
 * non-null {@code SingleByteString} without a check. Sound by the premise at {@code SingleByteString.POOL} (filled at
 * build time with SingleByteString instances only, never written again; {@link RepTypeChecks}' image-heap check checks
 * every reference the pool holds).
 * <p>
 * Not a plain {@link PiNode}: points-to unproxifies Pi nodes, so it would see the element load of a {@code String[]}
 * (every instantiated String subtype). This node is no proxy: the type-flow builder gives a node without a flow of its
 * own and with an exact stamp a source flow of exactly that type ({@code MethodTypeFlowBuilder.TypeFlowsOfNodes.lookup} /
 * {@code handleObjectStamp}). After the analysis it canonicalizes to a guard-free {@link PiNode} with the same stamp,
 * as {@code ReachabilityRegistrationNode} / {@code TestDeoptimizeNode} do.
 */
@NodeInfo(cycles = NodeCycles.CYCLES_0, size = NodeSize.SIZE_0)
public final class ExactPoolEntryNode extends FloatingNode implements Canonicalizable {
    public static final NodeClass<ExactPoolEntryNode> TYPE = NodeClass.create(ExactPoolEntryNode.class);

    @Input ValueNode object;

    public ExactPoolEntryNode(ValueNode object, ResolvedJavaType singleByteString) {
        super(TYPE, StampFactory.objectNonNull(TypeReference.createExactTrusted(singleByteString)));
        this.object = object;
    }

    public ValueNode object() {
        return object;
    }

    @Override
    public Node canonical(CanonicalizerTool tool) {
        if (!BuildPhaseProvider.isAnalysisFinished()) {
            return this;
        }
        if (stamp(NodeView.DEFAULT).equals(object.stamp(NodeView.DEFAULT))) {
            return object;
        }
        return new PiNode(object, stamp(NodeView.DEFAULT));
    }
}
