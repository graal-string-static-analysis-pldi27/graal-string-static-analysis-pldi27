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

import org.junit.Assert;
import org.junit.Test;

/**
 * Pins. (1) The JMH Blackhole sink (knob {@code sink.jmhblackhole}, see
 * {@link StringAtoms#JMH_BLACKHOLE_SINK}). The rule keys on the exact declaring class, name, staticness and descriptor of
 * the three Object sinks of {@code org.openjdk.jmh.infra.Blackhole} (JMH 1.37); the sink slot is never the receiver of an
 * instance target; the target's usage site counts as safe-sink evidence ({@link TransferFacts#isSafeSinkMethod}). (2) The
 * extra-root bridge's reflective first reason accepts the child's reflection extra root. (3) The implicit
 * {@code AssertionError(Object)} message is exception flow, every other implicit exception argument an observation. (4) The
 * silent-end census labels.
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
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type"})
public class SinkAndExceptionFlowRulesTest {

    private static final String BH = "org.openjdk.jmh.infra.Blackhole";

    @Test
    public void knobDefaultsOn() {
        Assert.assertTrue("sink.jmhblackhole defaults to 1", StringAtoms.JMH_BLACKHOLE_SINK);
    }

    @Test
    public void sinkTargetsExactly() {
        Assert.assertTrue(StringAtoms.isJmhBlackholeSink(false, BH, "consume", "(Ljava/lang/Object;)V"));
        Assert.assertTrue(StringAtoms.isJmhBlackholeSink(false, BH, "consumeFull", "(Ljava/lang/Object;)V"));
        Assert.assertTrue(StringAtoms.isJmhBlackholeSink(true, BH, "consumeCompiler", "(Ljava/lang/Object;)V"));
        // staticness must match each helper
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(true, BH, "consume", "(Ljava/lang/Object;)V"));
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(false, BH, "consumeCompiler", "(Ljava/lang/Object;)V"));
        // primitive overloads, other methods, other classes (a user class of the same simple name, a subclass name)
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(false, BH, "consume", "(I)V"));
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(true, BH, "consumeCPU", "(J)V"));
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(false, "my.Blackhole", "consume", "(Ljava/lang/Object;)V"));
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink(false, BH + "L2", "consume", "(Ljava/lang/Object;)V"));
        Assert.assertFalse(StringAtoms.isJmhBlackholeSink((jdk.vm.ci.meta.ResolvedJavaMethod) null));
    }

    @Test
    public void sinkSlot() {
        Assert.assertTrue(StringAtoms.jmhBlackholeSinkSlot(true, true, 1, false, true));
        Assert.assertTrue("static consumeCompiler: slot 0 is the argument", StringAtoms.jmhBlackholeSinkSlot(true, true, 0, true, true));
        Assert.assertFalse("the receiver of an instance sink", StringAtoms.jmhBlackholeSinkSlot(true, true, 0, false, true));
        Assert.assertFalse("knob off", StringAtoms.jmhBlackholeSinkSlot(false, true, 1, false, true));
        Assert.assertFalse("not a STRING atom", StringAtoms.jmhBlackholeSinkSlot(true, false, 1, false, true));
        Assert.assertFalse("not a sink target", StringAtoms.jmhBlackholeSinkSlot(true, true, 1, false, false));
    }

    private static SugVertex site(String decl, String name, String sig) {
        SugVertex v = new SugVertex(1);
        v.setDeclaringClass(decl);
        v.setMethodName(name);
        v.setMethodSignature(sig);
        return v;
    }

    @Test
    public void sinkSiteIsSafeSinkEvidence() {
        Assert.assertTrue(TransferFacts.isSafeSinkMethod(site(BH, "consume", "Ljava/lang/Object;")));
        Assert.assertTrue(TransferFacts.isSafeSinkMethod(site(BH, "consumeFull", "Ljava/lang/Object;")));
        Assert.assertTrue(TransferFacts.isSafeSinkMethod(site(BH, "consumeCompiler", "Ljava/lang/Object;")));
        Assert.assertFalse(TransferFacts.isSafeSinkMethod(site(BH, "consume", "I")));
        Assert.assertFalse(TransferFacts.isSafeSinkMethod(site("my.Blackhole", "consume", "Ljava/lang/Object;")));
        // the pre-existing safe sinks are unchanged
        Assert.assertTrue(TransferFacts.isSafeSinkMethod(site("java.io.PrintStream", "println", "Ljava/lang/String;")));
    }

    @Test
    public void extraRootReasonIsReflective() {
        // the emitted reasons are ExtraRootsDiscovery's shared constants; pin their byte-identical
        // values so a reword of either side of the extra-root match (emitter or matcher) fails here
        Assert.assertEquals("string-analysis extra root (reflection)", ExtraRootsDiscovery.REFLECTION_METHOD_REASON);
        Assert.assertEquals("string-analysis extra root constructor (reflection)", ExtraRootsDiscovery.REFLECTION_CONSTRUCTOR_REASON);
        Assert.assertEquals("string-analysis extra root", ExtraRootsDiscovery.REFLECTION_REASON_PREFIX);
        Assert.assertEquals("(reflection)", ExtraRootsDiscovery.REFLECTION_REASON_SUFFIX);
        Assert.assertTrue("the shared constants must match the E3 predicate",
                        ReflectionBridge.childReflectionExtraRoot(ExtraRootsDiscovery.REFLECTION_METHOD_REASON) &&
                                        ReflectionBridge.childReflectionExtraRoot(ExtraRootsDiscovery.REFLECTION_CONSTRUCTOR_REASON));
        Assert.assertTrue(ReflectionBridge.childReflectionExtraRoot("string-analysis extra root (reflection)"));
        Assert.assertTrue(ReflectionBridge.childReflectionExtraRoot("string-analysis extra root constructor (reflection)"));
        Assert.assertFalse("the user-class extra root is not reflective", ReflectionBridge.childReflectionExtraRoot("string-analysis extra root"));
        Assert.assertFalse(ReflectionBridge.childReflectionExtraRoot("string-analysis extra root constructor"));
        Assert.assertFalse(ReflectionBridge.childReflectionExtraRoot("main entry point"));
        Assert.assertFalse(ReflectionBridge.childReflectionExtraRoot(null));
        Assert.assertTrue(ReflectionBridge.reflectiveFirstReason("string-analysis extra root (reflection)"));
        Assert.assertFalse(ReflectionBridge.reflectiveFirstReason("Registered in ReflectionFeature"));
        // the rest of the reflective-only rule is unchanged: the bridge table, JNI and native entries still decide
        Assert.assertFalse(ReflectionBridge.reflectiveOnly(false, true, false, false));
        Assert.assertFalse(ReflectionBridge.reflectiveOnly(true, true, true, false));
        Assert.assertTrue(ReflectionBridge.reflectiveOnly(true, true, false, false));
    }

    @Test
    public void assertionMessageIsExceptionFlow() {
        jdk.vm.ci.meta.MetaAccessProvider meta = jdk.vm.ci.hotspot.HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        jdk.graal.compiler.nodes.ValueNode msg = jdk.graal.compiler.nodes.ConstantNode.forInt(7);
        jdk.graal.compiler.nodes.ValueNode other = jdk.graal.compiler.nodes.ConstantNode.forInt(8);
        var kinds = jdk.graal.compiler.nodes.extended.BytecodeExceptionNode.BytecodeExceptionKind.class;
        var assertion = new jdk.graal.compiler.nodes.extended.BytecodeExceptionNode(meta, Enum.valueOf(kinds, "ASSERTION_ERROR_OBJECT"), msg);
        Assert.assertTrue(RecursiveTracking.assertionMessageUse(assertion, msg));
        Assert.assertFalse("not an argument", RecursiveTracking.assertionMessageUse(assertion, other));
        var store = new jdk.graal.compiler.nodes.extended.BytecodeExceptionNode(meta, Enum.valueOf(kinds, "ARRAY_STORE"), msg);
        Assert.assertFalse("ArrayStoreException reads only the class", RecursiveTracking.assertionMessageUse(store, msg));
        var cast = new jdk.graal.compiler.nodes.extended.BytecodeExceptionNode(meta, Enum.valueOf(kinds, "CLASS_CAST"), msg, other);
        Assert.assertFalse("ClassCastException reads only the class", RecursiveTracking.assertionMessageUse(cast, msg));
        Assert.assertNull("an assertion message is an effect, not a silent end", RecursiveTracking.silentUsesLabel(msg, java.util.List.of(assertion)));
        Assert.assertEquals("obs:BytecodeException/ARRAY_STORE", RecursiveTracking.silentUsesLabel(msg, java.util.List.of(store)));
    }

    @Test
    public void silentEndLabels() {
        jdk.graal.compiler.nodes.ValueNode v = jdk.graal.compiler.nodes.ConstantNode.forInt(1);
        Assert.assertEquals("no-usages", RecursiveTracking.silentUsesLabel(v, java.util.List.of()));
        Assert.assertEquals("unread-param", RecursiveTracking.silentCause("unread-param:a.B.m#1 @ x@3 Invoke"));
        Assert.assertEquals("state+obs", RecursiveTracking.silentCause("state+obs:IsNullNode @ x@3 Invoke"));
        Assert.assertEquals("pi-arm-dead", RecursiveTracking.silentCause("pi-arm-dead @ x@3 PiNode"));
        Assert.assertTrue("the census is on by default (print-only)", RecursiveTracking.SILENT_CENSUS);
    }

    @Test
    public void singleByteClassCheckRejects() {
        StringUtilizationGraph g = new StringUtilizationGraph();
        java.util.List<UsageTag> tags = new java.util.ArrayList<>();
        SugVertex c = g.newVertex();
        c.setNodeType(SugNodeType.STRING_METHOD_CALL);
        c.setMethodName("substring");
        c.setUsageTags(new java.util.BitSet());
        SugVertex println = site("java.io.PrintStream", "println", "Ljava/lang/String;");
        tags.add(new UsageTag(println, UsageRole.PARAMETER, 1));
        c.getUsageTags().set(0);
        g.setUsageTags(tags);
        Assert.assertFalse(SingleByteHeuristic.hasStrictClassCheck(g, c));
        tags.add(new UsageTag(site("java.lang.Object", "getClass", ""), UsageRole.RECEIVER, -1));
        c.getUsageTags().set(1);
        g.setUsageTags(tags);
        Assert.assertTrue("getClass() of the candidate", SingleByteHeuristic.hasStrictClassCheck(g, c));
        Assert.assertTrue(SugNameTables.isStrictClassCheckName("cast", "java.lang.Class"));
    }

    @Test
    public void literalSeedingIsOnByDefaultAndKeyedOnRealLiterals() {
        SugVertex lit = site(null, null, null);
        lit.setNodeType(SugNodeType.STRING_LITERAL);
        lit.setLiteralText("x");
        lit.setLength(1);
        lit.setLabel("x");
        Assert.assertTrue(StringAtoms.isSeedableLiteral(lit));
        lit.setLabel("concat-constant");
        Assert.assertFalse("a concat recipe constant has no ldc", StringAtoms.isSeedableLiteral(lit));
        lit.setLabel("xy");
        lit.setLiteralText("xy");
        lit.setLength(2);
        Assert.assertFalse(StringAtoms.isSeedableLiteral(lit));
        jdk.graal.compiler.nodes.ValueNode v = jdk.graal.compiler.nodes.ConstantNode.forInt(1);
        Assert.assertFalse(RecursiveTracking.identityObservation(v));
    }
}
