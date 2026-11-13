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

import java.io.Serializable;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.pointsto.AbstractAnalysisEngine;
import com.oracle.svm.hosted.phases.StringAnalysisChildInlining;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.bytecode.ResolvedJavaMethodBytecode;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.InvokeNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * {@link StringAnalysisChildInlining}: (1) the scope, i.e. which call sites open a method-handle
 * intrinsification scope in the analysis child (only {@code LambdaMetafactory} captures); (2) the call-site identity of
 * the invokes an inlined scope leaves: the points-to bci (the root call's), including the collision of an inner bci with
 * a real call of the root method, and the no-flow rule for an ambiguous or mismatched key.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java", "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type", "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo", "jdk.graal.compiler/jdk.graal.compiler.options"})
public class LambdaInliningParityTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    /** The indy kinds of the fixtures; each method below holds exactly the named call site(s). */
    @SuppressWarnings("unused")
    static final class Sites {
        static Supplier<String> capturingLambda(String s) {
            return () -> s; // LambdaMetafactory.metafactory
        }

        static Supplier<Integer> boundMethodReference(String s) {
            return s::length; // LambdaMetafactory.metafactory (bound receiver)
        }

        static Runnable nonCapturingLambda() {
            return () -> {
            }; // LambdaMetafactory.metafactory (no capture)
        }

        static Supplier<String> serializableLambda(String s) {
            return (Supplier<String> & Serializable) () -> s; // LambdaMetafactory.altMetafactory
        }

        static String concat(String s) {
            return "<" + s; // StringConcatFactory.makeConcatWithConstants
        }

        static int typeSwitch(Object o) {
            return switch (o) { // SwitchBootstraps.typeSwitch
                case String str -> str.length();
                case Integer i -> i;
                default -> 0;
            };
        }

        static Object constantHandle(String s) throws Throwable {
            return HANDLE.invokeExact(s); // a constant MethodHandle call, no invokedynamic
        }

        record R(String s) {
            // toString/hashCode/equals: ObjectMethods.bootstrap
        }

        static final MethodHandle HANDLE;
        static {
            try {
                HANDLE = MethodHandles.lookup().findStatic(Sites.class, "concat", MethodType.methodType(String.class, String.class)).asType(MethodType.methodType(Object.class, String.class));
            } catch (ReflectiveOperationException e) {
                throw new ExceptionInInitializerError(e);
            }
        }

        /** a real {@code substring} call and a lambda capture in one method. */
        static int captureAfterSubstring(String base) {
            String c = base.substring(1);
            Supplier<String> sup = () -> c;
            return sup.get().length();
        }

        /** Stands in for an inlined method of the scope (the frame an MH-scope invoke carries); its code spans the bcis used. */
        static void scopeMethod() {
            otherTarget();
            otherTarget();
            otherTarget();
            lambdaConstructorStandIn();
            otherTarget();
            otherTarget();
            otherTarget();
            otherTarget();
            otherTarget();
            otherTarget();
        }

        static void lambdaConstructorStandIn() {
        }

        static void otherTarget() {
        }
    }

    private static ResolvedJavaMethod method(Class<?> holder, String name, Class<?>... params) throws NoSuchMethodException {
        return META.lookupJavaMethod(holder.getDeclaredMethod(name, params));
    }

    /** Every bci of {@code m}'s bytecode, and the subset that holds an {@code invokedynamic}. */
    private static List<Integer> bcis(ResolvedJavaMethod m, boolean indyOnly) {
        List<Integer> out = new ArrayList<>();
        BytecodeStream s = new BytecodeStream(m.getCode());
        while (s.currentBC() != Bytecodes.END) {
            if (!indyOnly || s.currentBC() == Bytecodes.INVOKEDYNAMIC) {
                out.add(s.currentBCI());
            }
            s.next();
        }
        return out;
    }

    private static int firstBci(ResolvedJavaMethod m, int opcode) {
        BytecodeStream s = new BytecodeStream(m.getCode());
        while (s.currentBC() != Bytecodes.END) {
            if (s.currentBC() == opcode) {
                return s.currentBCI();
            }
            s.next();
        }
        throw new AssertionError("no " + Bytecodes.nameOf(opcode) + " in " + m.format("%H.%n"));
    }

    /** {@code m} holds exactly one indy; it opens a scope iff {@code lambda}; no other bci does. */
    private static void assertSite(ResolvedJavaMethod m, boolean lambda) {
        List<Integer> indys = bcis(m, true);
        Assert.assertEquals("fixture precondition: one invokedynamic in " + m.format("%H.%n"), 1, indys.size());
        Assert.assertEquals(m.format("%H.%n") + "@" + indys.get(0), lambda, StringAnalysisChildInlining.isLambdaMetafactorySite(m, indys.get(0)));
        for (int bci : bcis(m, false)) {
            if (!indys.contains(bci)) {
                Assert.assertFalse(m.format("%H.%n") + "@" + bci + " is not an indy", StringAnalysisChildInlining.isLambdaMetafactorySite(m, bci));
            }
        }
    }

    @Test
    public void lambdaMetafactoryCapturesOpenAScope() throws Exception {
        assertSite(method(Sites.class, "capturingLambda", String.class), true);
        assertSite(method(Sites.class, "boundMethodReference", String.class), true);
        assertSite(method(Sites.class, "nonCapturingLambda"), true);
        assertSite(method(Sites.class, "serializableLambda", String.class), true);
    }

    @Test
    public void otherMethodHandleRootsAreLeftAlone() throws Exception {
        assertSite(method(Sites.class, "concat", String.class), false); // StringConcatFactory
        assertSite(method(Sites.class, "typeSwitch", Object.class), false); // SwitchBootstraps
        assertSite(method(Sites.R.class, "toString"), false); // ObjectMethods (records)
        assertSite(method(Sites.R.class, "hashCode"), false);
        assertSite(method(Sites.R.class, "equals", Object.class), false);
        ResolvedJavaMethod constant = method(Sites.class, "constantHandle", String.class);
        Assert.assertTrue("fixture precondition: no invokedynamic", bcis(constant, true).isEmpty());
        for (int bci : bcis(constant, false)) {
            Assert.assertFalse("constant MethodHandle.invokeExact @" + bci, StringAnalysisChildInlining.isLambdaMetafactorySite(constant, bci));
        }
        ResolvedJavaMethod m = method(Sites.class, "capturingLambda", String.class);
        Assert.assertFalse(StringAnalysisChildInlining.isLambdaMetafactorySite(m, -1));
        Assert.assertFalse(StringAnalysisChildInlining.isLambdaMetafactorySite(m, m.getCodeSize()));
    }

    // ------------------------------------------------------------------ the call-site identity

    /** A flow of the points-to index in miniature: its target method. */
    private record Flow(String name, ResolvedJavaMethod target) {
    }

    private static final class Graph {
        final StructuredGraph graph;
        final ResolvedJavaMethod root;

        Graph(ResolvedJavaMethod root) {
            OptionValues options = new OptionValues(EconomicMap.create());
            this.graph = new StructuredGraph.Builder(options, new DebugContext.Builder(options).build()).name("LambdaInliningParityTest").method(root).build();
            this.graph.setStart(graph.add(new StartNode()));
            this.root = root;
        }

        FrameState frame(FrameState outer, ResolvedJavaMethod m, int bci) {
            return graph.add(new FrameState(outer, new ResolvedJavaMethodBytecode(m), bci, new ValueNode[0], new ValueNode[0], 0, new JavaKind[0], new ValueNode[0], new ValueNode[0], null,
                            FrameState.StackState.BeforePop));
        }

        InvokeNode invoke(ResolvedJavaMethod target, int bci, FrameState stateAfter) {
            MethodCallTargetNode ct = graph.addWithoutUnique(new MethodCallTargetNode(InvokeKind.Static, target, new ValueNode[0], StampPair.createSingle(StampFactory.forVoid()), null));
            InvokeNode inv = graph.addWithoutUnique(new InvokeNode(ct, bci));
            inv.setStateAfter(stateAfter);
            return inv;
        }
    }

    /**
     * The collision: the invoke the scope leaves carries the inner bci of the inlined method, which is
     * the bci of the root method's real {@code substring} call. Its identity is the root call's bci (the lambda capture),
     * where the points-to analysis keys its flow; the real call keeps its own bci.
     */
    @Test
    public void scopeInvokesAreKeyedByTheRootCallBci() throws Exception {
        ResolvedJavaMethod root = method(Sites.class, "captureAfterSubstring", String.class);
        int substringBci = firstBci(root, Bytecodes.INVOKEVIRTUAL);
        int captureBci = firstBci(root, Bytecodes.INVOKEDYNAMIC);
        Assert.assertTrue(StringAnalysisChildInlining.isLambdaMetafactorySite(root, captureBci));
        ResolvedJavaMethod substring = method(String.class, "substring", int.class);
        ResolvedJavaMethod ctor = method(Sites.class, "lambdaConstructorStandIn");
        ResolvedJavaMethod scope = method(Sites.class, "scopeMethod");

        Graph g = new Graph(root);
        InvokeNode real = g.invoke(substring, substringBci, g.frame(null, root, substringBci + 3));
        // the scope's invoke: inner bci = the substring's bci (the collision), its frame's outer state = the capture site
        InvokeNode left = g.invoke(ctor, substringBci, g.frame(g.frame(null, root, captureBci), scope, substringBci + 3));

        Assert.assertEquals(substringBci, StringAnalysisChildInlining.pointsToBci(real));
        Assert.assertFalse(StringAnalysisChildInlining.isFromInlinedScope(real));
        Assert.assertEquals("the scope invoke is keyed by the root call", captureBci, StringAnalysisChildInlining.pointsToBci(left));
        Assert.assertTrue(StringAnalysisChildInlining.isFromInlinedScope(left));
        // = the points-to analysis' own position of the invoke (MethodTypeFlowBuilder.getInvokePosition, no source position)
        Assert.assertEquals(AbstractAnalysisEngine.syntheticSourcePosition(left, root).getBCI(), StringAnalysisChildInlining.pointsToBci(left));
        Assert.assertEquals(AbstractAnalysisEngine.syntheticSourcePosition(real, root).getBCI(), StringAnalysisChildInlining.pointsToBci(real));

        Flow substringFlow = new Flow("substring", substring);
        Flow ctorFlow = new Flow("ctor", ctor);
        Map<Integer, Flow> index = Map.of(substringBci, substringFlow, captureBci, ctorFlow);
        Assert.assertSame("the collision: by Invoke.bci() the scope invoke would take the substring's flow", substringFlow, index.get(left.bci()));
        Assert.assertSame(ctorFlow, SugBuilderV2.invokeFlowAt(index, Set.of(), left, Flow::target));
        Assert.assertSame(substringFlow, SugBuilderV2.invokeFlowAt(index, Set.of(), real, Flow::target));
    }

    /** With a node source position, the identity is its outermost caller's bci, as for the points-to invoke position. */
    @Test
    public void sourcePositionCallerChainGivesTheRootBci() throws Exception {
        ResolvedJavaMethod root = method(Sites.class, "captureAfterSubstring", String.class);
        int captureBci = firstBci(root, Bytecodes.INVOKEDYNAMIC);
        ResolvedJavaMethod scope = method(Sites.class, "scopeMethod");
        Graph g = new Graph(root);
        InvokeNode left = g.invoke(method(Sites.class, "lambdaConstructorStandIn"), 2, g.frame(null, scope, 3));
        NodeSourcePosition rootPos = new NodeSourcePosition(null, root, captureBci);
        left.setNodeSourcePosition(new NodeSourcePosition(new NodeSourcePosition(rootPos, scope, 7), scope, 2));
        Assert.assertEquals(captureBci, StringAnalysisChildInlining.pointsToBci(left));
        Assert.assertTrue(StringAnalysisChildInlining.isFromInlinedScope(left));
        InvokeNode own = g.invoke(scope, 5, g.frame(null, root, 8));
        own.setNodeSourcePosition(new NodeSourcePosition(null, root, 5));
        Assert.assertEquals(5, StringAnalysisChildInlining.pointsToBci(own));
        Assert.assertFalse(StringAnalysisChildInlining.isFromInlinedScope(own));
    }

    /**
     * Where the root bci holds several flows (the scope left several invokes), or the flow at it has another target, a
     * scope invoke has no flow (no LFG vertex); an invoke of the method's own code is looked up by its bci as before.
     */
    @Test
    public void ambiguousOrMismatchedRootBciGivesNoFlow() throws Exception {
        ResolvedJavaMethod root = method(Sites.class, "captureAfterSubstring", String.class);
        int substringBci = firstBci(root, Bytecodes.INVOKEVIRTUAL);
        int captureBci = firstBci(root, Bytecodes.INVOKEDYNAMIC);
        ResolvedJavaMethod ctor = method(Sites.class, "lambdaConstructorStandIn");
        ResolvedJavaMethod other = method(Sites.class, "otherTarget");
        ResolvedJavaMethod substring = method(String.class, "substring", int.class);
        Graph g = new Graph(root);
        InvokeNode left = g.invoke(ctor, 1, g.frame(g.frame(null, root, captureBci), method(Sites.class, "scopeMethod"), 4));
        InvokeNode real = g.invoke(substring, substringBci, g.frame(null, root, substringBci + 3));

        Map<Integer, Flow> index = Map.of(captureBci, new Flow("ctor", ctor), substringBci, new Flow("substring", substring));
        Assert.assertNull("ambiguous root bci", SugBuilderV2.invokeFlowAt(index, Set.of(captureBci), left, Flow::target));
        Assert.assertNull("the flow at the root bci has another target", SugBuilderV2.invokeFlowAt(Map.of(captureBci, new Flow("other", other)), Set.of(), left, Flow::target));
        Assert.assertNull("no flow at the root bci", SugBuilderV2.invokeFlowAt(Map.of(substringBci, new Flow("ctor", ctor)), Set.of(), left, Flow::target));
        Assert.assertNull("no index for the method", SugBuilderV2.invokeFlowAt(null, null, left, Flow::target));
        // the method's own invokes: by their bci, the first flow as before (ambiguity and target are not consulted)
        Assert.assertEquals("substring", SugBuilderV2.invokeFlowAt(index, Set.of(substringBci), real, Flow::target).name());
        Assert.assertEquals("other", SugBuilderV2.invokeFlowAt(Map.of(substringBci, new Flow("other", other)), Set.of(), real, Flow::target).name());
    }

    private static LocalFlowGraph.LocalVertex callVertex(Object irNode, int bci) {
        LocalFlowGraph.LocalVertex v = new LocalFlowGraph.LocalVertex(null, -1, LocalFlowGraph.VertexKind.INVOKE_CALLSITE);
        v.irNode = irNode;
        v.bci = bci;
        return v;
    }

    /**
     * The target resolution reads a call vertex's invoke flow by the call-site identity rule
     * ({@code ForwardFixpoint.callFlowAt}, used by {@code computeTargets} and the target cap). At the root bci of a scope
     * invoke the key's first flow can belong to another invoke, here a special invoke of another target (the lambda
     * constructor's): reading it would bind a virtual callee to its declared method. The scope invoke gets no flow (the
     * CHA takes the declaring class), also where the key is ambiguous; only a unique key holding its own target's flow is
     * accepted. A vertex of the method's own code,

     * or one without an IR invoke, keeps the first flow at its bci.
     */
    @Test
    public void targetResolutionNeverReadsAForeignFlow() throws Exception {
        ResolvedJavaMethod root = method(Sites.class, "captureAfterSubstring", String.class);
        int substringBci = firstBci(root, Bytecodes.INVOKEVIRTUAL);
        int captureBci = firstBci(root, Bytecodes.INVOKEDYNAMIC);
        ResolvedJavaMethod ctor = method(Sites.class, "lambdaConstructorStandIn");
        ResolvedJavaMethod other = method(Sites.class, "otherTarget");
        ResolvedJavaMethod substring = method(String.class, "substring", int.class);
        ResolvedJavaMethod scope = method(Sites.class, "scopeMethod");
        Graph g = new Graph(root);
        InvokeNode virtualInScope = g.invoke(other, 1, g.frame(g.frame(null, root, captureBci), scope, 4));
        InvokeNode ctorInScope = g.invoke(ctor, 2, g.frame(g.frame(null, root, captureBci), scope, 5));
        InvokeNode real = g.invoke(substring, substringBci, g.frame(null, root, substringBci + 3));
        Assert.assertTrue(StringAnalysisChildInlining.isFromInlinedScope(virtualInScope));
        Assert.assertEquals(captureBci, StringAnalysisChildInlining.pointsToBci(virtualInScope));

        Flow special = new Flow("special <init>", ctor);
        Flow substringFlow = new Flow("substring", substring);
        Map<Integer, Flow> index = Map.of(captureBci, special, substringBci, substringFlow);
        LocalFlowGraph.LocalVertex v = callVertex(virtualInScope, captureBci);
        Assert.assertSame("the pre-R lookup read the key's first flow: another invoke's", special, index.get(v.bci));
        Assert.assertNull("a foreign flow at the root bci", ForwardFixpoint.callFlowAt(index, Set.of(), v, Flow::target));
        Assert.assertNull("an ambiguous root bci", ForwardFixpoint.callFlowAt(index, Set.of(captureBci), callVertex(ctorInScope, captureBci), Flow::target));
        Assert.assertSame("a unique key with its own target's flow", special, ForwardFixpoint.callFlowAt(index, Set.of(), callVertex(ctorInScope, captureBci), Flow::target));
        Assert.assertSame("the method's own invoke: its bci", substringFlow, ForwardFixpoint.callFlowAt(index, Set.of(substringBci), callVertex(real, substringBci), Flow::target));
        Assert.assertSame("no IR invoke (a fixture or desugared vertex): its bci", special, ForwardFixpoint.callFlowAt(index, Set.of(captureBci), callVertex(null, captureBci), Flow::target));
        Assert.assertNull("no index", ForwardFixpoint.callFlowAt(null, null, v, Flow::target));
    }
}
