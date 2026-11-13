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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import com.oracle.svm.hosted.code.InliningUtilities;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeBitMap;
import jdk.graal.compiler.nodes.AbstractBeginNode;
import jdk.graal.compiler.nodes.AbstractEndNode;
import jdk.graal.compiler.nodes.AbstractMergeNode;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.EndNode;
import jdk.graal.compiler.nodes.FixedNode;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.FullInfopointNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.MergeNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.PiNode;
import jdk.graal.compiler.nodes.ShortCircuitOrNode;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.UnwindNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.VirtualState;
import jdk.graal.compiler.nodes.calc.ConditionalNode;
import jdk.graal.compiler.nodes.calc.ObjectEqualsNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.extended.LoadHubNode;
import jdk.graal.compiler.nodes.extended.ValueAnchorNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.InstanceOfNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.spi.ValueProxy;
import jdk.graal.compiler.nodes.type.StampTool;
import jdk.graal.compiler.replacements.nodes.MethodHandleWithExceptionNode;
import jdk.vm.ci.meta.ConstantReflectionProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Inlining parity with stock: the IC chain's rep-arm dispatch nodes do not count towards the post-analysis
 * trivial-method limits ({@link InliningUtilities#isTrivialMethod}).
 * <p>
 * A wrapper such as {@code s.toLowerCase(Locale.ROOT)} is trivial in stock. With an IC chain it also holds, per listed
 * rep R, an {@code If(exact R)} arm calling {@code R.m}, plus the chain merge and phi; the extra invoke alone exceeds
 * the "<= 1 invoke" limit, so the wrapper stays out of line where stock inlines it. This class recognises the arms
 * structurally and returns their nodes, which the trivial count skips; everything else is counted as in stock.
 * <p>
 * A rep arm: an {@link IfNode} whose condition is an exact {@link InstanceOfNode} of a rep type (a strict subclass of
 * {@code java.lang.String}) or a class compare ({@code ObjectEquals(GetClass|LoadHub, constant)}) with a rep-type
 * constant, whose true successor is a straight line of begins, one direct invoke of a method declared by a supertype of
 * the tested rep on the arm's own receiver Pi, more begins and an end; the invoke's exception edge (if any) is an
 * {@link ExceptionObjectNode} followed directly by an end or an unwind. Anything else: not an arm (counted). Dispatch
 * nodes: the If and the false successor begin, the arm's fixed nodes, call target and exception path; a merge with
 * exactly one non-dispatch forward end, its phis and that end (the input at the remaining end is the flat value and
 * stays counted); floating nodes used only by dispatch nodes. Frame states are ignored as usages. Target: the
 * discounted count equals the stock count of the flat twin (the method without the chain).
 * <p>
 * Soundness: this changes only which calls the trivial inliner inlines; inlining is semantics-preserving (the inlined
 * copy keeps the arms, their exception edges and frame states). Active only in images with a loaded profile (set at
 * beforeCompilation: SVMHost's analysis-time trivial set is untouched).
 */
public final class RepDispatchAccounting {

    /** Set by {@link StringAnalysisFeature#beforeCompilation} when a profile is loaded. */
    static volatile boolean active;

    /** Resolves the class-compare test's constant (set with {@link #active}; null: the class-compare form is no arm). */
    static volatile ConstantReflectionProvider constantReflection;

    private static final Set<String> ARM_GRAPHS = ConcurrentHashMap.newKeySet();
    private static final Set<String> MADE_TRIVIAL = ConcurrentHashMap.newKeySet();
    /** Recall evidence: graphs with a rep-declared call but no recognised arm (counted as in stock). */
    private static final Set<String> NO_ARM = ConcurrentHashMap.newKeySet();
    /** Recall evidence: graphs with an If on a rep test whose true branch is not an arm shape (counted as in stock). */
    private static final Set<String> TEST_NOT_ARM = ConcurrentHashMap.newKeySet();

    private RepDispatchAccounting() {
    }

    /** The dispatch nodes of {@code graph}'s rep arms, or null when inactive or the graph has no rep arm. */
    public static NodeBitMap dispatchNodes(StructuredGraph graph) {
        if (!active) {
            return null;
        }
        NodeBitMap marked = dispatchNodesOf(graph);
        return redirectSwapNodes(graph, marked);
    }

    /**
     * The Object-declared equals REDIRECT's swap ({@code EqualsMatrixNodePlugin.emitObjectRedirectSwap}) does not count
     * either: the pair {@code r = C(notRare, x, y)}, {@code a = C(notRare, y, x)} with {@code notRare = !(x is an exact
     * String) || !(y instanceof String)}, recognised by shape. A node is discounted only when every usage is a discounted
     * node or the invoke's call target (a shared InstanceOf elsewhere stays counted).
     */
    static NodeBitMap redirectSwapNodes(StructuredGraph graph, NodeBitMap marked) {
        NodeBitMap m = marked;
        for (ShortCircuitOrNode or : graph.getNodes(ShortCircuitOrNode.TYPE)) {
            if (!(or.isXNegated() && or.isYNegated() && or.getX() instanceof InstanceOfNode x && or.getY() instanceof InstanceOfNode y && x.type().isExact() &&
                            !y.type().isExact() && isString(x.type().getType()) && isString(y.type().getType()))) {
                continue;
            }
            List<Node> conds = new ArrayList<>();
            for (Node u : or.usages()) {
                if (u instanceof ConditionalNode c && c.condition() == or &&
                                (c.trueValue() == x.getValue() && c.falseValue() == y.getValue() || c.trueValue() == y.getValue() && c.falseValue() == x.getValue()) &&
                                c.usages().filter(cu -> !(cu instanceof MethodCallTargetNode)).isEmpty()) {
                    conds.add(c);
                } else {
                    conds = null;
                    break;
                }
            }
            if (conds == null || conds.size() != 2) {
                continue;
            }
            if (m == null) {
                m = graph.createNodeBitMap();
            }
            for (Node c : conds) {
                m.mark(c);
            }
            m.mark(or);
            if (x.usages().count() == 1) {
                m.mark(x);
            }
            if (y.usages().count() == 1) {
                m.mark(y);
            }
        }
        return m;
    }

    private static boolean isString(ResolvedJavaType t) {
        return t != null && t.toJavaName().equals("java.lang.String");
    }

    /** The predicate itself (also used by the JUnit test, independent of {@link #active}). */
    static NodeBitMap dispatchNodesOf(StructuredGraph graph) {
        ResolvedJavaMethod own = graph.method();
        if (own != null && isRep(own.getDeclaringClass())) {
            return null;
        }
        boolean anyRepCall = false;
        for (MethodCallTargetNode t : graph.getNodes(MethodCallTargetNode.TYPE)) {
            if (isRep(t.targetMethod().getDeclaringClass()) || AppendMirror.mirrorSlot(t.targetMethod()) >= 0) {
                anyRepCall = true;
                break;
            }
        }
        if (!anyRepCall) {
            return null;
        }
        NodeBitMap marked = graph.createNodeBitMap();
        ArrayDeque<Node> work = new ArrayDeque<>();
        int arms = 0;
        for (IfNode ifNode : graph.getNodes(IfNode.TYPE)) {
            List<Node> armNodes = repArm(ifNode);
            if (armNodes != null) {
                arms++;
                for (Node n : armNodes) {
                    mark(marked, work, n);
                }
            } else if (active && repTest(ifNode.condition()) != null) {
                TEST_NOT_ARM.add(name(graph));
            }
        }
        if (arms == 0) {
            if (active) {
                NO_ARM.add(name(graph));
            }
            return null;
        }
        /* The exact-first String test in front of the arms (ic.exactfirst) is dispatch too */
        for (IfNode ifNode : graph.getNodes(IfNode.TYPE)) {
            List<Node> ef = exactFirstNodes(ifNode, marked);
            if (ef != null) {
                for (Node n : ef) {
                    mark(marked, work, n);
                }
            }
        }
        /*
         * Merges that exist only because of the arms (exactly one forward end is not a dispatch end): without the arms
         * the remaining path flows straight on. A phi's inputs at the dispatch ends are arm values; its input at the
         * remaining end is the flat value, which survives in the flat graph, so it stays counted.
         */
        NodeBitMap keep = graph.createNodeBitMap();
        List<Node> armValues = new ArrayList<>();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (AbstractMergeNode m : graph.getNodes(AbstractMergeNode.TYPE)) {
                if (m instanceof LoopBeginNode || marked.isMarked(m)) {
                    continue;
                }
                int other = 0;
                AbstractEndNode otherEnd = null;
                for (AbstractEndNode e : m.forwardEnds()) {
                    if (!marked.isMarked(e)) {
                        other++;
                        otherEnd = e;
                    }
                }
                if (other == 1) {
                    int flatIndex = m.phiPredecessorIndex(otherEnd);
                    for (PhiNode phi : m.phis()) {
                        marked.mark(phi); // not pushed: only the arm-side inputs propagate
                        for (int i = 0; i < phi.valueCount(); i++) {
                            if (i == flatIndex) {
                                keep.mark(phi.valueAt(i));
                            } else {
                                armValues.add(phi.valueAt(i));
                            }
                        }
                    }
                    mark(marked, work, otherEnd);
                    mark(marked, work, m);
                    changed = true;
                }
            }
        }
        /* floating inputs used only by dispatch nodes (frame states are not counted and are ignored as usages) */
        for (Node v : armValues) {
            markIfOnlyDispatch(marked, keep, work, v);
        }
        while (!work.isEmpty()) {
            Node n = work.pop();
            for (Node in : n.inputs()) {
                markIfOnlyDispatch(marked, keep, work, in);
            }
        }
        return marked;
    }

    private static void markIfOnlyDispatch(NodeBitMap marked, NodeBitMap keep, ArrayDeque<Node> work, Node in) {
        if (in instanceof FixedNode || in instanceof FrameState || in instanceof VirtualState || marked.isMarked(in) || keep.isMarked(in) || in.hasNoUsages()) {
            return;
        }
        for (Node u : in.usages()) {
            if (!(u instanceof FrameState || u instanceof VirtualState) && !marked.isMarked(u)) {
                return;
            }
        }
        mark(marked, work, in);
    }

    private static void mark(NodeBitMap marked, ArrayDeque<Node> work, Node n) {
        if (!marked.isMarked(n)) {
            marked.mark(n);
            work.push(n);
        }
    }

    /** A rep test: the tested rep type and the tested value. */
    record RepTest(ResolvedJavaType type, ValueNode value) {
    }

    /**
     * The fixed dispatch nodes of a rep arm rooted at {@code ifNode}, or null if it is not one. The arm's invoke must be
     * a direct call of a method declared by a supertype of the tested rep, on the arm's own receiver Pi: a {@link PiNode}
     * of the tested value, guarded by a begin of the arm, with the exact tested rep as its stamp (the emitter's shape).
     */
    private static List<Node> repArm(IfNode ifNode) {
        RepTest test = repTest(ifNode.condition());
        if (test == null) {
            return null;
        }
        List<Node> nodes = new ArrayList<>();
        nodes.add(ifNode);
        nodes.add(ifNode.falseSuccessor());
        FixedNode cur = ifNode.trueSuccessor();
        Invoke invoke = null;
        while (true) {
            if (cur instanceof AbstractEndNode) {
                nodes.add(cur);
                break;
            }
            if (cur instanceof Invoke inv && invoke == null && inv.callTarget() instanceof MethodCallTargetNode t && (isRepArmCall(t, test, nodes) || isMirrorArmCall(t, test, nodes))) {
                invoke = inv;
                nodes.add(cur);
                nodes.add(t);
                if (cur instanceof InvokeWithExceptionNode iwe) {
                    if (!(iwe.exceptionEdge() instanceof ExceptionObjectNode eo) || !(eo.next() instanceof AbstractEndNode || eo.next() instanceof UnwindNode)) {
                        return null;
                    }
                    nodes.add(eo);
                    nodes.add(eo.next());
                    cur = iwe.next();
                } else {
                    cur = ((FixedWithNextNode) cur).next();
                }
                continue;
            }
            if (cur instanceof AbstractBeginNode b && !(cur instanceof AbstractMergeNode) && !(cur instanceof ExceptionObjectNode)) {
                nodes.add(cur);
                cur = b.next();
                continue;
            }
            if (cur instanceof ValueAnchorNode a) {
                /* the parser's anchor after a begin (not counted by the stock rule either) */
                nodes.add(cur);
                cur = a.next();
                continue;
            }
            return null;
        }
        return invoke == null ? null : nodes;
    }

    /**
     * Exact-first: the fixed nodes of the IC chain's leading {@code If(x instanceof exact String)}, or null. Its true
     * successor is a straight line of begins into an end of a two-end merge M; its false successor a straight line into
     * an already recognised rep arm on the same x. In the flat twin none of it exists, so the If, both lines, M and its
     * ends are dispatch nodes; the call after M stays counted.
     */
    static List<Node> exactFirstNodes(IfNode ifNode, NodeBitMap marked) {
        if (marked.isMarked(ifNode) || !(ifNode.condition() instanceof InstanceOfNode io) || !io.type().isExact() || !isString(io.type().getType())) {
            return null;
        }
        List<Node> nodes = new ArrayList<>();
        nodes.add(ifNode);
        FixedNode t = ifNode.trueSuccessor();
        while (t instanceof AbstractBeginNode b && !(t instanceof AbstractMergeNode) && !(t instanceof ExceptionObjectNode)) {
            nodes.add(t);
            t = b.next();
        }
        if (!(t instanceof EndNode strEnd) || !(strEnd.merge() instanceof MergeNode m) || m.forwardEndCount() != 2 || m.phis().isNotEmpty()) {
            return null;
        }
        nodes.add(strEnd);
        FixedNode f = ifNode.falseSuccessor();
        while ((f instanceof AbstractBeginNode && !(f instanceof AbstractMergeNode) && !(f instanceof ExceptionObjectNode)) || f instanceof ValueAnchorNode) {
            nodes.add(f);
            f = ((FixedWithNextNode) f).next();
        }
        if (!(f instanceof IfNode first) || !marked.isMarked(first) || repTest(first.condition()) == null || repTest(first.condition()).value() != io.getValue()) {
            return null;
        }
        nodes.add(m);
        for (AbstractEndNode e : m.forwardEnds()) {
            if (e != strEnd) {
                nodes.add(e);
            }
        }
        return nodes;
    }

    /** The IC arm's call: a direct call of a method declared by a supertype of the tested rep, on the arm's rep Pi. */
    private static boolean isRepArmCall(MethodCallTargetNode t, RepTest test, List<Node> armSoFar) {
        return !t.invokeKind().isIndirect() && t.invokeKind().hasReceiver() && t.targetMethod().getDeclaringClass().isAssignableFrom(test.type()) &&
                        isRep(t.targetMethod().getDeclaringClass()) && isArmReceiver(t.arguments().get(0), test, armSoFar);
    }

    /**
     * The builder-append mirror arm's call ({@link AppendMirrorNodePlugin}): a call (direct, or virtual on the builder)
     * of a builder mirror member ({@link AppendMirror#mirrorSlot}) whose string argument is the arm's rep Pi and whose
     * other arguments are not the tested value. In the flat twin the original invoke stays, so the arm is dispatch.
     */
    static boolean isMirrorArmCall(MethodCallTargetNode t, RepTest test, List<Node> armSoFar) {
        int slot = AppendMirror.mirrorSlot(t.targetMethod());
        if (slot < 0 || slot >= t.arguments().size() || t.invokeKind() == jdk.graal.compiler.nodes.CallTargetNode.InvokeKind.Interface || !t.invokeKind().hasReceiver()) {
            return false;
        }
        for (int i = 0; i < t.arguments().size(); i++) {
            if (i != slot && t.arguments().get(i) == test.value()) {
                return false;
            }
        }
        return isArmReceiver(t.arguments().get(slot), test, armSoFar);
    }

    /** The receiver is the arm's rep Pi: of the tested value, guarded by a begin already on the arm, exactly the tested rep. */
    private static boolean isArmReceiver(ValueNode receiver, RepTest test, List<Node> armSoFar) {
        return receiver instanceof PiNode pi && pi.object() == test.value() && pi.getGuard() != null && armSoFar.contains(pi.getGuard().asNode()) &&
                        StampTool.isExactType(pi) && test.type().equals(StampTool.typeOrNull(pi));
    }

    /**
     * The rep test of an If: an exact InstanceOf of a rep type, or a class compare {@code ObjectEquals(GetClass|LoadHub,
     * constant)} whose constant is a rep type (resolved with {@link #constantReflection}; without it the form is not
     * recognised); null if it is neither.
     */
    private static RepTest repTest(LogicNode c) {
        if (c instanceof InstanceOfNode io) {
            return io.type().isExact() && isRep(io.type().getType()) ? new RepTest(io.type().getType(), io.getValue()) : null;
        }
        if (c instanceof ObjectEqualsNode eq) {
            RepTest t = classCompare(eq.getX(), eq.getY());
            return t != null ? t : classCompare(eq.getY(), eq.getX());
        }
        return null;
    }

    private static RepTest classCompare(ValueNode classOf, ValueNode constant) {
        ValueNode tested = classOf instanceof GetClassNode gc ? gc.getObject() : classOf instanceof LoadHubNode lh ? lh.getValue() : null;
        ConstantReflectionProvider cr = constantReflection;
        if (tested == null || !(constant instanceof ConstantNode cn) || cr == null) {
            return null;
        }
        ResolvedJavaType type = cr.asJavaType(cn.asConstant());
        return type != null && isRep(type) ? new RepTest(type, tested) : null;
    }

    private static final ConcurrentHashMap<ResolvedJavaType, Boolean> IS_REP = new ConcurrentHashMap<>();

    /** A rep: a strict subclass of java.lang.String (the defined rep set, not a name list); memoised per type. */
    static boolean isRep(ResolvedJavaType type) {
        if (type == null || type.isInterface() || type.isArray()) {
            return false;
        }
        return IS_REP.computeIfAbsent(type, RepDispatchAccounting::computeIsRep);
    }

    private static boolean computeIsRep(ResolvedJavaType type) {
        for (ResolvedJavaType s = type.getSuperclass(); s != null; s = s.getSuperclass()) {
            if (s.toJavaName().equals("java.lang.String")) {
                return true;
            }
        }
        return false;
    }

    /**
     * The trivial-method count by the stock rule of {@link InliningUtilities#isTrivialMethod}, skipping {@code skip}:
     * {invokes, others}. For the census and the JUnit parity check only.
     */
    static int[] count(StructuredGraph graph, NodeBitMap skip) {
        int invokes = 0;
        int others = 0;
        for (Node n : graph.getNodes()) {
            if (n instanceof StartNode || n instanceof ParameterNode || n instanceof FullInfopointNode || n instanceof ValueProxy || n instanceof ValueAnchorNode || n instanceof FrameState ||
                            skip != null && skip.isMarked(n)) {
                continue;
            }
            if (n instanceof MethodCallTargetNode || n instanceof MethodHandleWithExceptionNode) {
                invokes++;
            } else {
                others++;
            }
        }
        return new int[]{invokes, others};
    }

    /** The census side of the hook: records a graph with rep arms and whether the discount made it trivial. */
    public static boolean census(StructuredGraph graph, boolean trivialWithDiscount) {
        String name = name(graph);
        ARM_GRAPHS.add(name);
        if (trivialWithDiscount && !InliningUtilities.isTrivialMethod(graph, null)) {
            int[] stock = count(graph, null);
            int[] disc = count(graph, dispatchNodesOf(graph));
            MADE_TRIVIAL.add(name + " stock " + stock[0] + "+" + stock[1] + " discounted " + disc[0] + "+" + disc[1]);
        }
        return trivialWithDiscount;
    }

    private static String name(StructuredGraph graph) {
        return graph.method() == null ? graph.toString() : graph.method().format("%H.%n(%p)");
    }

    private static List<String> first(Set<String> set, int n) {
        List<String> out = new ArrayList<>();
        for (String s : new TreeSet<>(set)) {
            if (out.size() == n) {
                break;
            }
            out.add(s);
        }
        return out;
    }

    static String censusLine() {
        List<String> made = first(MADE_TRIVIAL, 20);
        List<String> noArm = first(NO_ARM, 5);
        List<String> testNotArm = first(TEST_NOT_ARM, 5);
        return "[string-analysis] r2-trivial: active=" + active + " graphs with rep arms=" + ARM_GRAPHS.size() + ", made trivial by the discount=" + MADE_TRIVIAL.size() +
                        (made.isEmpty() ? "" : " (first 20: " + made + ")") + "; graphs with a rep call but no recognised arm=" + NO_ARM.size() + (noArm.isEmpty() ? "" : " (first 5: " + noArm + ")") +
                        "; graphs with a rep-test If that is no arm=" + TEST_NOT_ARM.size() + (testNotArm.isEmpty() ? "" : " (first 5: " + testNotArm + ")");
    }
}
