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
package com.oracle.svm.hosted.phases;

import java.util.concurrent.atomic.AtomicLong;

import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.HostedProviders;
import com.oracle.graal.pointsto.phases.InlineBeforeAnalysisPolicy;
import com.oracle.svm.core.ParsingReason;
import com.oracle.svm.hosted.SVMHost;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.FixedWithNextNode;
import jdk.graal.compiler.nodes.FrameState;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InlineInvokePlugin.InlineInfo;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Inline-before-analysis of the string-analysis child: the child's IR of a lambda capture is the IR the production
 * pipeline makes of it.
 * <p>
 * The child decodes with {@link InlineBeforeAnalysisPolicy#NO_INLINING} so that user calls such as {@code substring}
 * survive as invokes. A lambda capture parses into a call of the {@code Invokers$Holder.linkToTargetMethod} adapter
 * with the call-site target as a constant appendix; the production policy ({@link InlineBeforeAnalysisPolicyImpl})
 * inlines it as a method-handle intrinsification root, folding it into the lambda allocation plus constructor call.
 * Under NO_INLINING the child would analyze SVM's method-handle interpreter instead, a sound but much coarser model.
 * <p>
 * {@link Policy} keeps NO_INLINING everywhere except inside a method-handle intrinsification scope rooted at the
 * adapter call of a {@code LambdaMetafactory.metafactory/altMetafactory} site, where it takes the production decision
 * unchanged (same rules, limits and plugins). A scope that cannot complete leaves the adapter call (the production
 * rule) on the conservative NO_INLINING path. No other method-handle root (string concat, records, pattern
 * {@code switch}, constant {@code MethodHandle.invoke*}, {@code VarHandle}) is intrinsified. This is the production
 * compilation of the same bytecode, not a model of the JDK.
 * <p>
 * Invokes left by an inlined scope keep their inner bci, while points-to positions them at the root call
 * ({@code MethodTypeFlowBuilder.getInvokePosition}); {@link #pointsToBci} is that position, and the string analysis
 * keys such invokes by it ({@code SugBuilderV2.invokeFlowAt}: where the root bci holds several invoke flows, or a flow
 * of another target, such an invoke gets no flow and no LFG vertex).
 * <p>
 * Used only in the child; the parent's policy is untouched.
 */
public final class StringAnalysisChildInlining {

    private StringAnalysisChildInlining() {
    }

    /**
     * Print-only census ({@code lambdaparity{roots=N}}): adapter calls admitted as scope roots. JVM-wide, which is one
     * analysis in the child process.
     */
    public static final AtomicLong ROOTS = new AtomicLong();

    private static final String LAMBDA_METAFACTORY = "java.lang.invoke.LambdaMetafactory";

    /**
     * Is the instruction at {@code bci} of {@code method} an {@code invokedynamic} whose bootstrap is
     * {@code LambdaMetafactory.metafactory} or {@code altMetafactory} (a lambda or method-reference capture)?
     */
    public static boolean isLambdaMetafactorySite(ResolvedJavaMethod method, int bci) {
        try {
            ResolvedJavaMethod raw = method instanceof AnalysisMethod am ? am.getWrapped() : method;
            byte[] code = raw.getCode();
            if (code == null || bci < 0 || bci >= code.length) {
                return false;
            }
            BytecodeStream s = new BytecodeStream(code);
            s.setBCI(bci);
            if (s.currentBC() != Bytecodes.INVOKEDYNAMIC) {
                return false;
            }
            ConstantPool.BootstrapMethodInvocation bmi = raw.getConstantPool().lookupBootstrapMethodInvocation(s.readCPI4(), Bytecodes.INVOKEDYNAMIC);
            ResolvedJavaMethod boot = bmi != null ? bmi.getMethod() : null;
            return boot != null && LAMBDA_METAFACTORY.equals(boot.getDeclaringClass().toJavaName(true)) &&
                            ("metafactory".equals(boot.getName()) || "altMetafactory".equals(boot.getName()));
        } catch (Throwable t) {
            return false; // unreadable: no scope (the NO_INLINING IR)
        }
    }

    /**
     * The bci at which points-to positions an invoke ({@code MethodTypeFlowBuilder.getInvokePosition}): the outermost
     * caller of its node source position, else of its frame state (the root call for an invoke left by an inlined
     * scope); otherwise {@code Invoke.bci()}.
     */
    public static int pointsToBci(Invoke inv) {
        NodeSourcePosition p = inv.asNode().getNodeSourcePosition();
        if (p != null && p.getCaller() != null) {
            while (p.getCaller() != null) {
                p = p.getCaller();
            }
            return p.getBCI();
        }
        FrameState fs = inv.stateAfter();
        if (fs != null && fs.outerFrameState() != null) {
            while (fs.outerFrameState() != null) {
                fs = fs.outerFrameState();
            }
            return fs.bci;
        }
        return inv.bci();
    }

    /**
     * Was {@code inv} left by an inlined scope, i.e. is its points-to position a caller's call site (a node source
     * position with a caller, or an outer frame state)? This is broader than the lambda-capture scopes
     * this class opens: it is true for every invoke that inlining left in the graph, parse-time inlining included (e.g.
     * through an {@code InlineInvokePlugin} of the replacements, {@code NativeImageGenerator}), whatever its target. So
     * every consumer that keys an invoke by {@link #pointsToBci} must apply the call-site identity rule to these invokes
     * ({@code SugBuilderV2.invokeFlowAt}; the target resolution {@code ForwardFixpoint.callFlowAt}), and
     * must not assume that their targets are statically bound.
     */
    public static boolean isFromInlinedScope(Invoke inv) {
        NodeSourcePosition p = inv.asNode().getNodeSourcePosition();
        if (p != null && p.getCaller() != null) {
            return true;
        }
        FrameState fs = inv.stateAfter();
        return fs != null && fs.outerFrameState() != null;
    }

    /**
     * NO_INLINING, except inside a method-handle intrinsification scope rooted at a lambda-capture site, where the
     * production policy decides.
     */
    public static final class Policy extends InlineBeforeAnalysisPolicy {
        private final InlineBeforeAnalysisPolicyImpl production;

        public Policy(SVMHost hostVM, InlineBeforeAnalysisPolicyUtils inliningUtils) {
            /* The production node plugin (InlineBeforeAnalysisPolicyImpl), active inside the scopes only. */
            super(new NodePlugin[]{new InsideScopes(new ConstantFoldLoadFieldPlugin(ParsingReason.PointsToAnalysis))});
            this.production = new InlineBeforeAnalysisPolicyImpl(hostVM, inliningUtils);
        }

        @Override
        protected boolean shouldInlineInvoke(GraphBuilderContext b, AbstractPolicyScope policyScope, AnalysisMethod method, ValueNode[] args) {
            if (policyScope == null) {
                /*
                 * A call of the decoded method itself: only the adapter at a lambda-capture site opens a scope. The site
                 * is read from the root method's bytecode at b.bci(); for an adapter call inside parse-time-inlined code
                 * that bci is an inner one (of the inlined method), so the check may read an unrelated instruction. That
                 * fails safe: a non-indy or non-LMF instruction opens no scope (the conservative NO_INLINING
                 * path), and at worst a concat adapter is intrinsified as in the parent, which the string layer's own
                 * recogniser refuses when it cannot read the site.
                 */
                if (!InlineBeforeAnalysisPolicyUtils.isMethodHandleIntrinsificationRoot(method) || !isLambdaMetafactorySite(b.getMethod(), b.bci())) {
                    return false;
                }
                boolean inline = production.shouldInlineInvoke(b, null, method, args);
                if (inline) {
                    ROOTS.incrementAndGet();
                }
                return inline;
            }
            if (!(policyScope instanceof InlineBeforeAnalysisPolicyUtils.AccumulativeInlineScope scope) || !scope.accumulativeCounters.inMethodHandleIntrinsification()) {
                /* Below a callee that is not part of the method-handle apparatus (e.g. the lambda's constructor). */
                return false;
            }
            return production.shouldInlineInvoke(b, policyScope, method, args);
        }

        @Override
        protected InlineInfo createInvokeInfo(AnalysisMethod method) {
            return production.createInvokeInfo(method);
        }

        @Override
        protected boolean needsExplicitExceptions() {
            return production.needsExplicitExceptions();
        }

        @Override
        protected boolean tryInvocationPlugins() {
            /* Retried inside the scopes only: ChildGraphDecoder#tryInvocationPlugin. */
            return production.tryInvocationPlugins();
        }

        @Override
        protected FixedWithNextNode processInvokeArgs(AnalysisMethod targetMethod, FixedWithNextNode insertionPoint, ValueNode[] arguments, NodeSourcePosition sourcePosition) {
            return production.processInvokeArgs(targetMethod, insertionPoint, arguments, sourcePosition);
        }

        @Override
        protected AbstractPolicyScope createRootScope() {
            return production.createRootScope();
        }

        @Override
        protected AbstractPolicyScope openCalleeScope(AbstractPolicyScope outer, AnalysisMethod caller, AnalysisMethod method) {
            return production.openCalleeScope(outer, caller, method);
        }

        @Override
        protected boolean shouldOmitIntermediateMethodInState(AnalysisMethod method) {
            return production.shouldOmitIntermediateMethodInState(method);
        }
    }

    /** The graph decoder of the child: invocation plugins are retried inside inlined scopes only. */
    public static final class ChildGraphDecoder extends InlineBeforeAnalysisGraphDecoderImpl {
        public ChildGraphDecoder(BigBang bb, Policy policy, StructuredGraph graph, HostedProviders providers) {
            super(bb, policy, graph, providers);
        }

        @Override
        protected boolean tryInvocationPlugin(PEMethodScope methodScope, LoopScope loopScope, InvokeData invokeData, MethodCallTargetNode callTarget) {
            /* At depth 0 (the decoded method itself) NO_INLINING retries none. */
            return methodScope.isInlinedMethod() && super.tryInvocationPlugin(methodScope, loopScope, invokeData, callTarget);
        }
    }

    /** A node plugin applied inside inlined scopes only (depth > 0); at depth 0 NO_INLINING applies none. */
    private static final class InsideScopes implements NodePlugin {
        private final NodePlugin delegate;

        InsideScopes(NodePlugin delegate) {
            this.delegate = delegate;
        }

        @Override
        public boolean handleLoadField(GraphBuilderContext b, ValueNode object, ResolvedJavaField field) {
            return b.getDepth() > 0 && delegate.handleLoadField(b, object, field);
        }

        @Override
        public boolean handleLoadStaticField(GraphBuilderContext b, ResolvedJavaField field) {
            return b.getDepth() > 0 && delegate.handleLoadStaticField(b, field);
        }
    }
}
