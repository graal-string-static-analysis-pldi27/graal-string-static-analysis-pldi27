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

import jdk.graal.compiler.api.replacements.SnippetReflectionProvider;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.TypeReference;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugins;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Constant-fold disable of the string-analysis child: the child keeps {@code getClass()}/{@code intern()} of a
 * compile-time constant {@code java.lang.String} receiver as real invokes in its analysis IR, so the usage-tracking
 * walk sees them.
 * <p>
 * <b>The gap</b>: a seeded 1-char String literal is a compile-time
 * constant, and its same-frame hazard uses fold away during graph parsing, long before the walk: the production
 * {@code StandardGraphBuilderPlugins} fold {@code lit.getClass()} to a {@code Class} constant
 * ({@code GetClassNode.tryFold}) and {@code lit.intern()} to the receiver itself (a constant is already interned per
 * JLS, so {@code lit.intern() == lit} folds to true). The seeded literal's walk then sees no class
 * check and no intern, so {@code SingleByteHeuristic.hasStrictClassCheck}/{@code reachesIntern} are vacuous, while in the image the
 * replaced literal is a pooled {@code SingleByteString} (not a constant), so the same calls execute and diverge.
 * <p>
 * <b>The disable</b>: {@link #register} overwrites the two production plugins (the last registration wins the lookup)
 * with wrappers that decline (return {@code false}, so the ordinary invoke is emitted) only when the receiver is a
 * compile-time constant {@code String} ({@code StandardGraphBuilderPlugins.asConstantObject}, the exact condition of
 * the production folds). Everything else is identical to production, and no canonicalizer runs between parse and the
 * analysis IR ({@code AnalysisParsedGraph.optimizeAndEncode} only encodes), so a declined invoke cannot fold back.
 * The wrappers replace the plugins in the shared {@code InvocationPlugins}, so every consumer in the child sees them
 * (the parse, and the decode retry inside lambda scopes, {@code StringAnalysisChildInlining.ChildGraphDecoder}).
 * <p>
 * <b>Child-only and narrow</b>: registered only under {@code -H:+StringAnalysisFork}. The parent keeps the production
 * folds, which are sound there: a literal the analysis did not replace stays a constant in the image, and a replaced
 * literal's site no longer holds a constant at run time. So the unsoundness is only ever "the child did not see the
 * use", never "the parent folded something it should not have". Without the wrappers the production folds would hide
 * these uses.
 * In the child only candidate atoms (seeded literals; substrings born at invokes
 * are never constants) can change verdict, and only toward REJECT (more visible uses), the safe direction.
 * <p>
 * The walk then records the kept invokes with no further change: {@code Object.getClass} via
 * {@code SugBuilderV2.classifyInvokeFromFlow} ({@code SugNameTables.isStrictClassCheckName}), {@code String.intern}
 * (retargeted to {@code StringInternSupport.intern}) by its intern branch; and {@code lit.intern() == lit} stays a real
 * {@code ReferenceEqNode}, so the {@code LITERAL_IDENTITY} observation can fire too.
 */
public final class StringAnalysisChildNoFold {

    private StringAnalysisChildNoFold() {
    }

    /** Print-only census ({@code nofold{getClass=N intern=N}}): sites whose fold was declined (JVM-wide, one analysis). */
    public static final AtomicLong DECLINED_INTERN = new AtomicLong();
    public static final AtomicLong DECLINED_GETCLASS = new AtomicLong();

    /**
     * The decline predicate of both wrappers, the classification of the production folds
     * ({@code StandardGraphBuilderPlugins.asConstantObject}): the receiver is a compile-time non-null constant
     * {@code java.lang.String} ({@code asObject} reflects a non-String constant to null; it is not a cast). Pinned by
     * {@code ChildNoFoldTest}.
     */
    public static boolean declinesFold(ValueNode receiver, SnippetReflectionProvider snippetReflection) {
        if (!(receiver instanceof ConstantNode constantNode) || !(constantNode.getValue() instanceof JavaConstant javaConstant) || !javaConstant.isNonNull()) {
            return false;
        }
        return snippetReflection.asObject(String.class, javaConstant) != null;
    }

    /**
     * Overwrites the production {@code String.intern}/{@code Object.getClass} plugins with the declining wrappers
     * (analysis child only; the old plugin stays in the chain, unreachable).
     */
    public static void register(InvocationPlugins plugins) {
        new InvocationPlugins.Registration(plugins, String.class).setAllowOverwrite(true).register(new InvocationPlugin("intern", InvocationPlugin.Receiver.class) {
            @Override
            public boolean apply(GraphBuilderContext b, ResolvedJavaMethod targetMethod, InvocationPlugin.Receiver receiver) {
                if (declinesFold(receiver.get(false), b.getSnippetReflection())) {
                    /* The one case the production plugin folds (a constant String IS its own intern per JLS): keep the invoke. */
                    DECLINED_INTERN.incrementAndGet();
                    return false;
                }
                /* The production plugin declines non-constant receivers too: identical behaviour. */
                return false;
            }
        });
        new InvocationPlugins.Registration(plugins, Object.class).setAllowOverwrite(true).register(new InvocationPlugin("getClass", InvocationPlugin.Receiver.class) {
            @Override
            public boolean apply(GraphBuilderContext b, ResolvedJavaMethod targetMethod, InvocationPlugin.Receiver receiver) {
                ValueNode object = receiver.get(true);
                if (declinesFold(GraphUtil.originalValue(object, true), b.getSnippetReflection())) {
                    /* The seeded-literal hazard shape: keep the invoke (the production plugin would fold an exact-stamp
                     * constant receiver to a Class constant). Non-String constants keep the production behaviour below. */
                    DECLINED_GETCLASS.incrementAndGet();
                    return false;
                }
                /* The production plugin body, unchanged (fold other exact receivers; emit GetClassNode otherwise). */
                ValueNode folded = GetClassNode.tryFold(b.getAssumptions(), b.getMetaAccess(), b.getConstantReflection(), NodeView.DEFAULT,
                                GraphUtil.originalValue(object, true));
                if (folded != null) {
                    b.addPush(JavaKind.Object, folded);
                } else {
                    b.addPush(JavaKind.Object, new GetClassNode(
                                    StampFactory.objectNonNull(TypeReference.createTrusted(b.getAssumptions(), b.getMetaAccess().lookupJavaType(Class.class))), object));
                }
                return true;
            }
        });
        System.out.println("[string-analysis-nofold] child: getClass/intern of constant String receivers stay invokes");
    }
}
