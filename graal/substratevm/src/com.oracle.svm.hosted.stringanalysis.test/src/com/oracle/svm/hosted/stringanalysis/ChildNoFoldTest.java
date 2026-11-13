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

import java.lang.reflect.Executable;
import java.lang.reflect.Field;

import org.graalvm.collections.EconomicMap;
import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.phases.StringAnalysisChildNoFold;

import jdk.graal.compiler.api.replacements.SnippetReflectionProvider;
import jdk.graal.compiler.core.common.type.StampFactory;
import jdk.graal.compiler.core.common.type.StampPair;
import jdk.graal.compiler.nodes.ConstantNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.extended.GetClassNode;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugins;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.options.OptionValues;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.hotspot.HotSpotObjectConstant;
import jdk.vm.ci.meta.Assumptions;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The {@link StringAnalysisChildNoFold} wrapper (without it a seeded literal's class check folds away at the child's
 * parse). (1) The decline decision {@link StringAnalysisChildNoFold#declinesFold}: the two wrappers keep
 * {@code getClass()}/{@code intern()} as invokes exactly for a compile-time non-null constant {@code String} receiver
 * (the production plugins' own fold condition); a non-constant receiver and a non-String constant receiver run the
 * production body (fold / decline unchanged). (2) The premise: the production {@code getClass} fold
 * ({@code GetClassNode.tryFold}) really fires for a constant String receiver (an exact-stamp constant) — declining is
 * the only way the child keeps that invoke. (3) The registration overwrites the plugin chain head for exactly the two
 * methods ({@code String#intern}, {@code Object#getClass}) and nothing else.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.graal.compiler/jdk.graal.compiler.api.replacements",
                "jdk.graal.compiler/jdk.graal.compiler.graph", "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.options"})
public class ChildNoFoldTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
    private static final OptionValues OPTIONS = new OptionValues(EconomicMap.create());

    /**
     * The snippet reflection of the running HotSpot JVM, the same null-on-mismatch {@code asObject} the production
     * {@code HotSpotSnippetReflectionProvider} applies (a non-String object constant reflects to null, never a cast).
     */
    private static final SnippetReflectionProvider SNIPPETS = new SnippetReflectionProvider() {
        @Override
        public JavaConstant forObject(Object object) {
            return ((jdk.vm.ci.hotspot.HotSpotConstantReflectionProvider) HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection()).forObject(object);
        }

        @Override
        public <T> T asObject(Class<T> type, JavaConstant constant) {
            if (constant instanceof HotSpotObjectConstant hs) {
                return hs.asObject(type);
            }
            return null;
        }

        @Override
        public <T> T getInjectedNodeIntrinsicParameter(Class<T> type) {
            return null;
        }

        @Override
        public Class<?> originalClass(jdk.vm.ci.meta.ResolvedJavaType type) {
            return null;
        }

        @Override
        public Executable originalMethod(ResolvedJavaMethod method) {
            return null;
        }

        @Override
        public Field originalField(jdk.vm.ci.meta.ResolvedJavaField field) {
            return null;
        }
    };

    @Test
    public void declinesExactlyConstantStringReceivers() {
        // the decline: a compile-time non-null constant String (the seeded literal's birth)
        ValueNode lit = ConstantNode.forConstant(HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection().forString("x"), META);
        Assert.assertTrue("a constant String receiver: the fold is declined, the invoke stays in the child IR",
                        StringAnalysisChildNoFold.declinesFold(lit, SNIPPETS));
        // the production body: a non-constant receiver (a parameter, the substring twin's birth)
        ValueNode param = new ParameterNode(0, StampPair.createSingle(StampFactory.object()));
        Assert.assertFalse("a non-constant receiver keeps the production plugin behaviour",
                        StringAnalysisChildNoFold.declinesFold(param, SNIPPETS));
        // the production body: non-String constants (an Integer object constant, a null constant, an int constant)
        ValueNode boxed = ConstantNode.forConstant(SNIPPETS.forObject(42), META);
        Assert.assertFalse("a non-String object constant (Integer) keeps the production fold",
                        StringAnalysisChildNoFold.declinesFold(boxed, SNIPPETS));
        ValueNode nul = ConstantNode.forConstant(JavaConstant.NULL_POINTER, META);
        Assert.assertFalse("a null constant receiver", StringAnalysisChildNoFold.declinesFold(nul, SNIPPETS));
        Assert.assertFalse("a primitive constant", StringAnalysisChildNoFold.declinesFold(ConstantNode.forInt(1), SNIPPETS));
        Assert.assertFalse("no receiver at all", StringAnalysisChildNoFold.declinesFold(null, SNIPPETS));
    }

    @Test
    public void productionGetClassFoldReallyFiresForAConstantStringReceiver() throws Exception {
        // the premise: without the decline, lit.getClass() folds at the child's parse (an exact-stamp
        // constant receiver) and the class-check usage never exists (unsound with a seeded literal)
        ValueNode lit = ConstantNode.forConstant(HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection().forString("c"), META);
        ValueNode folded = GetClassNode.tryFold(new Assumptions(), META,
                        HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection(), NodeView.DEFAULT, lit);
        Assert.assertNotNull("GetClassNode.tryFold folds a constant String receiver (why the wrapper must decline it)", folded);
        // and for the non-String constant the wrapper declines nothing: the production fold applies there too
        ValueNode boxed = ConstantNode.forConstant(SNIPPETS.forObject(42), META);
        Assert.assertNotNull("an Integer constant receiver folds exactly as in production",
                        GetClassNode.tryFold(new Assumptions(), META,
                                        HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection(), NodeView.DEFAULT, boxed));
        // a non-constant receiver never folds: the production plugin emits a GetClassNode, the wrapper is identical there
        ValueNode param = new ParameterNode(0, StampPair.createSingle(StampFactory.object()));
        Assert.assertNull(GetClassNode.tryFold(new Assumptions(), META,
                        HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection(), NodeView.DEFAULT, param));
    }

    @Test
    public void registrationOverwritesExactlyTheTwoPlugins() throws Exception {
        InvocationPlugins plugins = new InvocationPlugins();
        StringAnalysisChildNoFold.register(plugins);
        // the two wrappers sit at the HEAD of their chains (setAllowOverwrite): the lookup finds them, not a
        // production plugin registered earlier on the same instance
        InvocationPlugin intern = plugins.lookupInvocation(method(String.class, "intern"), OPTIONS);
        Assert.assertNotNull("String#intern is registered", intern);
        Assert.assertEquals("the String#intern head is the nofold wrapper", "com.oracle.svm.hosted.phases.StringAnalysisChildNoFold$1",
                        intern.getClass().getName());
        InvocationPlugin getClass = plugins.lookupInvocation(method(Object.class, "getClass"), OPTIONS);
        Assert.assertNotNull("Object#getClass is registered", getClass);
        Assert.assertEquals("the Object#getClass head is the nofold wrapper", "com.oracle.svm.hosted.phases.StringAnalysisChildNoFold$2",
                        getClass.getClass().getName());
        // nothing else is touched (a fresh instance: no other method has any plugin)
        Assert.assertNull("String#equals is not registered by the nofold registration",
                        plugins.lookupInvocation(method(String.class, "equals", Object.class), OPTIONS));
        Assert.assertNull("String#hashCode is not registered by the nofold registration",
                        plugins.lookupInvocation(method(String.class, "hashCode"), OPTIONS));
        Assert.assertNull("Object#toString is not registered by the nofold registration",
                        plugins.lookupInvocation(method(Object.class, "toString"), OPTIONS));
    }

    private static ResolvedJavaMethod method(Class<?> holder, String name, Class<?>... params) throws NoSuchMethodException {
        return META.lookupJavaMethod(holder.getDeclaredMethod(name, params));
    }
}
