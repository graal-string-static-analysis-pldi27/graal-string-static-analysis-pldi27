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

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration.Plugins;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugins;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The parent's {@code equals} intrinsics: {@code String.maybeCustomStringEquals} (the REDIRECT target) and the
 * {@code equals(Object)} of every rep class, each built by its graph builder.
 */
final class RepEqualsPluginRegistration {

    /** One intrinsic's graph builder; returns false to keep the original call. */
    @FunctionalInterface
    interface EqualsGraph {
        boolean build(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other);
    }

    static void register(Plugins plugins) {
        register(plugins, String.class, "maybeCustomStringEquals", SafeStringEqualsGraphBuilder::buildSafeEqualsGraph);
        register(plugins, StringView.class, "equals", StringViewEqualsGraphBuilder::buildStringViewEqualsGraph);
        register(plugins, RopeString.class, "equals", RopeStringEqualsGraphBuilder::buildRopeStringEqualsGraph);
        register(plugins, ThreeWayString.class, "equals", ThreeWayStringEqualsGraphBuilder::buildThreeWayStringEqualsGraph);
        register(plugins, FixedConcat4.class, "equals", FixedConcat4EqualsGraphBuilder::buildFixedConcat4EqualsGraph);
        register(plugins, ArrayLazyString.class, "equals", ArrayLazyStringEqualsGraphBuilder::buildArrayLazyStringEqualsGraph);
        register(plugins, InterleavedStringArray.class, "equals", InterleavedStringArrayEqualsGraphBuilder::buildInterleavedStringArrayEqualsGraph);
    }

    private static void register(Plugins plugins, Class<?> declaringClass, String name, EqualsGraph graph) {
        InvocationPlugins.Registration r = new InvocationPlugins.Registration(plugins.getInvocationPlugins(), declaringClass);
        r.setAllowOverwrite(true);
        r.register(new InvocationPlugin(name, Receiver.class, Object.class) {
            @Override
            public boolean apply(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode other) {
                return graph.build(b, targetMethod, receiver, other);
            }
        });
    }

    private RepEqualsPluginRegistration() {
    }
}
