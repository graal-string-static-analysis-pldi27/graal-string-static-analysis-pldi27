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

import com.oracle.svm.core.stringrep.SingleByteString;

import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration.Plugins;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugin.Receiver;
import jdk.graal.compiler.nodes.graphbuilderconf.InvocationPlugins;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Intrinsifies the private {@code SingleByteString.exactPoolEntry(String)} (called only with
 * {@code POOL[i]}, pinned by RepHeapPoolTest) into an {@link ExactPoolEntryNode}: no type check in the factories, the
 * exact {@code SingleByteString} type for the analysis and the compiler. Registered for every analysis parse (the
 * factories can be reached whenever a profile or the analysis replaces sites); without it the method's checked cast runs.
 */
final class SingleByteStringPoolPluginRegistration {

    static void register(Plugins plugins) {
        InvocationPlugins.Registration r = new InvocationPlugins.Registration(plugins.getInvocationPlugins(), SingleByteString.class);
        r.register(new InvocationPlugin("exactPoolEntry", String.class) {
            @Override
            public boolean apply(GraphBuilderContext b, ResolvedJavaMethod targetMethod, Receiver receiver, ValueNode poolEntry) {
                b.addPush(JavaKind.Object, new ExactPoolEntryNode(poolEntry, b.getMetaAccess().lookupJavaType(SingleByteString.class)));
                return true;
            }
        });
    }
}
