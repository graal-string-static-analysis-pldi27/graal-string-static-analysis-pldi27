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

import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.graal.RuntimeCompilation;

import jdk.graal.compiler.nodes.CallTargetNode.InvokeKind;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The builder JDK keeps the stock {@code AbstractStringBuilder.appendChars(byte[],byte,int,String,int,int)} (it reads
 * {@code s.value()}) and carries the ranged copy as the added twin {@code appendCharsRangeCopy} (copying through the
 * protected {@code String.getBytes(byte[],int,int,byte,int)}, which the reps override). This plugin redirects the only
 * call, in {@code append(CharSequence,int,int)}, to the twin wherever a rep may reach it:
 * <ul>
 * <li>the analysis child (it walks the twin, so its site keys are the twin's, as the parent's);</li>
 * <li>every parent where the "no rep exists" premise is not checked: the stock body is kept only where the
 * afterAnalysis subtype check of the OFF String binding (no instantiated strict subtype of String, fail-closed) is
 * guaranteed to run, i.e. {@link OffStringFinalBindingPlugin} is registered or {@link ZeroAdmitStock} applies.
 * Everything else redirects, a parse before the profile load included;</li>
 * <li>every image with runtime compilation: the analysis and {@code JITCompilation} parses always redirect, so a
 * runtime-compiled graph never gets the stock body with reps present.</li>
 * </ul>
 * Knob {@code svm.stringanalysis.xd.rangecopy}: 1 (default) = as above; 2 = redirect in every image (OFF included).
 * There is no "never" setting: a value-null rep must not reach {@code s.value()}.
 */
public final class RangeCopyRedirectPlugin implements NodePlugin {

    static final int MODE = Integer.getInteger("svm.stringanalysis.xd.rangecopy", 1);

    static final String ASB = "java.lang.AbstractStringBuilder";
    static final String NAME = "appendChars";
    static final String TWIN = "appendCharsRangeCopy";
    static final String DESCRIPTOR = "([BBILjava/lang/String;II)[B";

    private volatile ResolvedJavaMethod twin;

    /** The effective mode of this build: 2 whenever runtime compilation is enabled. */
    static int mode() {
        return RuntimeCompilation.isEnabled() ? 2 : MODE;
    }

    /**
     * The redirect decision (pure): the stock body only in a parent whose String-subtype check is guaranteed (the OFF
     * String binding registered, or {@link ZeroAdmitStock#applies}).
     */
    static boolean redirects(int mode, boolean fork, boolean offR5Registered, boolean zeroAdmitApplies) {
        if (mode == 2 || fork) {
            return true; // the child always walks the twin: its keys and its "no raw value() read" premise
        }
        return !(offR5Registered || zeroAdmitApplies);
    }

    @Override
    public boolean handleInvoke(GraphBuilderContext b, ResolvedJavaMethod method, ValueNode[] args) {
        if (InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, method)) {
            return false; // the uniform first check of every string-analysis node plugin
        }
        if (!NAME.equals(method.getName()) || !method.isStatic() || !ASB.equals(method.getDeclaringClass().toJavaName()) ||
                        !DESCRIPTOR.equals(method.getSignature().toMethodDescriptor())) {
            return false;
        }
        /* ZeroAdmitStock.active (not applies): it marks the build for the afterAnalysis String-subtype check */
        if (!redirects(mode(), SubstrateOptions.StringAnalysisFork.getValue(), OffStringFinalBindingPlugin.offRegistered, ZeroAdmitStock.active())) {
            return false;
        }
        ResolvedJavaMethod t = resolveTwin(method.getDeclaringClass());
        if (t == null) {
            return false; // a builder JDK without the twin (pre-xd): its appendChars is the ranged copy itself
        }
        b.handleReplacedInvoke(InvokeKind.Static, t, args, false);
        return true;
    }

    private ResolvedJavaMethod resolveTwin(ResolvedJavaType asb) {
        ResolvedJavaMethod t = twin;
        if (t == null) {
            for (ResolvedJavaMethod m : asb.getDeclaredMethods(false)) {
                if (TWIN.equals(m.getName()) && m.isStatic() && DESCRIPTOR.equals(m.getSignature().toMethodDescriptor())) {
                    t = m;
                    twin = m;
                    break;
                }
            }
        }
        return t;
    }
}
