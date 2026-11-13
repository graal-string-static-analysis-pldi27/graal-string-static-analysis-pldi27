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

import com.oracle.graal.pointsto.meta.AnalysisMethod;

import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Site keys shared by the analysis child and the parent: the profile key of a bytecode site
 * ({@code Class#method(descriptor)@bci}) and the parameter-type signature format of a method.
 */
final class SiteKeys {

    private SiteKeys() {
    }

    static final String UNKNOWN_KEY = "<unknown>#<unknown>@-1";

    static String profileKey(ResolvedJavaMethod method, int bci) {
        if (method == null) {
            return UNKNOWN_KEY;
        }
        try {
            return method.getDeclaringClass().toJavaName(true) + "#" + method.getName() +
                            method.getSignature().toMethodDescriptor() + "@" + bci;
        } catch (Throwable t) {
            return UNKNOWN_KEY;
        }
    }

    static String sourceKey(Object src) {
        if (src instanceof BytecodePosition pos && pos.getMethod() instanceof AnalysisMethod am) {
            return profileKey(am, pos.getBCI());
        }
        return null;
    }

    /** The class part of a site key ({@code Class#method(descriptor)@bci}). */
    static String classOf(String key) {
        int h = key.indexOf('#');
        return h < 0 ? key : key.substring(0, h);
    }

    /** A hidden class (lambda or other hidden class) by its name. */
    static boolean isHidden(String cls) {
        return cls.contains("/0x") || cls.contains("$$Lambda");
    }

    static String formatSignature(AnalysisMethod m) {
        StringBuilder sb = new StringBuilder();
        var sig = m.getSignature();
        int n = sig.getParameterCount(false);
        for (int i = 0; i < n; i++) {
            if (i > 0) {
                sb.append(",");
            }
            sb.append(sig.getParameterType(i, null).getName());
        }
        return sb.toString();
    }
}
