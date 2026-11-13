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

import java.util.concurrent.atomic.AtomicBoolean;

import com.oracle.svm.core.SubstrateOptions;

/**
 * "No-rep image = stock": the gate for a parent whose loaded profile admits no representation
 * ({@link RepresentationProfile#admitsNoRep}). Such a parent mints no rep, so it compiles String as an OFF image does:
 * String calls bound as if String were final ({@link OffStringFinalBindingPlugin}), the representation plugins (IC,
 * equals matrix, {@code StringLengthNodePlugin}, replacement) step aside, and the stock
 * {@code AbstractStringBuilder.appendChars(..., String, ...)} body is kept ({@link RangeCopyRedirectPlugin}). Soundness:
 * the afterAnalysis String-final check (no instantiated strict subtype of String) runs whenever this gate was open.
 * The IC plugin is not gated: with every entry rep-free it emits the stock-bound direct call (an IC gate would have to
 * go before {@code handleInvoke0}: a gate after it, having emitted the lowered call, would make the parser emit the
 * invoke again).
 * <p>
 * Knob {@code svm.stringanalysis.off.stringfinal}: 2 (default) = the binding in OFF and zero-admit images; 1 = OFF only
 * (this gate never opens); 0 = the binding is off.
 */
final class ZeroAdmitStock {

    static final int MODE = Integer.getInteger("svm.stringanalysis.off.stringfinal", 2);

    /** Set once {@link #active} returned true in this build: the String-final subtype check then runs at afterAnalysis. */
    static final AtomicBoolean USED = new AtomicBoolean();

    private ZeroAdmitStock() {
    }

    /** The gate as a pure function (pinned by JUnit). */
    static boolean applies(int mode, boolean fork, RepresentationProfile profile) {
        return mode >= 2 && !fork && profile != null && profile.admitsNoRep();
    }

    /**
     * True iff this is the parent, the knob is 2 and the loaded profile admits no rep. Not cached while no profile is
     * loaded (it is loaded at beforeAnalysis, before the analysis parse).
     */
    static boolean active() {
        boolean a = applies(MODE, SubstrateOptions.StringAnalysisFork.getValue(), RepresentationProfileHolder.getInstance());
        if (a && !USED.get()) {
            USED.set(true);
        }
        return a;
    }
}
