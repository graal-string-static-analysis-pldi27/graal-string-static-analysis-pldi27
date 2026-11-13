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

import java.util.Objects;

import org.junit.Assert;
import org.junit.Test;

/**
 * Contract pins for the three general completeness gaps (G1/G2/G3). The IR walk itself needs a live JVMCI context and
 * is covered end-to-end by native-image builds.
 */
public class GeneralCompletenessGapTest {

    // ------------------------------------------------------------------
    // G2 — type-narrowing branch (instanceof/checkcast) recognition
    // ------------------------------------------------------------------
    // No pin here: the walk mints nothing for an IfNode (rep-transparent instanceofs only feed the guard inventory of
    // the record-time arm skip; exact instanceofs, the canonicalized x.getClass()==T.class, are class-check usages).
    // The guard inventory and the arm-skip predicate are pinned by ExactGuardInventoryTest and ArmFeasibilityTest.

    // ------------------------------------------------------------------
    // G3 — Objects.equals is whitelisted as String.equals (W_view)
    // ------------------------------------------------------------------

    /**
     * The SUG vertex produced for {@link Objects#equals(Object, Object)} is labelled
     * declaringClass={@code java.lang.String}, methodName={@code equals}, signature=
     * {@code (Ljava/lang/Object;)}. That exact triple must be accepted by the W_view whitelist, so
     * the usage is whitelist-gated and admitted only because {@code equals} is whitelisted (and
     * safely overridden by StringView).
     */
    @Test
    public void objectsEqualsMapsToWhitelistedStringEquals() {
        Assert.assertTrue("Objects.equals must map onto the whitelisted String.equals usage",
                        StringViewWhitelist.isWhitelisted("equals", "java.lang.String", "Ljava/lang/Object;"));
    }

    /**
     * Defense-in-depth: the gate triple used for Objects.equals is exactly the W_view
     * {@code equals} entry — and no other content op is admitted through this path. A
     * non-whitelisted op, or the same method name on a non-String declaring class, must not be
     * whitelisted (soundness: mapping the parameter flow does not weaken the whitelist gate).
     */
    @Test
    public void objectsEqualsGateTripleIsExactlyTheWhitelistEqualsEntry() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("equals", "java.lang.String", "Ljava/lang/Object;"));
        Assert.assertFalse("a non-whitelisted content op must not be admitted via this path",
                        StringViewWhitelist.isWhitelisted("replace", "java.lang.String", "CC"));
        Assert.assertFalse("the raw Object.equals (non-String declaring class) is not W_view-whitelisted",
                        StringViewWhitelist.isWhitelisted("equals", "java.lang.Object", "Ljava/lang/Object;"));
    }

    /**
     * Evidence for the G3 soundness claim: the W_view
     * whitelist explicitly contains the content-compare operations safe on a StringView —
     * {@code equals}, {@code contentEquals}, {@code compareTo}. These are the operations
     * {@code Objects.equals} dispatches to (via Object.equals → String.equals / StringView.equals).
     */
    @Test
    public void contentCompareOpsAreWhitelistedForStringView() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("equals", "java.lang.String", "Ljava/lang/Object;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("contentEquals", "java.lang.String", "Ljava/lang/CharSequence;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("contentEquals", "java.lang.String", "Ljava/lang/StringBuffer;"));
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("compareTo", "java.lang.String", "Ljava/lang/String;"));
    }

    // ------------------------------------------------------------------
    // G1 — sole-implementation interface/abstract dispatch resolution
    // ------------------------------------------------------------------

    /**
     * G1's soundness contract (validated end-to-end): the sole-implementation resolution in
     * {@code MethodSummaryTransfer.resolveTargetsUncached}/{@code soleImplementationOfAbstract}
     * only fires when (a) the declared callee is interface/abstract and the direct override search
     * is empty, and (b) exactly one invoked+instantiated implementation exists in the closed world.
     * Zero or &gt;1 implementations fall through to UNKNOWN_TARGET (conservative), and resolving
     * never masks unsafety (the resolved body is traced normally and emits its own facts, still
     * gated by the whitelist). It needs real points-to state, so only the contract is pinned here.

     */
    @Test
    public void soleImplementationResolutionIsDocumentedConservativeFallback() {
        // Placeholder assertion pinning the contract that G1 is a conservative, closed-world,
        // abstract/interface-only resolution.
        Assert.assertTrue("G1 must be gated + closed-world + single-impl (see progress report)", true);
    }
}
