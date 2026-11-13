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

import java.lang.reflect.Method;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;

/**
 * Premise pins: the soundness premises of the equals/`maybeCustomStringEquals` lowering table that
 * `InlineCacheTrivialMethodNodePlugin` implements at `EQUALS_MATRIX REDIRECT` sites — the same
 * reflection-over-the-real-classes pattern as `RepInheritedBodyTest.everyValueNullRepOverridesCompareTo`.
 */
public class EqualsTablePremiseTest {

    /**
     * Every {@code value == null} rep overrides {@code maybeCustomStringEquals(Object)} ({@code return
     * this.equals(that)}), so a chain branch (special invoke) and the virtual residual both dispatch to the rep's
     * own equals — the inherited {@code String.maybeCustomStringEquals} fast path would NPE on the null
     * {@code value()}. {@link SingleByteString} is the one registry rep that does not override it: it keeps a real
     * {@code value[]}, the premise that lets it take the direct {@code String.maybeCustomStringEquals} else-branch (and
     * the single direct call when it is the only listed rep).

     */
    @Test
    public void everyValueNullRepOverridesMaybeCustomStringEquals() throws NoSuchMethodException {
        Method mCse = String.class.getDeclaredMethod("maybeCustomStringEquals", Object.class);
        for (Class<?> rep : RepInheritedBodyTest.VALUE_NULL_REPS) {
            Assert.assertSame(rep + " must override maybeCustomStringEquals",
                            rep, RepInheritedBodyTest.implementingClass(rep, mCse));
        }
        Assert.assertSame("SingleByteString must inherit String.maybeCustomStringEquals (it keeps value set)",
                        String.class, RepInheritedBodyTest.implementingClass(SingleByteString.class, mCse));
    }

    /**
     * The branch table the plugin builds at a REDIRECT site: the reps that get their own special-invoke branch on
     * the `maybeCustomStringEquals` override are exactly the six value-null reps; every other registry rep (today
     * only SBS) is a non-overrider and is covered by the direct `String.maybeCustomStringEquals` else-branch. A
     * rep that starts or stops overriding moves this pin — and the emitted table with it.
     */
    @Test
    public void maybeCustomStringEqualsBranchTableIsExactlyTheValueNullReps() {
        for (var e : InlineCacheRegistry.REP_CLASSES.entrySet()) {
            boolean valueNull = RepInheritedBodyTest.VALUE_NULL_REPS.contains(e.getValue());
            Assert.assertEquals(e.getKey() + " branch = overrides && value-null",
                            valueNull, InlineCacheRegistry.repOverrides(e.getValue(), "maybeCustomStringEquals"));
        }
    }
}
