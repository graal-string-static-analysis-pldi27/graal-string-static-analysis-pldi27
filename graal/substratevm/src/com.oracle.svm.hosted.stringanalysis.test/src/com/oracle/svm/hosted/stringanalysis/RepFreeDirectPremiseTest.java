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

import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;

/**
 * Premises of the rep-free direct-call emission that {@code InlineCacheTrivialMethodNodePlugin} implements at
 * {@code INLINE_CACHE UNKNOWN}/{@code EXACT_STRING} sites, checked by reflection over the real classes (as in
 * {@code EqualsTablePremiseTest}).
 */
public class RepFreeDirectPremiseTest {

    /*
     * toString is not in this set — no rep overrides it; its inherited body (aload_0; areturn) is
     * field-free and exactly correct on every receiver (ElseDirectPremiseTest.FIELD_FREE_INHERITED, pinned there).
     */
    private static final Set<String> NON_EQUALS_TRIVIAL = Set.of("length", "charAt", "hashCode", "isEmpty");

    /**
     * The plugin's population is exactly the 7 profiled trivial methods ({@code TRIVIAL_METHODS} of
     * {@code InlineCacheProfilingHeuristic}). Widening it (e.g. {@code compareTo}) is an analysis-side change, never a
     * silent runtime edit, and the parent's emission population must equal the profiled one or sites would silently take
     * the stock path. This pins the plugin's set; a heuristic-side widening moves the profile but not this pin.
     */
    @Test
    public void trivialMethodsPopulationIsExactlyTheSevenProfiledMethods() {
        /* The 7 names are the legacy set; the plugin's population is StringIcMethods (IcWideningPremiseTest). */
        Assert.assertEquals(Set.of("equals", "maybeCustomStringEquals", "length", "hashCode", "charAt", "isEmpty", "toString"),
                        new TreeSet<>(StringIcMethods.LEGACY_TRIVIAL_NAMES));
    }

    /**
     * The trust-exposure boundary is uniform: every {@code value == null} rep overrides every non-equals trivial method,
     * so the one profile error this emission trusts away (a rep at a site the profile calls rep-free) fails identically
     * everywhere: the direct {@code String.<m>} body reads {@code value()} and NPEs. A registry rep that inherits any of
     * the four is at most {@link SingleByteString}, which is value-carrying (its own overrides and the inherited
     * {@code String} body are both safe; pinned by {@code EqualsTablePremiseTest}). The equals family is doubly safe (the
     * patched bodies deflect). So the runtime needs no per-method defense. {@code toString} is outside the exposure set:
     * its rep-free direct lowering is the field-free {@code String.toString}, which gives the exact result on a rep.
     */
    @Test
    public void valueNullExposureIsUniformAcrossTheTrivialPopulation() {
        Set<String> covered = new TreeSet<>(NON_EQUALS_TRIVIAL);
        covered.addAll(ElseDirectPremiseTest.FIELD_FREE_INHERITED);
        covered.add("equals");
        covered.add("maybeCustomStringEquals");
        Assert.assertEquals("every trivial method is exposure-pinned, field-free or the equals family", new TreeSet<>(StringIcMethods.LEGACY_TRIVIAL_NAMES), covered);
        for (String name : NON_EQUALS_TRIVIAL) {
            for (Class<?> rep : RepInheritedBodyTest.VALUE_NULL_REPS) {
                Assert.assertTrue(rep + " must override " + name + " (the value-null exposure premise)",
                                InlineCacheRegistry.repOverrides(rep, name));
            }
            for (var e : InlineCacheRegistry.REP_CLASSES.entrySet()) {
                if (!InlineCacheRegistry.repOverrides(e.getValue(), name)) {
                    Assert.assertSame("only the value-carrying rep may inherit " + name, SingleByteString.class,
                                    e.getValue());
                }
            }
        }
    }
}
