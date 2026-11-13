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

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.TransferFacts.IncompleteReason;

/**
 * The world-top rule (R1 in the messages) and the caller-less rule (R3), as the pure decision functions the engine
 * calls.

 */
public class WorldTopRuleTest {

    /** The world-top predicate: every source of an unmodelled outside caller counts; none of them = not world-top. */
    @Test
    public void outsideCallerPredicate() {
        Assert.assertFalse(WorldTopRule.outsideCallerPredicate(false, false, false, false, false));
        Assert.assertTrue("native entry point", WorldTopRule.outsideCallerPredicate(true, false, false, false, false));
        Assert.assertTrue("direct root, any reason (the conservative first-reason reading)", WorldTopRule.outsideCallerPredicate(false, true, false, false, false));
        Assert.assertTrue("virtual root (JNI instance method, hole 3)", WorldTopRule.outsideCallerPredicate(false, false, true, false, false));
        Assert.assertTrue("reached through a virtual root's dispatch (holes 3/4/5)", WorldTopRule.outsideCallerPredicate(false, false, false, true, false));
        Assert.assertTrue("address-taken: a MethodPointer target", WorldTopRule.outsideCallerPredicate(false, false, false, false, true));
    }

    /** World-top rule, forward: an outside caller refuses WORLD_TOP_EXIT whatever the direct callers. */
    @Test
    public void worldTopExitWhateverTheDirectCallers() {
        Assert.assertEquals(RTrackRefusal.WORLD_TOP_EXIT, WorldTopRule.returnExitRefusal(true, 0));
        Assert.assertEquals("with direct callers too (hole 1b)", RTrackRefusal.WORLD_TOP_EXIT, WorldTopRule.returnExitRefusal(true, 3));
    }

    /** Caller-less rule: no caller and not world-top refuses NO_CALLER_EXIT. */
    @Test
    public void noCallerExit() {
        Assert.assertEquals(RTrackRefusal.NO_CALLER_EXIT, WorldTopRule.returnExitRefusal(false, 0));
        Assert.assertNull("callers, not world-top: the plain fan", WorldTopRule.returnExitRefusal(false, 1));
    }

    /** World-top rule, backward: WORLD_TOP_ENTRY regardless of the direct callers; DARK_ENTRY otherwise. */
    @Test
    public void worldTopEntryWhateverTheDirectCallers() {
        Assert.assertEquals(RTrackRefusal.WORLD_TOP_ENTRY, WorldTopRule.parameterEntryRefusal(true, 0));
        Assert.assertEquals("with direct callers (hole 2)", RTrackRefusal.WORLD_TOP_ENTRY, WorldTopRule.parameterEntryRefusal(true, 5));
        Assert.assertEquals("not world-top, no caller", RTrackRefusal.DARK_ENTRY, WorldTopRule.parameterEntryRefusal(false, 0));
        Assert.assertNull("not world-top, callers: the fan only", WorldTopRule.parameterEntryRefusal(false, 2));
    }

    /** The names are named refusals of the non-budget class; each exit shares its entry twin's verdict class. */
    @Test
    public void refusalClasses() {
        Assert.assertFalse(RTrackRefusal.WORLD_TOP_EXIT.budgetClass);
        Assert.assertFalse(RTrackRefusal.NO_CALLER_EXIT.budgetClass);
        Assert.assertEquals(RTrackRefusal.WORLD_TOP_ENTRY.verdictReason(), RTrackRefusal.WORLD_TOP_EXIT.verdictReason());
        Assert.assertEquals(RTrackRefusal.DARK_ENTRY.verdictReason(), RTrackRefusal.NO_CALLER_EXIT.verdictReason());
        Assert.assertEquals(IncompleteReason.INCOMPLETE_TRAVERSAL, RTrackRefusal.NO_CALLER_EXIT.verdictReason());
        // appended after the older names, so the enum order of every earlier name (the printed order) is unchanged
        Assert.assertEquals(RTrackRefusal.THREAD_LOCAL_UNMODELLED.ordinal() + 1, RTrackRefusal.WORLD_TOP_EXIT.ordinal());
        Assert.assertEquals(RTrackRefusal.WORLD_TOP_EXIT.ordinal() + 1, RTrackRefusal.NO_CALLER_EXIT.ordinal());
    }

    /**
     * Address-pending mode 0: a pending slot is skipped only for an exact allowlisted (declaring class, field); every
     * listed entry exists.
     */
    @Test
    public void pendingAllowlistIsExactAndPresent() {
        Assert.assertTrue(WorldTopRule.pendingAllowlisted("com.oracle.svm.core.jni.access.JNIAccessibleMethod", "nonvirtualTarget"));
        Assert.assertTrue(WorldTopRule.pendingAllowlisted("com.oracle.svm.core.jni.access.JNIAccessibleMethod", "valistNonvirtualWrapper"));
        Assert.assertTrue(WorldTopRule.pendingAllowlisted("com.oracle.svm.core.c.BoxedRelocatedPointer", "pointer"));
        Assert.assertTrue("the class wildcard", WorldTopRule.pendingAllowlisted("com.oracle.svm.core.code.ImageCodeInfo", "codeStart"));
        Assert.assertFalse("another field of a listed class", WorldTopRule.pendingAllowlisted("com.oracle.svm.core.jni.access.JNIAccessibleMethod", "modifiers"));
        Assert.assertFalse("a subclass/other class with a listed field name (RR1's shape)", WorldTopRule.pendingAllowlisted("C91E2rFnPtrPendingLeak$Holder", "pointer"));
        Assert.assertFalse("no prefix match", WorldTopRule.pendingAllowlisted("com.oracle.svm.core.c.BoxedRelocatedPointerX", "pointer"));
        Assert.assertEquals("every listed class and named field exists on this build", 0, WorldTopRule.pendingAllowlistMissing());
    }

    /** The static fan decision is unchanged; the engine adds the EMPTY outside atom beside the fan. */
    @Test
    public void staticFanUnchanged() {
        Assert.assertEquals(RecursiveTracking.SF_EMPTY, RecursiveTracking.staticFanDecision(false, 0, true, 32));
        Assert.assertEquals(RecursiveTracking.SF_FAN, RecursiveTracking.staticFanDecision(false, 1, false, 32));
        Assert.assertEquals(RecursiveTracking.SF_MERGE, RecursiveTracking.staticFanDecision(false, 0, false, 32));
    }
}
