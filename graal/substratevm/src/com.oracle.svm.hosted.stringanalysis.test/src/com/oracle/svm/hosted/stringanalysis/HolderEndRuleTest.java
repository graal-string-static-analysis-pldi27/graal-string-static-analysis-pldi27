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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscFact;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.EscKind;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.HolderFacts;
import com.oracle.svm.hosted.stringanalysis.HolderEndRule.HolderRuleResult;

/**
 * Holder-end rule ("explained holder ends only"): the pure pieces of the rule that gates an
 * {@code escape-no-load} "no usage" admit. An escape is holder-free (static, VM thread-local, a closed field with no load
 * site, a closed field that fell back to every load site) or rests on its holders' walks, recursively; an unexplained
 * holder end refuses ({@code HOLDER_END_UNEXPLAINED}, REJECT), a holder end with a sound cause (a points-to-dead target, ...)
 * does not.
 */
public class HolderEndRuleTest {

    private static HolderRuleResult rule(List<EscFact> s, Map<Object, HolderFacts> facts) {
        return HolderEndRule.holderRule(s, facts::get);
    }

    private static EscFact walk(Object... holders) {
        return new EscFact(false, List.of(holders));
    }

    private static EscFact free() {
        return new EscFact(true, List.of());
    }

    @Test
    public void holderFreeProofForms() {
        Assert.assertTrue("a static field (runtime-code static table)", HolderEndRule.escHolderFree(EscKind.STATIC, 0, false));
        Assert.assertTrue("a VM thread-local (global table)", HolderEndRule.escHolderFree(EscKind.VMTL, 0, false));
        Assert.assertTrue("a closed field with zero load sites", HolderEndRule.escHolderFree(EscKind.CLOSED, 0, false));
        Assert.assertTrue("a closed field fallen back to every load site", HolderEndRule.escHolderFree(EscKind.CLOSED, 5, true));
        Assert.assertFalse("a closed field with load sites and no fallback rests on holders", HolderEndRule.escHolderFree(EscKind.CLOSED, 5, false));
        Assert.assertFalse("an open field / array element / model member rests on holders", HolderEndRule.escHolderFree(EscKind.IDENTITY, 0, false));
        Assert.assertFalse(HolderEndRule.escHolderFree(EscKind.IDENTITY, 0, true));
    }

    @Test
    public void holderFreeEscapesIgnoreHolderEnds() {
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(), List.of("ret-no-caller @ M@3")));
        HolderRuleResult r = rule(List.of(free(), free()), f);
        Assert.assertTrue(r.holderFree());
        Assert.assertTrue(r.admits());
        Assert.assertEquals(0, r.holders());
    }

    @Test
    public void unexplainedHolderEndRefuses() {
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(), List.of("undelivered-ownerret:M on Y")));
        HolderRuleResult r = rule(List.of(walk("X")), f);
        Assert.assertFalse(r.holderFree());
        Assert.assertFalse("an unexplained holder end turns the no-usage claim into a refusal", r.admits());
        Assert.assertEquals(1, r.unexplained().size());
        Assert.assertTrue(r.unexplained().get(0).startsWith("X: "));
        // the refusal is a named one that ends in REJECT "incomplete downstream trace"
        Assert.assertEquals(TransferFacts.IncompleteReason.INCOMPLETE_TRAVERSAL, RTrackRefusal.HOLDER_END_UNEXPLAINED.verdictReason());
        Assert.assertFalse(RTrackRefusal.HOLDER_END_UNEXPLAINED.budgetClass);
    }

    @Test
    public void mixedEscapesOneWalkBasedWithUnexplainedEndRefuses() {
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(), List.of("ret-no-caller @ M@3")));
        Assert.assertFalse(rule(List.of(free(), walk("X")), f).admits());
    }

    @Test
    public void completeOrSoundlyEndedHolderAdmits() {
        // the logback shape: the holder's walk ends at points-to-dead targets only (recorded as sound, not unexplained)
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(), List.of()));
        HolderRuleResult r = rule(List.of(walk("X")), f);
        Assert.assertTrue(r.admits());
        Assert.assertEquals(1, r.holders());
        // a holder with no facts at all: a complete walk with no silent end, no escape, no wait
        Assert.assertTrue(rule(List.of(walk("Z")), f).admits());
    }

    @Test
    public void recursionThroughTheHoldersWalkBasedEscapes() {
        // LocationInfo shape: X escapes into a never-read static (holder-free): admitted
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(free()), List.of()));
        Assert.assertTrue(rule(List.of(walk("X")), f).admits());
        // X escapes into an open field of Y, and Y's walk has an unexplained end: refused (second level)
        f.put("X", new HolderFacts(List.of(walk("Y")), List.of()));
        f.put("Y", new HolderFacts(List.of(), List.of("undelivered-objidret:M")));
        HolderRuleResult r = rule(List.of(walk("X")), f);
        Assert.assertFalse(r.admits());
        Assert.assertEquals(2, r.holders());
        Assert.assertTrue(r.unexplained().get(0).startsWith("Y: "));
        // a holder-free escape of X is not followed (Y's end does not matter then)
        f.put("X", new HolderFacts(List.of(new EscFact(true, List.of("Y"))), List.of()));
        Assert.assertTrue(rule(List.of(walk("X")), f).admits());
    }

    @Test
    public void cyclesTerminate() {
        Map<Object, HolderFacts> f = new HashMap<>();
        f.put("X", new HolderFacts(List.of(walk("Y")), List.of()));
        f.put("Y", new HolderFacts(List.of(walk("X")), List.of()));
        HolderRuleResult r = rule(List.of(walk("X")), f);
        Assert.assertTrue(r.admits());
        Assert.assertEquals(2, r.holders());
    }

    @Test
    public void zeroHolderWalkEscapeIsUnexplained() {
        // a walk-based escape whose receiver sink delivered no holder rests on nothing
        Map<Object, HolderFacts> f = new HashMap<>();
        EscFact none = new EscFact(false, List.of(), false, "IDENTITY:Box.s");
        Assert.assertTrue(HolderEndRule.escNoHolderUnexplained(none));
        HolderRuleResult r = rule(List.of(none), f);
        Assert.assertFalse(r.holderFree());
        Assert.assertFalse("zero holders: refused", r.admits());
        Assert.assertEquals(List.of("no-holder:IDENTITY:Box.s"), r.unexplained());
        // the one sound exemption: every delivery skipped as the infeasible store into a length-0 array
        EscFact len0 = new EscFact(false, List.of(), true, "IDENTITY:[]");
        Assert.assertFalse(HolderEndRule.escNoHolderUnexplained(len0));
        Assert.assertTrue(rule(List.of(len0), f).admits());
        // a holder-free escape never needs a holder
        Assert.assertFalse(HolderEndRule.escNoHolderUnexplained(new EscFact(true, List.of(), false, "STATIC:S")));
        // with at least one holder the escape rests on that holder's walk (judged as before)
        Assert.assertFalse(HolderEndRule.escNoHolderUnexplained(new EscFact(false, List.of("X"), false, "IDENTITY:Box.s")));
        // the same belt at the holder level: X's own walk-based escape with no holder
        f.put("X", new HolderFacts(List.of(new EscFact(false, List.of(), false, "CLOSED:Y.f")), List.of()));
        HolderRuleResult r2 = rule(List.of(walk("X")), f);
        Assert.assertFalse(r2.admits());
        Assert.assertEquals(List.of("X: no-holder:CLOSED:Y.f"), r2.unexplained());
    }

    @Test
    public void soundEndCauses() {
        for (String c : new String[]{"dead-target", "unread-param", "monitor-obs", "no-usages", "state", "obs", "pi-arm-dead", "arm-dead-usage", "classname-only-getClass", "infeasible-owner"}) {
            Assert.assertTrue(c, HolderEndRule.soundEndCause(c));
        }
        // the cause of a quiet-node label is its first token (silentUsesLabel joins kinds with '+')
        Assert.assertTrue(HolderEndRule.soundEndCause(RecursiveTracking.silentCause("obs:IsNullNode+state")));
        Assert.assertTrue(HolderEndRule.soundEndCause(RecursiveTracking.silentCause("dead-target:ch.qos.logback.core.spi.ContextAwareBase.addStatus @ X@3 Invoke")));
        for (String c : new String[]{"ret-no-caller", "undelivered-ownerret", "anything-else", ""}) {
            Assert.assertFalse(c, HolderEndRule.soundEndCause(c));
        }
    }
}
