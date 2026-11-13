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
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * Every rep override that may
 * return a String (its declared return type is {@code String} or a supertype of it) and that the rep's whitelist
 * admits is on the hand list with {@code returnsThis=true}. The child's walk then continues at the call's result, so
 * a result that is the rep itself ({@code this}, as the JDK returns for the no-op cases) or another rep
 * (a {@code trim} view) stays on the tracked flow; a direct-call site can never receive it untracked.
 * <p>
 * The whitelists are the ones the verdict layer applies ({@link HandListLeakWhitelistTest#repWhitelists()}: W_view
 * incl. the bridge, W_lazy per variant and with an unknown variant, the accumulator's extraction). The flat reps
 * (SingleByteString, TrivialString) have no whitelist, so all their String-returning overrides count.
 * <p>
 * Every String-returning StringView override is whitelisted and hand-listed. No rep overrides {@code toString()} (the
 * inherited {@code String.toString} returns {@code this}), so {@link #NOT_WHITELISTED} is empty.

 */
public class RepReturnPinTest {

    /** The String-returning overrides no whitelist admits (empty: no rep overrides toString()). */
    static final Set<String> NOT_WHITELISTED = Set.of();

    /** The flat reps: a real {@code value[]}, no whitelist. */
    static boolean isFlat(Class<?> rep) {
        return InlineCacheRegistry.isValueCarryingFlatRep(rep); // derived, not a name list
    }

    static boolean mayReturnAString(Method m) {
        return !m.getReturnType().isPrimitive() && m.getReturnType().isAssignableFrom(String.class);
    }

    static boolean admittedByItsWhitelist(Class<?> rep, String name, String sig) {
        if (isFlat(rep)) {
            return true;
        }
        for (HandListLeakWhitelistTest.RepWhitelist w : HandListLeakWhitelistTest.repWhitelists()) {
            if (w.representation() == rep && w.whitelist().admits(name, StringTerminalHandList.STRING, sig)) {
                return true;
            }
        }
        return false;
    }

    /** The check over the given rep classes; returns one message per violation and fills {@code notWhitelisted}. */
    static List<String> violations(List<Class<?>> reps, Set<String> notWhitelisted) {
        List<String> out = new ArrayList<>();
        for (Class<?> rep : reps) {
            for (Method m : rep.getDeclaredMethods()) {
                if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers()) || !mayReturnAString(m)) {
                    continue;
                }
                String sig = RepPinSupport.signature(m);
                String label = RepPinSupport.label(rep, m.getName(), sig);
                if (m.isSynthetic() || m.isBridge()) {
                    out.add(label + ": a synthetic or bridge method that may return a String (unaudited)");
                    continue;
                }
                if (!admittedByItsWhitelist(rep, m.getName(), sig)) {
                    notWhitelisted.add(label);
                    continue;
                }
                StringTerminalHandList.Entry e = RepPinSupport.handEntry(m.getName(), sig);
                if (e == null || !e.returnsThis()) {
                    out.add(label + " is whitelisted and may return this or a rep, but the hand list has " +
                                    (e == null ? "no entry" : "returnsThis=false") + " for String." + m.getName() + "(" + sig + ")");
                }
            }
        }
        return out;
    }

    @Test
    public void everyWhitelistedStringReturningOverrideIsHandListedReturnsThis() {
        Set<String> notWhitelisted = new TreeSet<>();
        List<String> v = violations(RepPinSupport.repClasses(), notWhitelisted);
        Assert.assertTrue("A3 violations:\n  " + String.join("\n  ", v), v.isEmpty());
        Assert.assertEquals("the String-returning overrides outside every whitelist", new TreeSet<>(NOT_WHITELISTED), notWhitelisted);
    }

    /** Positive control: the check sees the StringView no-op overrides (a scan that finds nothing fails). */
    @Test
    public void theScanSeesTheStringViewNoOpOverrides() throws NoSuchMethodException {
        for (String name : new String[]{"trim", "strip", "stripLeading", "stripTrailing", "toUpperCase", "toLowerCase"}) {
            Method m = StringView.class.getDeclaredMethod(name);
            Assert.assertTrue(name, mayReturnAString(m));
            Assert.assertTrue(name, admittedByItsWhitelist(StringView.class, name, ""));
        }
        Assert.assertTrue(mayReturnAString(StringView.class.getDeclaredMethod("subSequence", int.class, int.class)));
        Assert.assertTrue(mayReturnAString(StringView.class.getDeclaredMethod("repeat", int.class)));
        Assert.assertTrue(mayReturnAString(StringView.class.getDeclaredMethod("substring", int.class)));
        Assert.assertFalse(mayReturnAString(StringView.class.getDeclaredMethod("length")));
    }
}
