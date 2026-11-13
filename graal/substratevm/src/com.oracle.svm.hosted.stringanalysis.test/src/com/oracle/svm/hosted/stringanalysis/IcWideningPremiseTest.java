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
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * The premises of the widened
 * inline cache. (1) The one method set is mechanically derived (every non-private instance method declared by
 * String, descriptor-keyed) and contains the pre-widening population. (2) The parent's per-(rep, method) else-domain
 * rule: a listed rep that inherits String's body rides the direct else only if it is a value-carrying flat rep or the
 * body is one of its pinned field-only entry bodies — for every value-null rep exactly
 * {@code RepInheritedBodyTest.EXPECTED_INHERITED} (the two derivations agree). (3) The raised caps.
 */
public class IcWideningPremiseTest {

    @Test
    public void methodSetIsTheReflectionDerivedStringInstanceSet() {
        Set<String> expected = new TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            if (!Modifier.isStatic(m.getModifiers()) && !Modifier.isPrivate(m.getModifiers())) {
                expected.add(TerminalBodyKinds.nameAndDescriptor(m));
            }
        }
        Assert.assertEquals(expected, new TreeSet<>(StringIcMethods.descriptors()));
        for (String legacy : new String[]{"equals(Ljava/lang/Object;)Z", "maybeCustomStringEquals(Ljava/lang/Object;)Z", "length()I", "hashCode()I",
                        "charAt(I)C", "isEmpty()Z", "toString()Ljava/lang/String;", StringIcMethods.GETBYTES_CODER_KEY}) {
            Assert.assertNotNull(legacy, StringIcMethods.lookup(legacy));
        }
        /* descriptor-exact: overloads are distinct members, the child keys them by parameter signature */
        Assert.assertTrue(StringIcMethods.isMemberSite("indexOf", "I"));
        Assert.assertTrue(StringIcMethods.isMemberSite("indexOf", "Ljava/lang/String;"));
        Assert.assertFalse(StringIcMethods.isMemberSite("indexOf", "Ljava/lang/Object;"));
        Assert.assertTrue(StringIcMethods.isMemberName("indexOf"));
        Assert.assertFalse(StringIcMethods.isMemberSite("valueOf", "I")); // static: not a member
    }

    /**
     * The value-null reps' else-domain over the whole widened set equals the independently pinned inherited-whitelisted
     * pairs: an inherited body a value-null rep may run through the direct else is exactly a pinned field-only entry
     * body; every other inherited body declines at a site listing that rep.
     */
    @Test
    public void valueNullElseDomainIsThePinnedEntryBodies() {
        Set<String> elseDomain = new TreeSet<>();
        int declinePairs = 0;
        for (Map.Entry<String, Class<?>> e : InlineCacheRegistry.REP_CLASSES.entrySet()) {
            Class<?> rep = e.getValue();
            if (InlineCacheRegistry.isValueCarryingFlatRep(rep)) {
                continue;
            }
            for (String nd : StringIcMethods.descriptors()) {
                Method m = StringIcMethods.lookup(nd);
                Class<?> impl = TerminalBodyKinds.implementingClass(rep, m);
                /*
                 * The JVM-rule selection (descriptor-exact, bridges included) always selects a
                 * declaration for a String member (a name/params walk would leave the covariant bridge
                 * resolveConstantDesc(Lookup)Object unresolved).
                 */
                Assert.assertNotNull(rep + " " + nd, impl);
                if (impl != String.class) {
                    continue;
                }
                if (TerminalBodyKinds.entryBodies(e.getKey()).contains(nd)) {
                    elseDomain.add(rep.getSimpleName() + "." + m.getName() + "(" + TerminalBodyKinds.usageSignature(m).replace(",", "") + ")");
                } else {
                    declinePairs++;
                }
            }
        }
        Assert.assertEquals(new TreeSet<>(RepInheritedBodyTest.EXPECTED_INHERITED), elseDomain);
        Assert.assertTrue("non-vacuity: some inherited value-reading bodies decline", declinePairs > 0);
    }

    @Test
    public void capsRaisedToFive() {
        Assert.assertEquals(5, HeuristicOrchestrator.MAX_RECEIVER_CUSTOM_REPS);
    }
}
