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

/**
 * The reflection bridge, the narrowed outside-caller predicate and the registry rule, as the pure functions the
 * engine calls.
 */
public class ReflectionBridgeTest {

    /** The accessor pointer fields: exact declaring class and name, nothing else. */
    @Test
    public void accessorPointerFields() {
        Assert.assertTrue(ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.reflect.SubstrateAccessor", "expandSignature"));
        Assert.assertTrue(ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.reflect.SubstrateAccessor", "directTarget"));
        Assert.assertTrue(ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.reflect.SubstrateConstructorAccessor", "factoryMethodTarget"));
        Assert.assertFalse("a subclass does not declare them", ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.reflect.SubstrateMethodAccessor", "directTarget"));
        Assert.assertFalse(ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.reflect.SubstrateAccessor", "initializeBeforeInvoke"));
        Assert.assertFalse("JNI pointers are not the bridge's", ReflectionBridge.isAccessorPointerField("com.oracle.svm.core.jni.access.JNIAccessibleMethod", "nonvirtualTarget"));
    }

    /** Reflective-only: in the table, a scan (accessor-reachable) first reason, not JNI, not a native entry. */
    @Test
    public void reflectiveOnly() {
        Assert.assertTrue(ReflectionBridge.reflectiveOnly(true, true, false, false));
        Assert.assertFalse("not in the bridge table", ReflectionBridge.reflectiveOnly(false, true, false, false));
        Assert.assertFalse("another source registered first (a non-scan reason)", ReflectionBridge.reflectiveOnly(true, false, false, false));
        Assert.assertFalse("JNI-registered too (option D)", ReflectionBridge.reflectiveOnly(true, true, true, false));
        Assert.assertFalse("a native entry", ReflectionBridge.reflectiveOnly(true, true, false, true));
    }

    /** The narrowed predicate: reflective-only sources are bridged, every other world-top source stays outside. */
    @Test
    public void narrowedOutside() {
        Assert.assertFalse(ReflectionBridge.narrowedOutside(false, false, false, false, false, false, false, false));
        Assert.assertFalse("a reflective-only direct root is bridged", ReflectionBridge.narrowedOutside(false, false, true, true, false, false, false, false));
        Assert.assertFalse("a reflective-only virtual root is bridged", ReflectionBridge.narrowedOutside(false, false, false, false, true, true, false, false));
        Assert.assertFalse("both, reflective-only", ReflectionBridge.narrowedOutside(false, false, true, true, true, true, false, false));
        Assert.assertTrue("native entry", ReflectionBridge.narrowedOutside(true, false, false, false, false, false, false, false));
        Assert.assertTrue("JNI-registered (registry)", ReflectionBridge.narrowedOutside(false, true, true, true, false, false, false, false));
        Assert.assertTrue("a direct root with another source", ReflectionBridge.narrowedOutside(false, false, true, false, false, false, false, false));
        Assert.assertTrue("a virtual root with another source", ReflectionBridge.narrowedOutside(false, false, false, false, true, false, false, false));
        Assert.assertTrue("reached through a non-reflective virtual root", ReflectionBridge.narrowedOutside(false, false, false, false, false, false, true, false));
        Assert.assertTrue("address taken outside the accessor slots", ReflectionBridge.narrowedOutside(false, false, true, true, false, false, false, true));
    }

    /** The narrowed predicate never answers outside where the world-top one does not (it only removes reflective sources). */
    @Test
    public void narrowingOnlyRemovesReflectiveSources() {
        for (int bits = 0; bits < 256; bits++) {
            boolean nat = (bits & 1) != 0;
            boolean jni = (bits & 2) != 0;
            boolean dr = (bits & 4) != 0;
            boolean dOnly = (bits & 8) != 0;
            boolean vr = (bits & 16) != 0;
            boolean vOnly = (bits & 32) != 0;
            boolean reachedNonRefl = (bits & 64) != 0;
            boolean addrUnmodelled = (bits & 128) != 0;
            boolean narrowed = ReflectionBridge.narrowedOutside(nat, jni, dr, dOnly, vr, vOnly, reachedNonRefl, addrUnmodelled);
            // the world-top predicate sees a JNI method as a root and a reached-through set with the non-reflective one
            boolean e2 = WorldTopRule.outsideCallerPredicate(nat, dr || jni, vr, reachedNonRefl, addrUnmodelled);
            if (narrowed && !(e2 || jni)) {
                Assert.fail("narrowed predicate outside where E2 is not: bits=" + bits);
            }
        }
    }

    /**
     * Registry rule: the non-pointer words of address-pending mode 0 need no registry; a JNI or boxed-pointer holder
     * must be listed.
     */
    @Test
    public void pendingHolderConfirmation() throws Exception {
        java.lang.reflect.Constructor<ReflectionBridge> c = ReflectionBridge.class.getDeclaredConstructor(RecursiveTracking.class);
        c.setAccessible(true);
        ReflectionBridge b = c.newInstance((RecursiveTracking) null);
        Object listed = new Object();
        b.jniMethodObjects.add(listed);
        Assert.assertTrue(b.pendingHolderConfirmed("com.oracle.svm.core.jni.access.JNIAccessibleMethod", listed));
        Assert.assertFalse("an unlisted JNI method holder", b.pendingHolderConfirmed("com.oracle.svm.core.jni.access.JNIAccessibleMethod", new Object()));
        Assert.assertFalse("an unlisted boxed pointer", b.pendingHolderConfirmed("com.oracle.svm.core.c.BoxedRelocatedPointer", new Object()));
        Assert.assertTrue("a non-pointer word of B'", b.pendingHolderConfirmed("com.oracle.svm.core.c.CIsolateData", new Object()));
        Assert.assertFalse("no bridge proof on an empty table", b.complete());
    }
}
