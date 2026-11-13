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

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The one override decision of the IC machinery ({@link TerminalBodyKinds#selectedDeclaration}) is
 * the JVM's. Oracle: the VM's own method selection ({@code ResolvedJavaType.resolveConcreteMethod}, HotSpot's vtable
 * rules) for every rep class × every non-private instance method declared by {@code java.lang.String} (bridges
 * included), and for a same-package package-private pair ({@code StringBuilder} × {@code AbstractStringBuilder}).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.internal.vm.ci/jdk.vm.ci.meta"})
public class IcOverrideRuleTest {

    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static List<String> mismatches(Class<?> receiver, Class<?> declaring) {
        return mismatches(receiver, declaring, false);
    }

    private static List<String> mismatches(Class<?> receiver, Class<?> declaring, boolean packagePrivateOnly) {
        ResolvedJavaType rt = META.lookupJavaType(receiver);
        List<String> out = new ArrayList<>();
        for (Method m : declaring.getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers())) {
                continue;
            }
            if (packagePrivateOnly && (Modifier.isPublic(m.getModifiers()) || Modifier.isProtected(m.getModifiers()))) {
                continue;
            }
            ResolvedJavaMethod vm = rt.resolveConcreteMethod(META.lookupJavaMethod(m), META.lookupJavaType(declaring)); // caller: the declaring class (accessible)
            Method ours = TerminalBodyKinds.selectedDeclaration(receiver, m);
            if (vm == null && Modifier.isFinal(m.getModifiers())) {
                vm = META.lookupJavaMethod(m); // JVMCI answers null for a final method; nothing can override it
            }
            if (vm == null && packagePrivateOnly) {
                continue; // JVMCI gives no answer for some synchronized (bridge) members here; the rep x String domain is strict
            }
            String vmDecl = vm == null ? "null" : vm.getDeclaringClass().toJavaName() + "." + vm.getName() + vm.getSignature().toMethodDescriptor();
            String ourDecl = ours == null ? "null" : ours.getDeclaringClass().getName() + "." + TerminalBodyKinds.nameAndDescriptor(ours);
            if (!vmDecl.equals(ourDecl)) {
                out.add(receiver.getSimpleName() + " " + TerminalBodyKinds.nameAndDescriptor(m) + ": VM " + vmDecl + " ours " + ourDecl);
            }
        }
        return out;
    }

    @Test
    public void selectionIsTheVmsForEveryRepAndStringMember() {
        List<String> wrong = new ArrayList<>();
        for (Class<?> rep : RepPinSupport.repClasses()) {
            wrong.addAll(mismatches(rep, String.class));
        }
        wrong.addAll(mismatches(String.class, String.class));
        Assert.assertEquals(List.of(), wrong);
    }

    @Test
    public void samePackagePackagePrivateIsOverridden() throws ClassNotFoundException {
        Class<?> asb = Class.forName("java.lang.AbstractStringBuilder");
        // the package-private members (the property under test; JVMCI answers null for some public synchronized overrides)
        Assert.assertEquals(List.of(), mismatches(StringBuilder.class, asb, true));
        Assert.assertEquals(List.of(), mismatches(StringBuffer.class, asb, true));
        int pp = 0;
        for (Method m : asb.getDeclaredMethods()) {
            int mod = m.getModifiers();
            if (!Modifier.isStatic(mod) && !Modifier.isPrivate(mod) && !Modifier.isPublic(mod) && !Modifier.isProtected(mod) &&
                            TerminalBodyKinds.implementingClass(StringBuffer.class, m) == StringBuffer.class) {
                pp++;
            }
        }
        Assert.assertTrue("non-vacuous: StringBuffer overrides some package-private ASB method", pp > 0);
    }

    /**
     * The ranged {@code getBytes(byte[],int,int,byte,int)}: a same-signature method in {@code com.oracle.svm.core.stringrep}
     * would not override it if it were package-private (what a name/params walk gets wrong). The builder JDK declares it
     * {@code protected} (the ranged copy of {@code AbstractStringBuilder.appendChars(..., String, ...)} /
     * {@code putStringAt}), so every value-null rep overrides it and virtual dispatch runs the rep's body; the flat reps
     * keep String's body ({@code RangeCopyParityTest}).
     */
    @Test
    public void rangedGetBytesIsOverriddenByEveryValueNullRep() throws NoSuchMethodException {
        Method m = String.class.getDeclaredMethod("getBytes", byte[].class, int.class, int.class, byte.class, int.class);
        Assert.assertTrue(Modifier.isProtected(m.getModifiers()));
        for (Class<?> rep : RepPinSupport.repClasses()) {
            Class<?> expected = RepInheritedBodyTest.VALUE_NULL_REPS.contains(rep) ? rep : String.class;
            Assert.assertSame(rep + " ranged getBytes implementation", expected, TerminalBodyKinds.implementingClass(rep, m));
        }
    }
}
