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

import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Dispatch pins:
 * <ul>
 * <li>the global proven override drop: a target is dropped only when another target
 * of the set overrides it and every block type dispatches it elsewhere (exact dispatch);</li>
 * <li>the abstract-root rule: an abstract CHA root never contributes its own resolution.</li>
 * </ul>
 * Both are pure functions, pinned on host JVMCI types (the fixture mirrors {@code TermsHashPerField}: an abstract
 * class whose two final subclasses both override {@code start}).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.internal.vm.ci/jdk.vm.ci.code"})
public class DispatchOverrideDropTest {

    abstract static class AbsRoot {
        void start() {
        }
    }

    static final class SubA extends AbsRoot {
        @Override
        void start() {
        }
    }

    static final class SubB extends AbsRoot {
        @Override
        void start() {
        }
    }

    /** a concrete base whose override may never run. */
    static class Box {
        void put(Object o) {
        }
    }

    static class SubBox extends Box {
        @Override
        void put(Object o) {
        }
    }

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private ResolvedJavaType type(Class<?> c) {
        ResolvedJavaType t = metaAccess.lookupJavaType(c);
        // HotSpot resolves a concrete method only on a linked type (an unlinked one answers null, which keeps the target)
        t.link();
        return t;
    }

    private ResolvedJavaMethod method(Class<?> c, String name, String descriptor) {
        for (ResolvedJavaMethod m : type(c).getDeclaredMethods(false)) {
            if (m.getName().equals(name) && m.getSignature().toMethodDescriptor().equals(descriptor)) {
                return m;
            }
        }
        throw new AssertionError("no method " + c.getName() + "." + name + descriptor);
    }

    @Test
    public void dropsAnOverriddenTargetEveryBlockTypeDispatchesElsewhere() {
        ResolvedJavaMethod objToString = method(Object.class, "toString", "()Ljava/lang/String;");
        ResolvedJavaMethod strToString = method(String.class, "toString", "()Ljava/lang/String;");
        Assert.assertEquals(List.of(strToString), DispatchResolution.provenOverrideDrop(List.of(objToString, strToString), List.of(type(String.class))));
        // the set's order is kept
        Assert.assertEquals(List.of(strToString), DispatchResolution.provenOverrideDrop(List.of(strToString, objToString), List.of(type(String.class))));
    }

    @Test
    public void keepsWhenABlockTypeMayRunTheTarget() {
        ResolvedJavaMethod objToString = method(Object.class, "toString", "()Ljava/lang/String;");
        ResolvedJavaMethod strToString = method(String.class, "toString", "()Ljava/lang/String;");
        List<ResolvedJavaMethod> both = List.of(objToString, strToString);
        Assert.assertEquals(both, DispatchResolution.provenOverrideDrop(both, List.of(type(String.class), type(Object.class))));
        // the receiver may be exactly a Box, so Box.put survives SubBox's override
        ResolvedJavaMethod boxPut = method(Box.class, "put", "(Ljava/lang/Object;)V");
        ResolvedJavaMethod subPut = method(SubBox.class, "put", "(Ljava/lang/Object;)V");
        List<ResolvedJavaMethod> puts = List.of(boxPut, subPut);
        Assert.assertEquals(puts, DispatchResolution.provenOverrideDrop(puts, List.of(type(Box.class), type(SubBox.class))));
        // a block of SubBox alone proves Box.put dead
        Assert.assertEquals(List.of(subPut), DispatchResolution.provenOverrideDrop(puts, List.of(type(SubBox.class))));
    }

    @Test
    public void keepsOnTopOrEmptyBlock() {
        ResolvedJavaMethod objToString = method(Object.class, "toString", "()Ljava/lang/String;");
        ResolvedJavaMethod strToString = method(String.class, "toString", "()Ljava/lang/String;");
        List<ResolvedJavaMethod> both = List.of(objToString, strToString);
        Assert.assertSame(both, DispatchResolution.provenOverrideDrop(both, null));
        Assert.assertSame(both, DispatchResolution.provenOverrideDrop(both, List.of()));
    }

    @Test
    public void keepsAProvenTargetThatNoOtherTargetOverrides() {
        // the string layer's rule: the drop needs an overriding target in the set (never empties the set)
        ResolvedJavaMethod objToString = method(Object.class, "toString", "()Ljava/lang/String;");
        ResolvedJavaMethod objHashCode = method(Object.class, "hashCode", "()I");
        List<ResolvedJavaMethod> set = List.of(objToString, objHashCode);
        Assert.assertTrue(ForwardFixpoint.overrideDropProven(true, List.of(type(String.class)), objToString));
        Assert.assertEquals(set, DispatchResolution.provenOverrideDrop(set, List.of(type(String.class))));
        Assert.assertEquals(List.of(objToString), DispatchResolution.provenOverrideDrop(List.of(objToString), List.of(type(String.class))));
    }

    @Test
    public void trioD2ShapeUnderTheDrop() {
        ResolvedJavaMethod absStart = method(AbsRoot.class, "start", "()V");
        ResolvedJavaMethod aStart = method(SubA.class, "start", "()V");
        ResolvedJavaMethod bStart = method(SubB.class, "start", "()V");
        List<ResolvedJavaMethod> three = List.of(absStart, aStart, bStart);
        Assert.assertEquals(List.of(aStart, bStart), DispatchResolution.provenOverrideDrop(three, List.of(type(SubA.class), type(SubB.class))));
        Assert.assertTrue(DispatchResolution.overriddenInSet(absStart, three));
        Assert.assertFalse(DispatchResolution.overriddenInSet(aStart, three));
    }

    @Test
    public void arrayRootsAlwaysContributeTheirOwnResolution() {
        // JVMCI reports array (and primitive) types as ABSTRACT|FINAL, yet an array is the exact runtime type
        // of its objects and has no subtypes: its own resolution (the Object methods) is its only target
        for (Class<?> c : new Class<?>[]{String[].class, Object[].class, int[].class, AbsRoot[].class, String[][].class}) {
            ResolvedJavaType t = type(c);
            Assert.assertTrue(c + " is reported abstract by JVMCI (the premise of this pin)", java.lang.reflect.Modifier.isAbstract(t.getModifiers()));
            Assert.assertTrue(c.getName(), DispatchResolution.rootContributesOwnResolution(t));
        }
        Assert.assertTrue(DispatchResolution.rootContributesOwnResolution(type(int.class)));
        // (the host HotSpot JVMCI asserts in resolveMethod on an array type)
        Assert.assertFalse(DispatchResolution.rootContributesOwnResolution(type(AbsRoot.class)));
    }

    @Test
    public void abstractRootContributesNoOwnResolution() {
        Assert.assertFalse(DispatchResolution.rootContributesOwnResolution(type(AbsRoot.class)));
        Assert.assertFalse(DispatchResolution.rootContributesOwnResolution(type(java.util.AbstractList.class)));
        Assert.assertTrue(DispatchResolution.rootContributesOwnResolution(type(SubA.class)));
        Assert.assertTrue(DispatchResolution.rootContributesOwnResolution(type(Box.class)));
        Assert.assertTrue(DispatchResolution.rootContributesOwnResolution(type(java.util.ArrayList.class)));
    }
}
