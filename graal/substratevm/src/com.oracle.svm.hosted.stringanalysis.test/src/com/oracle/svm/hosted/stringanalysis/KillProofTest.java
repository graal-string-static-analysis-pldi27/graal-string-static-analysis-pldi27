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
 * The inherited-carrier gate pin ({@link LfgWalk#carrierFieldInSuperclassChain}). The engine's kills are pinned by the
 * pools in {@code RTrackPoolsTest}.
 */
public class KillProofTest {

    /**
     * The allocation-seed gate ({@code LfgWalk.carrierFieldInSuperclassChain}) must walk the full superclass chain: a
     * subclass with no fields of its own that inherits a reference field ({@code class MyIter extends Base { }} with
     * {@code Base { MyList outer; }}) is an object carrier like a declaring class. A declared-only check leaves such
     * allocations unseeded (no ctor-this anchor, missed usages: the false-admit direction). Pinned at the gate
     * predicate (the seed walk itself needs the hosted universe and is covered end to end by the IterHop/Churn test
     * programs). The jdk.vm.ci types are faked by dynamic proxies.
     */
    @Test
    public void inheritedCarrierFieldMakesTheSubclassACarrier() {
        jdk.vm.ci.meta.ResolvedJavaType objectField = kindType(jdk.vm.ci.meta.JavaKind.Object);
        jdk.vm.ci.meta.ResolvedJavaType intField = kindType(jdk.vm.ci.meta.JavaKind.Int);
        // Base declares the carrier (a reference-typed instance field); the subclass declares nothing.
        jdk.vm.ci.meta.ResolvedJavaType base = typeWithFields(java.util.List.of(fieldOfType(objectField)), null);
        jdk.vm.ci.meta.ResolvedJavaType sub = typeWithFields(java.util.List.of(), base);
        Assert.assertTrue("an INHERITED reference field is a carrier (the M-2 seam: the declared-only gate said no)",
                        LfgWalk.carrierFieldInSuperclassChain(sub));
        // A primitive-only chain is never a carrier (two levels — the walk must not stop early either).
        jdk.vm.ci.meta.ResolvedJavaType primBase = typeWithFields(java.util.List.of(fieldOfType(intField)), null);
        jdk.vm.ci.meta.ResolvedJavaType primSub = typeWithFields(java.util.List.of(fieldOfType(intField)), primBase);
        Assert.assertFalse("primitive fields (own or inherited) carry nothing",
                        LfgWalk.carrierFieldInSuperclassChain(primSub));
        // The direct form (the class declares the field itself) holds.
        Assert.assertTrue("a declared reference field is a carrier (the F-4 form)",
                        LfgWalk.carrierFieldInSuperclassChain(base));
        // The java.lang.Object tail terminates the walk with no false carrier.
        Assert.assertFalse("a field-less chain end is not a carrier",
                        LfgWalk.carrierFieldInSuperclassChain(typeWithFields(java.util.List.of(), null)));
    }

    /** A fake {@link jdk.vm.ci.meta.ResolvedJavaType} answering declared fields + superclass. */
    private static jdk.vm.ci.meta.ResolvedJavaType typeWithFields(java.util.List<jdk.vm.ci.meta.ResolvedJavaField> declared,
                    jdk.vm.ci.meta.ResolvedJavaType sup) {
        return (jdk.vm.ci.meta.ResolvedJavaType) java.lang.reflect.Proxy.newProxyInstance(
                        jdk.vm.ci.meta.ResolvedJavaType.class.getClassLoader(),
                        new Class<?>[]{jdk.vm.ci.meta.ResolvedJavaType.class},
                        (proxy, method, args) -> {
                            switch (method.getName()) {
                                case "getInstanceFields":
                                    return declared.toArray(new jdk.vm.ci.meta.ResolvedJavaField[0]);
                                case "getSuperclass":
                                    return sup;
                                case "equals":
                                    return proxy == args[0];
                                case "hashCode":
                                    return System.identityHashCode(proxy);
                                case "toString":
                                    return "FakeType";
                                default:
                                    return null;
                            }
                        });
    }

    /** A fake {@link jdk.vm.ci.meta.ResolvedJavaField} of the given type. */
    private static jdk.vm.ci.meta.ResolvedJavaField fieldOfType(jdk.vm.ci.meta.ResolvedJavaType t) {
        return (jdk.vm.ci.meta.ResolvedJavaField) java.lang.reflect.Proxy.newProxyInstance(
                        jdk.vm.ci.meta.ResolvedJavaField.class.getClassLoader(),
                        new Class<?>[]{jdk.vm.ci.meta.ResolvedJavaField.class},
                        (proxy, method, args) -> {
                            switch (method.getName()) {
                                case "getType":
                                    return t;
                                case "equals":
                                    return proxy == args[0];
                                case "hashCode":
                                    return System.identityHashCode(proxy);
                                case "toString":
                                    return "FakeField";
                                default:
                                    return null;
                            }
                        });
    }

    /** A fake {@link jdk.vm.ci.meta.ResolvedJavaType} of the given kind (the fields' resolved type). */
    private static jdk.vm.ci.meta.ResolvedJavaType kindType(jdk.vm.ci.meta.JavaKind kind) {
        return (jdk.vm.ci.meta.ResolvedJavaType) java.lang.reflect.Proxy.newProxyInstance(
                        jdk.vm.ci.meta.ResolvedJavaType.class.getClassLoader(),
                        new Class<?>[]{jdk.vm.ci.meta.ResolvedJavaType.class},
                        (proxy, method, args) -> {
                            switch (method.getName()) {
                                case "getJavaKind":
                                    return kind;
                                case "equals":
                                    return proxy == args[0];
                                case "hashCode":
                                    return System.identityHashCode(proxy);
                                case "toString":
                                    return "FakeJavaType";
                                default:
                                    return null;
                            }
                        });
    }
}
