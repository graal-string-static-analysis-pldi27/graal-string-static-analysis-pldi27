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

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * The named-class rules of {@link ObjRetRules}: the String-cone check ({@code STRING_CONE}) first in the qualification
 * order (on real JDK types and a rep), the guard's order, the exposure rule, the harmless-use list of a Class object
 * (and what is not on it), the use-based construction scan, and the knob defaults (objret=1; objret=0 runs no named
 * code path; the census is off).
 */
public class ObjRetNamedClassTest {
    private static final MetaAccessProvider META = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static ResolvedJavaType t(Class<?> c) {
        return META.lookupJavaType(c);
    }

    @Test
    public void qStrIsFirstAndStructural() {
        ResolvedJavaType str = t(String.class);
        // every supertype of String, String itself and a rep: STRING_CONE
        for (Class<?> c : new Class<?>[]{Object.class, CharSequence.class, Comparable.class, java.io.Serializable.class, java.lang.constant.Constable.class,
                        java.lang.constant.ConstantDesc.class, String.class, com.oracle.svm.core.stringrep.TrivialString.class}) {
            Assert.assertTrue(c.getName(), ObjRetRules.stringCone(t(c), str));
            Assert.assertEquals(c.getName(), ObjRetRules.NoQualifyN.STRING_CONE, ObjRetRules.qualifies(ObjRetRules.stringCone(t(c), str), false));
            // STRING_CONE wins over an empty cone (first in the order)
            Assert.assertEquals(ObjRetRules.NoQualifyN.STRING_CONE, ObjRetRules.qualifies(true, true));
        }
        // a class / interface not comparable with String (incl. a supertype of a rep's other supertypes, e.g. Runnable)
        for (Class<?> c : new Class<?>[]{StringBuilder.class, java.util.AbstractList.class, Runnable.class, Integer.class, ObjRetNamedClassTest.class}) {
            Assert.assertFalse(c.getName(), ObjRetRules.stringCone(t(c), str));
            Assert.assertNull(c.getName(), ObjRetRules.qualifies(ObjRetRules.stringCone(t(c), str), false)); // c is used
        }
        Assert.assertEquals(ObjRetRules.NoQualifyN.EMPTY_CONE, ObjRetRules.qualifies(false, true));
        Assert.assertEquals(ObjRetRules.FrameNoQualify.STATIC, ObjRetRules.frameQualifies(true, true));
        Assert.assertEquals(ObjRetRules.FrameNoQualify.NATIVE_OR_ADDRESS, ObjRetRules.frameQualifies(false, true));
        Assert.assertNull(ObjRetRules.frameQualifies(false, false));
    }

    @Test
    public void guardTableOrder() {
        Assert.assertNull(guardWith());
        Assert.assertNull(ObjRetRules.guard(false, false, false, ObjRetRules.MAX_BIRTHS, false, 0, false, false, false, false, false, 0, 0, false, false, 0));
        Assert.assertEquals("the cap is 16", 16, ObjRetRules.MAX_BIRTHS);
        ObjRetRules.GuardFailN[] order = ObjRetRules.GuardFailN.values();
        for (int i = 0; i < order.length; i++) {
            Assert.assertEquals(order[i], guardWith(i));
            for (int j = i + 1; j < order.length; j++) {
                Assert.assertEquals(order[i] + " before " + order[j], order[i], guardWith(i, j));
            }
        }
    }

    private static ObjRetRules.GuardFailN guardWith(int... fails) {
        boolean[] f = new boolean[ObjRetRules.GuardFailN.values().length];
        for (int i : fails) {
            f[i] = true;
        }
        int births = f[ObjRetRules.GuardFailN.NO_BIRTH.ordinal()] ? 0 : f[ObjRetRules.GuardFailN.TOO_MANY_BIRTHS.ordinal()] ? ObjRetRules.MAX_BIRTHS + 1 : 1;
        return ObjRetRules.guard(f[ObjRetRules.GuardFailN.PREMISE.ordinal()], f[ObjRetRules.GuardFailN.VM_REENTRY.ordinal()], f[ObjRetRules.GuardFailN.INDEX_FAILED.ordinal()], births,
                        f[ObjRetRules.GuardFailN.NO_MEMBER_BIRTH.ordinal()], f[ObjRetRules.GuardFailN.UNFRAMED_METHOD.ordinal()] ? 1 : 0, f[ObjRetRules.GuardFailN.UNFRAMED_BIRTH.ordinal()],
                        f[ObjRetRules.GuardFailN.UNWALKABLE_BIRTH.ordinal()],
                        f[ObjRetRules.GuardFailN.NEST_EXPOSED.ordinal()], f[ObjRetRules.GuardFailN.CONE_ARRAY.ordinal()], f[ObjRetRules.GuardFailN.CONE_CSM.ordinal()],
                        f[ObjRetRules.GuardFailN.CLASS_CONSTANT.ordinal()] ? 1 : 0, f[ObjRetRules.GuardFailN.CLASS_HOLDER.ordinal()] ? 1 : 0, f[ObjRetRules.GuardFailN.REGISTERED.ordinal()],
                        f[ObjRetRules.GuardFailN.METADATA_TYPE.ordinal()], f[ObjRetRules.GuardFailN.PENDING_SLOT.ordinal()] ? 1 : 0);
    }

    private static final boolean[] EXPOSED_TABLE = {false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true};

    @Test
    public void exposureRule() {
        for (int bits = 0; bits < 16; bits++) {
            boolean cone = (bits & 1) != 0;
            boolean sealed = (bits & 2) != 0;
            boolean iface = (bits & 4) != 0;
            boolean above = (bits & 8) != 0;
            // the expected column is a literal table (bits = cone | sealed<<1 | iface<<2 | above<<3), not the formula
            boolean expect = EXPOSED_TABLE[bits];
            Assert.assertEquals("bits=" + bits, expect, ObjRetRules.exposed(cone, sealed, iface, above));
        }
        // an abstract class below a cone member leads to it by getSuperclass; an unsealed interface below it does not
        Assert.assertTrue(ObjRetRules.exposed(false, false, false, true));
        Assert.assertFalse(ObjRetRules.exposed(false, false, true, true));
    }

    @Test
    public void np5HarmlessList() {
        // receiver observations of Class (and its SVM hub)
        for (String m : new String[]{"getName", "getSimpleName", "getTypeName", "getCanonicalName", "getPackageName", "toString", "hashCode", "equals", "isInstance",
                        "isAssignableFrom", "cast", "isArray", "isPrimitive", "isInterface", "isEnum", "isRecord", "isHidden", "isSealed", "isAnonymousClass", "isLocalClass",
                        "isMemberClass", "isSynthetic", "isAnnotation", "getModifiers", "desiredAssertionStatus"}) {
            Assert.assertTrue(m, ObjRetRules.harmlessCall("java.lang.Class", m, 0, true));
            Assert.assertTrue(m, ObjRetRules.harmlessCall("com.oracle.svm.core.hub.DynamicHub", m, 0, true));
        }
        // not harmless: anything returning a Class or a reflective object, newInstance, ClassValue, lookups
        for (String m : new String[]{"getSuperclass", "getInterfaces", "componentType", "getComponentType", "arrayType", "getDeclaringClass", "getEnclosingClass",
                        "getNestHost", "getNestMembers", "getPermittedSubclasses", "getDeclaredConstructors", "getDeclaredMethods", "getMethod", "getEnumConstants",
                        "getRecordComponents", "getClassLoader", "getModule", "newInstance", "forName"}) {
            Assert.assertFalse(m, ObjRetRules.harmlessCall("java.lang.Class", m, 0, true));
        }
        // Object's identity methods on a Class receiver
        Assert.assertTrue(ObjRetRules.harmlessCall("java.lang.Object", "equals", 0, true));
        Assert.assertTrue(ObjRetRules.harmlessCall("java.lang.Object", "hashCode", 0, true));
        Assert.assertFalse("Object.getClass is not on the receiver list", ObjRetRules.harmlessCall("java.lang.Object", "getClass", 0, true));
        // argument positions: only another Class's isAssignableFrom / equals / isInstance; cast(c) returns c
        Assert.assertTrue(ObjRetRules.harmlessCall("java.lang.Class", "isAssignableFrom", 1, true));
        Assert.assertTrue(ObjRetRules.harmlessCall("java.lang.Object", "equals", 1, true));
        Assert.assertTrue(ObjRetRules.harmlessCall("java.lang.Class", "isInstance", 1, true));
        Assert.assertFalse(ObjRetRules.harmlessCall("java.lang.Class", "cast", 1, true));
        Assert.assertFalse("equals on an unknown receiver may store the argument", ObjRetRules.harmlessCall("java.lang.Object", "equals", 1, false));
        // any other holder (a user method, Unsafe.allocateInstance, MethodHandles.privateLookupIn, ClassValue.get) is not harmless
        for (String h : new String[]{"jdk.internal.misc.Unsafe", "sun.misc.Unsafe", "java.lang.invoke.MethodHandles", "java.lang.ClassValue", "java.util.Objects", "x.User"}) {
            Assert.assertFalse(h, ObjRetRules.harmlessCall(h, "allocateInstance", 1, false));
            Assert.assertFalse(h, ObjRetRules.harmlessCall(h, "get", 1, false));
            Assert.assertFalse(h, ObjRetRules.harmlessCall(h, "getName", 0, true));
        }
        // the node lists: observations only; Pis and hub reads are followed (never "harmless" themselves)
        Assert.assertTrue(ObjRetRules.HARMLESS_NODES.containsAll(java.util.Set.of("ObjectEqualsNode", "IsNullNode", "InstanceOfDynamicNode", "ClassIsAssignableFromNode")));
        for (String k : new String[]{"StoreFieldNode", "StoreIndexedNode", "ReturnNode", "MethodCallTargetNode", "PhiNode", "ValuePhiNode", "ConditionalNode", "UnsafeAllocateInstanceNode",
                        "DynamicNewInstanceNode", "PiNode", "ClassGetHubNode"}) {
            Assert.assertFalse(k, ObjRetRules.HARMLESS_NODES.contains(k));
        }
        Assert.assertEquals(java.util.Set.of("PiNode", "ClassGetHubNode"), ObjRetRules.FOLLOW_NODES);
        Assert.assertEquals(java.util.Set.of("RETURN_FAN_CAP", "WORLD_TOP_EXIT", "CALLER_FAN_CAP", "WORLD_TOP_ENTRY"), ObjRetRules.NESTABLE);
    }

    /** Construction-scan fixtures: one method names RETAIN_CLASS_REFERENCE, one only another option, one none. */
    static StackWalker retainWalker() {
        return StackWalker.getInstance(StackWalker.Option.RETAIN_CLASS_REFERENCE);
    }

    static StackWalker reflectWalker() {
        return StackWalker.getInstance(StackWalker.Option.SHOW_REFLECT_FRAMES);
    }

    static int noWalker(int x) {
        return x + 1;
    }

    private static ResolvedJavaMethod m(String name, Class<?>... ps) throws NoSuchMethodException {
        return META.lookupJavaMethod(ObjRetNamedClassTest.class.getDeclaredMethod(name, ps));
    }

    @Test
    public void g1nConstructionScan() throws Exception {
        ResolvedJavaType opt = t(StackWalker.Option.class);
        Assert.assertTrue(ObjRetRules.readsStatic(m("retainWalker"), opt, "RETAIN_CLASS_REFERENCE"));
        Assert.assertFalse(ObjRetRules.readsStatic(m("reflectWalker"), opt, "RETAIN_CLASS_REFERENCE"));
        Assert.assertTrue(ObjRetRules.readsStatic(m("reflectWalker"), opt, "SHOW_REFLECT_FRAMES"));
        Assert.assertFalse(ObjRetRules.readsStatic(m("noWalker", int.class), opt, "RETAIN_CLASS_REFERENCE"));
        // the real JDK logger walker (SimpleConsoleLogger$CallerFinder) retains class references: construction fails there
        ResolvedJavaType cf = META.lookupJavaType(Class.forName("jdk.internal.logger.SimpleConsoleLogger$CallerFinder"));
        cf.link();
        boolean any = false;
        for (ResolvedJavaMethod x : cf.getDeclaredMethods(false)) {
            any |= ObjRetRules.readsStatic(x, opt, "RETAIN_CLASS_REFERENCE");
        }
        any |= cf.getClassInitializer() != null && ObjRetRules.readsStatic(cf.getClassInitializer(), opt, "RETAIN_CLASS_REFERENCE");
        Assert.assertTrue("CallerFinder.<clinit> reads RETAIN_CLASS_REFERENCE (G1-N must be use-based there)", any);
    }

    @Test
    public void knobDefaultsAreTheRevertIdentity() {
        // objret=1 is the default (objret=0: no named code path runs); the census stays off
        Assert.assertEquals(1, RecursiveTracking.OBJRET);
        Assert.assertFalse(RecursiveTracking.OBJRET_CENSUS);
        // the named key space is separate from the object-identity rule's (same wrapped site, different keys and census names)
        Object site = new Object();
        ObjectIdentityRule.IdSite hidden = new ObjectIdentityRule.IdSite(site);
        ObjectIdentityRule.IdSite named = new ObjectIdentityRule.IdSite(site, true);
        Assert.assertFalse(hidden.named);
        Assert.assertTrue(named.named);
        // IdSite has identity equality (no equals); the key-space separation is the two maps (idSites /
        // namedSites) and the census prefix below, not this object's equality
        Assert.assertTrue(hidden.toString().startsWith("objid:"));
        Assert.assertTrue(named.toString().startsWith("objret:"));
    }
}
