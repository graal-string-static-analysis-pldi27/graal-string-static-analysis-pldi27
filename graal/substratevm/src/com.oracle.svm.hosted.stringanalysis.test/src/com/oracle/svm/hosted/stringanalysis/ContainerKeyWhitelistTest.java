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

public class ContainerKeyWhitelistTest {

    @Test
    public void keyParamIndexIsAlwaysParamOne() {
        for (String m : SugNameTables.HASH_CONTAINER_KEY_METHODS) {
            Assert.assertTrue("key param for " + m + " should be index 1",
                            SugNameTables.isKeyParamIndex(m, 1));
            Assert.assertFalse("param 0 (receiver) for " + m + " should not be key",
                            SugNameTables.isKeyParamIndex(m, 0));
            Assert.assertFalse("param 2 (value of put/putIfAbsent) for " + m + " should not be key",
                            SugNameTables.isKeyParamIndex(m, 2));
            Assert.assertFalse("negative param for " + m, SugNameTables.isKeyParamIndex(m, -1));
        }
    }

    @Test
    public void unknownMethodNotKeyParam() {
        Assert.assertFalse(SugNameTables.isKeyParamIndex("computeIfAbsent", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("compute", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("merge", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("containsValue", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("replace", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("size", 1));
        Assert.assertFalse(SugNameTables.isKeyParamIndex("", 1));
    }

    @Test
    public void hashContainerClassesComplete() {
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.HashMap"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.LinkedHashMap"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.HashSet"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.LinkedHashSet"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.concurrent.ConcurrentHashMap"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.Hashtable"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.WeakHashMap"));
    }

    @Test
    public void excludedContainersNotListed() {
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.TreeMap"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.TreeSet"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.IdentityHashMap"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_CLASSES.contains("java.util.EnumMap"));
    }

    @Test
    public void excludedMethodsNotListed() {
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("computeIfAbsent"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("compute"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("merge"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("containsValue"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("putAll"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("clear"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("size"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("isEmpty"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_KEY_METHODS.contains("replace"));
    }

    @Test
    public void storingMethodsClassified() {
        for (String m : SugNameTables.HASH_CONTAINER_STORING_METHODS) {
            Assert.assertTrue("storing method " + m + " should be in key methods",
                            SugNameTables.HASH_CONTAINER_KEY_METHODS.contains(m));
        }
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("put"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("putIfAbsent"));
        Assert.assertTrue(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("add"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("get"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("containsKey"));
        Assert.assertFalse(SugNameTables.HASH_CONTAINER_STORING_METHODS.contains("remove"));
    }

    @Test
    public void containsAllowedOnlyForHashSetClasses() {
        Assert.assertTrue(SugNameTables.HASH_SET_CONTAINS_CLASSES.contains("java.util.HashSet"));
        Assert.assertTrue(SugNameTables.HASH_SET_CONTAINS_CLASSES.contains("java.util.LinkedHashSet"));
        Assert.assertFalse(SugNameTables.HASH_SET_CONTAINS_CLASSES.contains("java.util.Hashtable"));
        Assert.assertFalse(SugNameTables.HASH_SET_CONTAINS_CLASSES.contains("java.util.concurrent.ConcurrentHashMap"));
        Assert.assertFalse(SugNameTables.HASH_SET_CONTAINS_CLASSES.contains("java.util.HashMap"));
    }

    @Test
    public void storingMethodNameAcceptedByBothWhitelists() {
        String storingMethod = "equals";
        String declaringClass = "java.lang.String";
        Assert.assertTrue("equals must be SV-whitelisted for storing methods",
                        StringViewWhitelist.isWhitelisted(storingMethod, declaringClass, "Ljava/lang/Object;"));
        Assert.assertTrue("equals must be LS-whitelisted for storing methods",
                        LazyConcatWhitelist.isWhitelisted(storingMethod, declaringClass, "Ljava/lang/Object;")); // W_lazy is signature-gated
    }

    @Test
    public void contentEqualsNotLsWhitelisted() {
        Assert.assertFalse("contentEquals must NOT be LS-whitelisted",
                        LazyConcatWhitelist.isWhitelisted("contentEquals", "java.lang.String", ""));
        Assert.assertTrue("contentEquals must be SV-whitelisted",
                        StringViewWhitelist.isWhitelisted("contentEquals", "java.lang.String", "Ljava/lang/CharSequence;"));
    }

    @Test
    public void containerDerivedViewMethodsComplete() {
        Assert.assertTrue(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("entrySet"));
        Assert.assertTrue(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("keySet"));
        Assert.assertTrue(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("values"));
    }

    @Test
    public void containerDerivedViewMethodsExcludesNonView() {
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("iterator"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("add"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("put"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("get"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("containsKey"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("remove"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("size"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("isEmpty"));
        Assert.assertFalse(SugNameTables.CONTAINER_DERIVED_VIEW_METHODS.contains("clear"));
    }

    @Test
    public void entryAccessorMethodsComplete() {
        Assert.assertTrue(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("getKey"));
        Assert.assertTrue(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("getValue"));
    }

    @Test
    public void entryAccessorMethodsExcludesNonAccessor() {
        Assert.assertFalse(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("setValue"));
        Assert.assertFalse(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("hashCode"));
        Assert.assertFalse(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("equals"));
        Assert.assertFalse(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("iterator"));
        Assert.assertFalse(SugNameTables.ENTRY_ACCESSOR_METHODS.contains("next"));
    }
}
