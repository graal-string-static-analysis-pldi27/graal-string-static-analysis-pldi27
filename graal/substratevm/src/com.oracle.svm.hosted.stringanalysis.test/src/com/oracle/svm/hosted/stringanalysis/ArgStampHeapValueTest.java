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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.AbstractCollection;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.junit.Test;

/**
 * The arg-stamp image-heap rule: a field that can hold an image-heap value is ⊤, because a build-time value has no
 * parsed writer.
 */
public class ArgStampHeapValueTest {

    @Test
    public void staticFieldTopIffBuildTimeInitialized() {
        assertTrue(ArgStampResolution.imageHeapRule(true, true, Set.of(), "C"));
        assertFalse(ArgStampResolution.imageHeapRule(true, false, null, "C")); // run-time init: every value is a parsed store
    }

    @Test
    public void instanceFieldTopIffDeclaringClassHasHeapInstance() {
        Set<Class<?>> owners = ArgStampResolution.withSuperclasses(List.of(ArrayList.class), Class::getSuperclass);
        // a heap ArrayList carries the fields declared in ArrayList and in every superclass
        assertEquals(Set.of(ArrayList.class, AbstractList.class, AbstractCollection.class, Object.class), owners);
        assertTrue(ArgStampResolution.imageHeapRule(false, false, owners, AbstractList.class));
        assertFalse(ArgStampResolution.imageHeapRule(false, false, owners, java.util.LinkedList.class)); // a subclass is not covered
        assertTrue("unknown heap: fail closed", ArgStampResolution.imageHeapRule(false, false, null, java.util.LinkedList.class));
    }
}
