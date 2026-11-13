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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * The method set of the inline cache, shared by the child ({@link InlineCacheProfilingHeuristic}: which call vertices
 * get an {@code INLINE_CACHE} entry) and the parent ({@link InlineCacheTrivialMethodNodePlugin}: which String-declared
 * invokes it may lower). Derived by reflection: every non-private instance method declared by the builder JDK's
 * {@code java.lang.String} (so {@code maybeCustomStringEquals} and the protected {@code getBytes([BIB)V} are members;
 * bridges included). Sites are matched by name and descriptor, never by name alone: the child by name + usage
 * signature ({@link TerminalBodyKinds#usageSignature}), the parent by the full {@code name(desc)ret}.
 */
final class StringIcMethods {

    /** The narrow trivial-method population (the IC plugin's census labels the other members "/widened"). */
    static final Set<String> LEGACY_TRIVIAL_NAMES = Set.of(
                    "equals",
                    "maybeCustomStringEquals",
                    "length",
                    "hashCode",
                    "charAt",
                    "isEmpty",
                    "toString");

    static final String GETBYTES_CODER_KEY = "getBytes([BIB)V";

    /** {@code name(desc)ret} -> the reflected String method. */
    private static final Map<String, Method> BY_DESCRIPTOR;
    /** {@code name|usageSignature} (the child's site key) -> present. */
    private static final Set<String> BY_USAGE;

    static {
        Map<String, Method> d = new LinkedHashMap<>();
        Set<String> u = new TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            int mod = m.getModifiers();
            if (Modifier.isStatic(mod) || Modifier.isPrivate(mod)) {
                continue;
            }
            d.put(TerminalBodyKinds.nameAndDescriptor(m), m);
            u.add(m.getName() + "|" + TerminalBodyKinds.usageSignature(m));
        }
        BY_DESCRIPTOR = Collections.unmodifiableMap(d);
        BY_USAGE = Collections.unmodifiableSet(u);
    }

    /** The set, as {@code name(desc)ret} keys. */
    static Set<String> descriptors() {
        return BY_DESCRIPTOR.keySet();
    }

    /** The reflected String method of an IC member, or null when {@code name(desc)ret} is not a member. */
    static Method lookup(String nameAndDescriptor) {
        return BY_DESCRIPTOR.get(nameAndDescriptor);
    }

    /** Child: is a String-declared call vertex (name, usage signature) an IC member? */
    static boolean isMemberSite(String name, String usageSignature) {
        return BY_USAGE.contains(name + "|" + (usageSignature == null ? "" : usageSignature));
    }

    /** Child: is {@code name} the name of some member (a descriptor mismatch then is an "unknown descriptor" site)? */
    static boolean isMemberName(String name) {
        for (String k : BY_USAGE) {
            if (k.startsWith(name + "|")) {
                return true;
            }
        }
        return false;
    }

    private StringIcMethods() {
    }
}
