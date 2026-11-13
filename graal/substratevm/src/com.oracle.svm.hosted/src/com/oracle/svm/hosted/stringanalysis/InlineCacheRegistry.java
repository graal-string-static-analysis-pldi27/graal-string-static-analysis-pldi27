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
import java.util.Map;

import com.oracle.svm.core.stringrep.ArrayLazyString;
import com.oracle.svm.core.stringrep.FixedConcat4;
import com.oracle.svm.core.stringrep.InterleavedStringArray;
import com.oracle.svm.core.stringrep.RopeString;
import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.core.stringrep.ThreeWayString;

final class InlineCacheRegistry {

    static final Map<String, Class<?>> REP_CLASSES = Map.of(
                    "ROPE", RopeString.class,
                    "SV", StringView.class,
                    "THREE_WAY", ThreeWayString.class,
                    "FIXED4", FixedConcat4.class,
                    "ARRAY_LAZY", ArrayLazyString.class,
                    "INTERLEAVED", InterleavedStringArray.class,
                    "SBS", SingleByteString.class);

    static Class<?> getRepClass(String repName) {
        return REP_CLASSES.get(repName);
    }

    static Class<?>[] getParamTypes(String methodName) {
        return switch (methodName) {
            case "equals", "maybeCustomStringEquals" -> new Class<?>[]{Object.class};
            case "maybeCustomStringCompareTo" -> new Class<?>[]{String.class}; // the compareTo mirror
            case "charAt" -> new Class<?>[]{int.class};
            /* Only the coder copy primitive getBytes(byte[],int,byte) reaches the plugin (descriptor-gated). */
            case "getBytes" -> new Class<?>[]{byte[].class, int.class, byte.class};
            default -> new Class<?>[0];
        };
    }

    /**
     * A flat (value-carrying) rep keeps String's {@code value}/{@code coder} set, so String's inherited bodies are correct
     * on it. Derived from the class files: a rep is value-null iff some constructor of it (or of a superclass below
     * String) calls {@code String(byte coder)} ({@code invokespecial java/lang/String.<init>(B)V}, the only String
     * constructor that leaves {@code value == null}); every other rep is flat. Pinned by {@code FlatRepPremiseTest}
     * (the partition, {@code value()} non-null exactly on flat instances, and every flat override content-equivalent to
     * String's body).
     */
    static boolean isValueCarryingFlatRep(Class<?> repClass) {
        return FLAT.get(repClass);
    }

    /** The descriptor of String's value-null constructor {@code String(byte coder)}. */
    static final String VALUE_NULL_CONSTRUCTOR = "(B)V";

    private static final ClassValue<Boolean> FLAT = new ClassValue<>() {
        @Override
        protected Boolean computeValue(Class<?> repClass) {
            if (repClass == String.class || !String.class.isAssignableFrom(repClass)) {
                return false;
            }
            for (Class<?> c = repClass; c != String.class; c = c.getSuperclass()) {
                if (callsValueNullConstructor(c)) {
                    return false;
                }
            }
            return true;
        }
    };

    /** Does a constructor of {@code c} invoke {@code java.lang.String.<init>(B)V}? (class-file scan) */
    static boolean callsValueNullConstructor(Class<?> c) {
        byte[] bytes;
        try (java.io.InputStream in = c.getResourceAsStream("/" + c.getName().replace('.', '/') + ".class")) {
            if (in == null) {
                throw new IllegalStateException("no class file for " + c.getName());
            }
            bytes = in.readAllBytes();
        } catch (java.io.IOException e) {
            throw new java.io.UncheckedIOException(c.getName(), e);
        }
        for (java.lang.classfile.MethodModel mm : java.lang.classfile.ClassFile.of().parse(bytes).methods()) {
            if (!mm.methodName().equalsString("<init>") || mm.code().isEmpty()) {
                continue;
            }
            for (java.lang.classfile.CodeElement ce : mm.code().get()) {
                if (ce instanceof java.lang.classfile.instruction.InvokeInstruction inv && inv.opcode() == java.lang.classfile.Opcode.INVOKESPECIAL &&
                                inv.owner().asInternalName().equals("java/lang/String") && inv.name().equalsString("<init>") &&
                                inv.type().equalsString(VALUE_NULL_CONSTRUCTOR)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Does the rep implement String's {@code methodName} (the {@link #getParamTypes} overload) itself? The JVM's
     * selection, {@link TerminalBodyKinds#implementingClass} (one override decision).
     */
    static boolean repOverrides(Class<?> repClass, String methodName) {
        try {
            Method m = String.class.getDeclaredMethod(methodName, getParamTypes(methodName));
            Class<?> impl = TerminalBodyKinds.implementingClass(repClass, m);
            return impl != null && impl != String.class;
        } catch (NoSuchMethodException e) {
            return false;
        }
    }

    private InlineCacheRegistry() {
    }
}