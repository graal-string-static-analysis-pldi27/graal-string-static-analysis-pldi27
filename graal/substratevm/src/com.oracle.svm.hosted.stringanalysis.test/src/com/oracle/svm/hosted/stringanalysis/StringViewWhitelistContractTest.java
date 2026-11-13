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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

public class StringViewWhitelistContractTest {

    private enum ImplementationKind {
        OVERRIDE,
        AUDITED_INHERITED,
        STATIC_NO_RECEIVER
    }

    private static final Map<String, String> AUDITED_SAFE_INHERITED = Map.of(
                    "coder()", "reads only inherited coder field",
                    "isLatin1()", "reads only inherited coder field",
                    "contentEquals(Ljava/lang/StringBuffer;)", "delegates virtually to overridden contentEquals(CharSequence)",
                    // StringView does not override toString() (pinned by ElseDirectPremiseTest)
                    "toString()", "returns this; reads no field (String.toString is aload_0; areturn)");

    private static final Set<String> EXPECTED_STATIC = Set.of(
                    "valueOf(Ljava/lang/Object;)", "valueOf([C)", "valueOf([C,I,I)",
                    "valueOf(Z)", "valueOf(C)", "valueOf(I)", "valueOf(J)",
                    "valueOf(F)", "valueOf(D)");

    @Test
    public void everyAcceptedSignatureHasAnExplicitCompatibleImplementationCategory() {
        Map<String, Method> stringMethods = new HashMap<>();
        for (Method method : String.class.getDeclaredMethods()) {
            stringMethods.put(key(method), method);
        }
        Map<String, ImplementationKind> categories = new HashMap<>();

        for (String accepted : StringViewWhitelist.acceptedSignatures()) {
            Method stringMethod = stringMethods.get(accepted);
            Assert.assertNotNull("Whitelist signature does not exist on this JDK: " + accepted, stringMethod);
            Assert.assertFalse("Synthetic String declaration must not be accepted: " + accepted, stringMethod.isSynthetic());
            Assert.assertFalse("Bridge String declaration must not be accepted: " + accepted, stringMethod.isBridge());
            if (Modifier.isStatic(stringMethod.getModifiers())) {
                categories.put(accepted, ImplementationKind.STATIC_NO_RECEIVER);
                continue;
            }
            Assert.assertFalse("Private method cannot be a receiver contract: " + accepted,
                            Modifier.isPrivate(stringMethod.getModifiers()));
            if (AUDITED_SAFE_INHERITED.containsKey(accepted)) {
                categories.put(accepted, ImplementationKind.AUDITED_INHERITED);
                continue;
            }
            Method implementation;
            try {
                implementation = StringView.class.getDeclaredMethod(stringMethod.getName(), stringMethod.getParameterTypes());
            } catch (NoSuchMethodException ex) {
                throw new AssertionError("Accepted receiver signature has no StringView override or audited inherited implementation: " + accepted, ex);
            }
            Assert.assertSame(StringView.class, implementation.getDeclaringClass());
            Assert.assertFalse("Override must not be static: " + accepted, Modifier.isStatic(implementation.getModifiers()));
            Assert.assertFalse("Override must not be private: " + accepted, Modifier.isPrivate(implementation.getModifiers()));
            Assert.assertFalse("Synthetic override is not an audited implementation: " + accepted, implementation.isSynthetic());
            Assert.assertFalse("Bridge override is not an audited implementation: " + accepted, implementation.isBridge());
            Assert.assertTrue("Incompatible return type for " + accepted,
                            stringMethod.getReturnType().isAssignableFrom(implementation.getReturnType()));
            categories.put(accepted, ImplementationKind.OVERRIDE);
        }

        Assert.assertEquals(StringViewWhitelist.acceptedSignatures(), categories.keySet());
        Set<String> actualStatic = new HashSet<>();
        categories.forEach((signature, kind) -> {
            if (kind == ImplementationKind.STATIC_NO_RECEIVER) {
                actualStatic.add(signature);
            }
        });
        Assert.assertEquals(EXPECTED_STATIC, actualStatic);
        Assert.assertEquals(AUDITED_SAFE_INHERITED.keySet(), categories.entrySet().stream()
                        .filter(entry -> entry.getValue() == ImplementationKind.AUDITED_INHERITED)
                        .map(Map.Entry::getKey).collect(java.util.stream.Collectors.toSet()));
    }

    private static String key(Method method) {
        StringBuilder result = new StringBuilder(method.getName()).append('(');
        Class<?>[] parameters = method.getParameterTypes();
        for (int i = 0; i < parameters.length; i++) {
            if (i != 0) {
                result.append(',');
            }
            result.append(descriptor(parameters[i]));
        }
        return result.append(')').toString();
    }

    private static String descriptor(Class<?> type) {
        if (type.isArray()) {
            return type.getName().replace('.', '/');
        }
        if (!type.isPrimitive()) {
            return "L" + type.getName().replace('.', '/') + ";";
        }
        if (type == boolean.class) {
            return "Z";
        } else if (type == byte.class) {
            return "B";
        } else if (type == char.class) {
            return "C";
        } else if (type == short.class) {
            return "S";
        } else if (type == int.class) {
            return "I";
        } else if (type == long.class) {
            return "J";
        } else if (type == float.class) {
            return "F";
        } else if (type == double.class) {
            return "D";
        } else if (type == void.class) {
            return "V";
        }
        throw new AssertionError(type);
    }
}
