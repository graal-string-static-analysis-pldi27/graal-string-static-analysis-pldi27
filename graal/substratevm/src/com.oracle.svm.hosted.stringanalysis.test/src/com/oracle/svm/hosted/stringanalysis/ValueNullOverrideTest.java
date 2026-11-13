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

import java.io.IOException;
import java.io.InputStream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

/**
 * Flat delivery: the IC lowering sends every listed rep that does not override the site's method to the direct
 * {@code String.<m>} else, value-carrying or not. That is sound by dispatch equivalence, not by this pin: the direct
 * else is used only when {@code TerminalBodyKinds.implementingClass(rep, m) == String.class}, the JVM's own selection,
 * so it binds the same body the stock virtual call binds on that rep. This pin guards the separate premise that such an
 * inherited body is correct on a value-null rep wherever a whitelist lets that rep reach the method's receiver: for
 * every (value-null rep, whitelisted inherited method) pair ({@link RepInheritedBodyTest#inheritedWhitelistedPairs}),
 * incl. the unknown-variant {@code W_lazy[null->..]} rows, String's body never touches {@code value} nor calls
 * {@code value()}/{@code valueRaw()}, and every String instance method it calls is overridden by that rep or is itself
 * such a pair. Only calls owned by {@code java/lang/String} are followed; a {@code this} handed to another class rests
 * on the E_K and terminal-body pins.
 */
public class ValueNullOverrideTest {

    record Pair(Class<?> rep, Method m) {
    }

    static List<Pair> inheritedValueNullPairs() {
        List<Pair> out = new ArrayList<>();
        for (HandListLeakWhitelistTest.RepWhitelist w : HandListLeakWhitelistTest.repWhitelists()) {
            Class<?> rep = w.representation();
            if (rep == null || InlineCacheRegistry.isValueCarryingFlatRep(rep)) {
                continue;
            }
            for (Method m : String.class.getDeclaredMethods()) {
                if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers())) {
                    continue;
                }
                if (w.whitelist().admits(m.getName(), StringTerminalHandList.STRING, RepPinSupport.signature(m)) &&
                                !RepPinSupport.isRep(RepInheritedBodyTest.implementingClass(rep, m)) && !out.contains(new Pair(rep, m))) {
                    out.add(new Pair(rep, m)); // a pair admitted by several rows (a variant and its null-> row) once
                }
            }
        }
        return out;
    }

    static ClassModel stringClass() throws IOException {
        try (InputStream in = ValueNullOverrideTest.class.getResourceAsStream("/java/lang/String.class")) {
            Assert.assertNotNull("the class file of java.lang.String is readable", in);
            return ClassFile.of().parse(in.readAllBytes());
        }
    }

    static MethodModel bodyOf(ClassModel cm, Method m) {
        String desc = TerminalBodyKinds.nameAndDescriptor(m);
        for (MethodModel mm : cm.methods()) {
            if ((mm.methodName().stringValue() + mm.methodType().stringValue()).equals(desc)) {
                return mm;
            }
        }
        throw new AssertionError("no body " + desc + " in java.lang.String");
    }

    static Method stringInstanceMethod(String name, String descriptor) {
        for (Method m : String.class.getDeclaredMethods()) {
            if (!Modifier.isStatic(m.getModifiers()) && TerminalBodyKinds.nameAndDescriptor(m).equals(name + descriptor)) {
                return m;
            }
        }
        return null;
    }

    /**
     * The reps this pin walks ({@code HandListLeakWhitelistTest.repWhitelists}) are exactly the
     * value-null reps the IC registry can list ({@code InlineCacheRegistry.REP_CLASSES}): a registered value-null rep
     * without a whitelist row would otherwise bypass the pin.
     */
    @Test
    public void theRepSetIsTheRegistrysValueNullReps() {
        Set<Class<?>> pinned = new HashSet<>();
        for (HandListLeakWhitelistTest.RepWhitelist w : HandListLeakWhitelistTest.repWhitelists()) {
            if (w.representation() != null && !InlineCacheRegistry.isValueCarryingFlatRep(w.representation())) {
                pinned.add(w.representation());
            }
        }
        Set<Class<?>> registry = new HashSet<>();
        for (Class<?> rep : InlineCacheRegistry.REP_CLASSES.values()) {
            if (!InlineCacheRegistry.isValueCarryingFlatRep(rep)) {
                registry.add(rep);
            }
        }
        Assert.assertFalse("non-vacuous", registry.isEmpty());
        Assert.assertEquals(registry, pinned);
    }

    @Test
    public void everyInheritedWhitelistedBodyOfAValueNullRepIsValueFree() throws IOException {
        ClassModel cm = stringClass();
        List<Pair> pairs = inheritedValueNullPairs();
        Assert.assertFalse("non-vacuous: the pinned inherited pairs exist", pairs.isEmpty());
        List<String> wrong = new ArrayList<>();
        for (Pair p : pairs) {
            CodeModel code = bodyOf(cm, p.m()).code().orElse(null);
            Assert.assertNotNull("String." + p.m().getName() + " has code", code);
            for (CodeElement e : code) {
                if (e instanceof FieldInstruction fi && fi.owner().asInternalName().equals("java/lang/String") && fi.name().stringValue().equals("value")) {
                    wrong.add(p.rep().getSimpleName() + " inherits String." + TerminalBodyKinds.nameAndDescriptor(p.m()) + " which touches value: " + fi);
                } else if (e instanceof InvokeInstruction ii && ii.owner().asInternalName().equals("java/lang/String") && ii.opcode() != Opcode.INVOKESTATIC) {
                    String name = ii.name().stringValue();
                    if (name.equals("value") || name.equals("valueRaw")) {
                        wrong.add(p.rep().getSimpleName() + " inherits String." + TerminalBodyKinds.nameAndDescriptor(p.m()) + " which calls " + name + "()");
                        continue;
                    }
                    Method callee = stringInstanceMethod(name, ii.type().stringValue());
                    if (callee == null || name.equals("<init>")) {
                        continue;
                    }
                    boolean overridden = RepPinSupport.isRep(RepInheritedBodyTest.implementingClass(p.rep(), callee));
                    boolean pinned = pairs.contains(new Pair(p.rep(), callee));
                    if (!overridden && !pinned) {
                        wrong.add(p.rep().getSimpleName() + " inherits String." + TerminalBodyKinds.nameAndDescriptor(p.m()) + " which calls the inherited, unpinned String." + name +
                                        ii.type().stringValue());
                    }
                }
            }
        }
        Assert.assertEquals("value-null reps inheriting a value-reading whitelisted String body", List.of(), wrong);
    }
}
