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
import java.lang.classfile.CodeElement;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;

/**
 * Else-direct premise pins: the soundness premise of the all-branches-direct emission (the ideal invocation model) that
 * `InlineCacheTrivialMethodNodePlugin` implements at rep-list `INLINE_CACHE` sites — the
 * reflection-over-the-real-classes pattern of `EqualsTablePremiseTest`/`RepFreeDirectPremiseTest`,
 * extended to the full trivial population.
 */
public class ElseDirectPremiseTest {

    /* The pre-widening trivial population (the widened set's per-(rep, method) rule: IcWideningPremiseTest). */
    static final Set<String> ALL_TRIVIAL = new TreeSet<>(StringIcMethods.LEGACY_TRIVIAL_NAMES);

    /**
     * The flat registry reps: they keep a real backing {@code value[]}, so the inherited {@code java.lang.String}
     * bodies are correct on them and they may take the direct {@code String.<m>} else (and the DC form). A rep joining
     * this set must be verified flat (extend the spot-check in {@link #everyNonOverridingRegistryRepIsFlat}).
     */
    static final Set<Class<?>> FLAT_REPS = Set.of(SingleByteString.class);

    /**
     * The trivial methods whose inherited {@code java.lang.String} body is field-free: it reads neither {@code value}
     * nor {@code coder} and calls nothing, so it is correct on every receiver, value-null reps included. No rep
     * overrides them (an override of {@code toString} makes every {@code toString} call site polymorphic). The
     * field-freeness is pinned structurally by {@link #fieldFreeInheritedBodiesReadNoFieldAndCallNothing}; a re-added
     * override fails {@link #noRegistryRepDeclaresAFieldFreeTrivialMethod}.
     */
    static final Set<String> FIELD_FREE_INHERITED = Set.of("toString");

    /**
     * The bytecode of every {@code java.lang.String.<name>} declaration, pseudo-instructions (labels, line numbers)
     * dropped. It reads {@code String.class} from the JUnit JVM, which is the same labs builder JDK the images are
     * built with; after a JDK bump, re-check that both are the same JDK.
     */
    static List<List<Opcode>> stringMethodOpcodes(String name) throws IOException {
        byte[] bytes;
        try (InputStream in = String.class.getResourceAsStream("String.class")) {
            Assert.assertNotNull("class bytes of java.lang.String", in);
            bytes = in.readAllBytes();
        }
        List<List<Opcode>> out = new ArrayList<>();
        for (MethodModel mm : ClassFile.of().parse(bytes).methods()) {
            if (mm.methodName().stringValue().equals(name)) {
                List<Opcode> ops = new ArrayList<>();
                for (CodeElement ce : mm.code().orElseThrow()) {
                    if (ce instanceof Instruction ins) {
                        ops.add(ins.opcode());
                    }
                }
                out.add(ops);
            }
        }
        return out;
    }

    /**
     * The premise that lets every rep inherit the {@link #FIELD_FREE_INHERITED} methods (iterated
     * over the set): every JDK declaration of each name reads no field and calls nothing (no NPE on a
     * {@code value == null} receiver), and {@code toString()} is exactly {@code aload_0; areturn} (returns
     * {@code this}, as a {@code return this} override would). A JDK change to such a body fails here.
     */
    @Test
    public void fieldFreeInheritedBodiesReadNoFieldAndCallNothing() throws IOException {
        for (String name : FIELD_FREE_INHERITED) {
            List<List<Opcode>> decls = stringMethodOpcodes(name);
            Assert.assertFalse("String." + name + " declared", decls.isEmpty());
            for (List<Opcode> ops : decls) {
                for (Opcode op : ops) {
                    Assert.assertFalse("String." + name + " reads/writes a field: " + ops, op.kind() == Opcode.Kind.FIELD_ACCESS);
                    Assert.assertFalse("String." + name + " calls something: " + ops, op.kind() == Opcode.Kind.INVOKE || op.kind() == Opcode.Kind.INVOKE_DYNAMIC);
                }
            }
        }
        Assert.assertEquals(List.of(List.of(Opcode.ALOAD_0, Opcode.ARETURN)), stringMethodOpcodes("toString"));
    }

    /** No registry rep declares a field-free inherited trivial method (re-adding the toString override fails here). */
    @Test
    public void noRegistryRepDeclaresAFieldFreeTrivialMethod() {
        Assert.assertTrue(ALL_TRIVIAL.containsAll(FIELD_FREE_INHERITED));
        Set<String> declared = new TreeSet<>();
        for (var e : InlineCacheRegistry.REP_CLASSES.entrySet()) {
            for (String name : FIELD_FREE_INHERITED) {
                if (InlineCacheRegistry.repOverrides(e.getValue(), name)) {
                    declared.add(e.getValue().getSimpleName() + "#" + name);
                }
            }
        }
        Assert.assertTrue("reps overriding a field-free trivial method (makes every call site polymorphic): " + declared, declared.isEmpty());
        // the rep classes outside the registry too (TrivialString)
        for (Class<?> rep : RepPinSupport.repClasses()) {
            for (String name : FIELD_FREE_INHERITED) {
                Assert.assertFalse(rep + " declares " + name, InlineCacheRegistry.repOverrides(rep, name));
            }
        }
    }

    /**
     * The direct-else soundness premise (a missed dispatch would NPE): every {@code value == null} rep
     * overrides every trivial method whose inherited body reads a field (all but {@link #FIELD_FREE_INHERITED},
     * whose inherited body is pinned field-free), so a value-null receiver always takes its own chain branch and never
     * reaches the else-branch's direct {@code String.<m>} body (which reads {@code value()}). Symmetrically
     * this is the DC-form premise: a listed rep set with no overrider is necessarily flat.
     */
    @Test
    public void everyValueNullRepOverridesEveryTrivialMethod() {
        Assert.assertEquals(Set.of("equals", "maybeCustomStringEquals", "length", "hashCode", "charAt", "isEmpty", "toString"),
                        ALL_TRIVIAL);
        for (Class<?> rep : RepInheritedBodyTest.VALUE_NULL_REPS) {
            for (String name : ALL_TRIVIAL) {
                if (FIELD_FREE_INHERITED.contains(name)) {
                    continue;
                }
                Assert.assertTrue(rep + " must override " + name + " (the direct-else/DC-form premise)",
                                InlineCacheRegistry.repOverrides(rep, name));
            }
        }
    }

    /**
     * The stable soundness invariant of the all-branches-direct emission. The plugin decides each branch per (rep,
     * method) at build time ({@code InlineCacheRegistry.repOverrides}, a {@code getDeclaredMethod} check against the
     * real classes), so a frozen override matrix would fail on lawful changes. The invariant the direct
     * {@code String.<m>} else (and the DC form) needs: for every registry rep and every trivial method, either the rep
     * overrides the method (it gets its own branch) or the rep is flat (a real backing {@code value[]}, so the inherited
     * body is correct on it). Today the only non-overrider is {@link SingleByteString} (see {@link #FLAT_REPS}); a new
     * value-null rep inheriting any trivial method fails here (neither an overrider nor flat).
     */
    @Test
    public void everyNonOverridingRegistryRepIsFlat() {
        Set<String> nonFlat = new TreeSet<>();
        for (var e : InlineCacheRegistry.REP_CLASSES.entrySet()) {
            for (String name : ALL_TRIVIAL) {
                if (FIELD_FREE_INHERITED.contains(name)) {
                    continue; // the inherited body is field-free (pinned), correct on every receiver
                }
                if (!InlineCacheRegistry.repOverrides(e.getValue(), name) && !FLAT_REPS.contains(e.getValue())) {
                    nonFlat.add(e.getValue().getSimpleName() + "#" + name);
                }
            }
        }
        Assert.assertTrue("registry reps that inherit a trivial method without being flat (their receivers" + " would ride the direct String.<m> else / the DC form into the inherited body on a" +
                        " null backing value): " + nonFlat,
                        nonFlat.isEmpty());
        /*
         * Flatness spot-check of the named flat set ({@code String.value()} is public in the patched JDK):
         * SingleByteString's constructor passes a real backing String to super, so its {@code value()} is
         * non-null — the mechanical evidence that the inherited String.<m> bodies are correct on it.
         */
        Assert.assertNotNull("SingleByteString (the flat set) must keep a real backing value",
                        SingleByteString.create((byte) 'x').value());
    }
}
