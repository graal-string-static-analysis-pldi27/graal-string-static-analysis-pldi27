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
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * The premise of the terminal-body scope of
 * {@link StringAnalysisPolicy#isTerminalBodyClass} — <b>a terminal body hands the rep it holds only to terminal-body
 * code</b> (so every site outside the terminal bodies is reached by a rep only along a path the walk follows, and its
 * entry is complete like a user-code entry). The receiver side ({@code this} in String's inherited bodies) is pinned by
 * {@link KindTerminalPremiseTest#entryBodiesAreClosed}; this test pins the OPERAND side of the concat machinery and
 * the argument side of String's deflection bodies, against the real bytecode.
 * <p>
 * An <i>escape</i> is an invoke whose owner is outside the terminal-body classes and that has a parameter a rep could
 * be passed as (a supertype of String). A virtual/interface call owned by {@code Object}/{@code CharSequence}/
 * {@code Comparable} is not an escape: on a rep it dispatches into the rep's override or a String body (both terminal).
 */
public class TerminalBodyPremiseTest {

    /** The types a rep can be passed as. */
    private static final Set<String> REP_CARRIER_TYPES = Set.of("Ljava/lang/String;", "Ljava/lang/Object;", "Ljava/lang/CharSequence;", "Ljava/lang/Comparable;",
                    "Ljava/io/Serializable;", "Ljava/lang/constant/Constable;", "Ljava/lang/constant/ConstantDesc;");

    private static final Set<String> DISPATCH_OWNERS = Set.of("java/lang/Object", "java/lang/CharSequence", "java/lang/Comparable");

    /**
     * {@code StringConcatHelper} (the runtime concat machinery; {@code StringConcatFactory} runs at build time, its
     * strategies only bind/generate calls into StringConcatHelper): the escapes are exactly the exception-message and
     * method-lookup calls below, none of which receives an operand — the messages are built from literals and ints
     * ({@code newString}, {@code checkOverflow}, {@code newArray}), and {@code lookupStatic}'s String is the constant
     * name of a StringConcatHelper method (its only callers pass literals). {@code stringOf}'s {@code Object.toString}
     * dispatches on the operand (not an escape). A JDK change adding an escape fails here.
     */
    @Test
    public void concatMachineryHandsOperandsOnlyToTerminalBodies() throws Exception {
        Class<?> sch = Class.forName("java.lang.StringConcatHelper");
        Assert.assertTrue(StringAnalysisPolicy.isTerminalBodyClass(sch.getName()));
        Set<String> escapes = escapes(parse(sch), null);
        Assert.assertEquals(new TreeSet<>(Set.of(
                        "checkOverflow(J)J -> java/lang/OutOfMemoryError.<init>(Ljava/lang/String;)V",
                        "checkOverflow(I)I -> java/lang/OutOfMemoryError.<init>(Ljava/lang/String;)V",
                        "newArray(I)[B -> java/lang/OutOfMemoryError.<init>(Ljava/lang/String;)V",
                        "newString([BJ)Ljava/lang/String; -> java/lang/InternalError.<init>(Ljava/lang/String;)V",
                        "newString([BJ)Ljava/lang/String; -> java/lang/StringBuilder.append(Ljava/lang/String;)Ljava/lang/StringBuilder;",
                        "lookupStatic(Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/MethodHandle; -> java/lang/invoke/MethodHandles$Lookup.findStatic(Ljava/lang/Class;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/MethodHandle;",
                        "lookupStatic(Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/MethodHandle; -> java/lang/AssertionError.<init>(Ljava/lang/Object;)V")),
                        escapes);
        // none of the message/lookup methods takes an operand-typed parameter other than lookupStatic's constant name
        for (MethodModel mm : parse(sch).methods()) {
            String n = mm.methodName().stringValue();
            if (n.equals("checkOverflow") || n.equals("newArray") || n.equals("newString")) {
                for (ClassDesc p : MethodTypeDesc.ofDescriptor(mm.methodType().stringValue()).parameterList()) {
                    Assert.assertFalse(n + " takes a rep-carrier parameter", REP_CARRIER_TYPES.contains(p.descriptorString()));
                }
            }
        }
    }

    /**
     * String's deflection bodies (the equals / compareTo argument terminals and the REDIRECT target, {@link
     * TerminalBodyKinds#isDeflectionBody}) run with a rep as their argument: they hand it nowhere outside String and the
     * rep's own dispatch.
     */
    @Test
    public void deflectionBodiesHandTheArgumentOnlyToTerminalBodies() throws IOException {
        ClassModel string = parse(String.class);
        int bodies = 0;
        for (MethodModel mm : string.methods()) {
            if (mm.code().isPresent() && TerminalBodyKinds.isDeflectionBody("java.lang.String", mm.methodName().stringValue(), mm.methodType().stringValue())) {
                bodies++;
            }
        }
        // the stock compareTo(String) is not one; maybeCustomStringCompareTo(String) is
        Assert.assertEquals("equals(Object), compareTo(Object), maybeCustomStringEquals(Object), maybeCustomStringCompareTo(String)", 4, bodies);
        Assert.assertEquals(Set.of(), escapes(string, mm -> TerminalBodyKinds.isDeflectionBody("java.lang.String", mm.methodName().stringValue(), mm.methodType().stringValue())));
    }

    private static Set<String> escapes(ClassModel cm, java.util.function.Predicate<MethodModel> filter) {
        Set<String> out = new TreeSet<>();
        for (MethodModel mm : cm.methods()) {
            if (mm.code().isEmpty() || (filter != null && !filter.test(mm))) {
                continue;
            }
            for (CodeElement ce : mm.code().get()) {
                if (!(ce instanceof InvokeInstruction inv)) {
                    continue;
                }
                String owner = inv.owner().asInternalName();
                if (StringAnalysisPolicy.isTerminalBodyClass(owner.replace('/', '.'))) {
                    continue;
                }
                if ((inv.opcode() == Opcode.INVOKEVIRTUAL || inv.opcode() == Opcode.INVOKEINTERFACE) && DISPATCH_OWNERS.contains(owner)) {
                    continue;
                }
                boolean carrier = false;
                for (ClassDesc p : inv.typeSymbol().parameterList()) {
                    carrier |= REP_CARRIER_TYPES.contains(p.descriptorString());
                }
                if (carrier) {
                    out.add(mm.methodName().stringValue() + mm.methodType().stringValue() + " -> " + owner + "." + inv.name().stringValue() + inv.type().stringValue());
                }
            }
        }
        return out;
    }

    private static ClassModel parse(Class<?> c) throws IOException {
        try (InputStream in = c.getResourceAsStream(c.getSimpleName() + ".class")) {
            Assert.assertNotNull("class bytes of " + c, in);
            return ClassFile.of().parse(in.readAllBytes());
        }
    }
}
