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
import java.lang.classfile.attribute.InnerClassInfo;
import java.lang.classfile.attribute.InnerClassesAttribute;
import java.lang.classfile.instruction.ArrayStoreInstruction;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

/**
 * Rep code never passes a rep ({@code this}, or a {@code String}/{@code CharSequence}/{@code Object}/{@code Comparable}-
 * typed value it received) to a method outside the rep classes, except as the receiver of a virtual call. The child
 * never walks rep code, so such a value would reach shared JDK code on an edge no tracked flow covers; a direct call
 * there would run a {@code String} body on a rep.
 * <p>
 * The check reads the class files of every rep class of {@link RepPinSupport#repClasses()} and their nested classes.
 * Findings: every invoke from rep code to a non-rep owner whose descriptor takes a reference parameter of one of those
 * types (or an array of one), and every {@code invokespecial} of a non-constructor on a non-rep owner (a
 * {@code super.m()}: the rep runs a shared body as its {@code this}). A finding passes only if {@link #ALLOWLIST} lists
 * it with a reason, or if it is an exception-style {@code <init>(String)} whose argument the immediately preceding
 * instruction makes from primitives only ({@code makeConcatWithConstants} with no reference operand) or as a constant.
 * Every allowlist entry must be used exactly as often as pinned ({@link #COUNTS}, default once).
 * <p>
 * Three further channels: (i) the flagged parameter types also include {@code Serializable}, {@code Constable},
 * {@code ConstantDesc} (String implements all three) and every rep class; (ii) every reference {@code putfield} /
 * {@code putstatic} is a finding unless it targets the storing class's own private field, and so is every
 * {@code aastore}; (iii) a virtual call on a rep of the calling class ({@code this} or a value of that static type) to a
 * method that class does not declare, i.e. an inherited {@code String} body run on a rep. Auto-cleared for (iii):
 * exactly the inherited pairs {@code RepInheritedBodyTest.EXPECTED_INHERITED} pins, all reading only the {@code coder}
 * field that {@code super(coder)} set.
 */
public class RepEscapeTest {

    static final String REP_PACKAGE_INTERNAL = RepPinSupport.REP_PACKAGE.replace('.', '/') + "/";

    static final Set<String> FLAGGED = Set.of("Ljava/lang/String;", "Ljava/lang/CharSequence;", "Ljava/lang/Object;", "Ljava/lang/Comparable;",
                    "Ljava/io/Serializable;", "Ljava/lang/constant/Constable;", "Ljava/lang/constant/ConstantDesc;");

    /** The owners of a virtual call that can dispatch to an inherited {@code String} body: String and its supertypes. */
    static final Set<String> STRING_AND_SUPERS = Set.of("java/lang/String", "java/lang/Object", "java/lang/CharSequence", "java/lang/Comparable",
                    "java/io/Serializable", "java/lang/constant/Constable", "java/lang/constant/ConstantDesc");

    /** Pinned findings: {@code Caller.method(desc) -> owner.name(desc)}, each with its reason. */
    static final Map<String, String> ALLOWLIST = allowlist();

    private static Map<String, String> allowlist() {
        Map<String, String> m = new LinkedHashMap<>();
        String copy = "arrays only: the two Object parameters are the backing byte[] and the destination byte[]";
        String fwd = "forwards the caller's own argument, unchanged, to the same String method on a plain materialized copy " +
                        "(a flat String receiver): the child walked that argument into that very body at the caller's site";
        String flatInit = "flat rep constructor super(String.valueOf((char) b)): the argument is a fresh one-char plain String, " +
                        "never a rep (the rep under construction is only the receiver)";
        String flatCharAt = "flat rep (a real value[] of length 1): super.charAt(index) only for index != 0, which always throws the JDK's own " +
                        "StringIndexOutOfBoundsException; only the int index is passed, the rep is the receiver of its own String body";
        String poolFill = "SingleByteString.<clinit> fills its private static POOL with fresh instances: the heap-check pool (RepHeapPoolTest pins the " +
                        "pool's readers: only the factories, at replaced sites)";
        String inheritedA4 = "an inherited String body run with the view as this: exactly the pinned pair (RepInheritedBodyTest); it reads " +
                        "only the String.coder field that the String(byte) constructor set, and passes nothing on";
        m.put("StringView.getBytes([BIB)V -> java/lang/System.arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", copy);
        m.put("StringView.getBytes(II[BI)V -> java/lang/System.arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", copy);
        // The protected ranged copy getBytes(byte[],int,int,byte,int) (offset-aware copy from the backing)
        m.put("StringView.getBytes([BIIBI)V -> java/lang/System.arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", copy);
        // The shared encoder (scanned as a nested class of RepParts, which the reps reference): the ISO-8859-1
        // copy of a Latin-1 part's (or a view's backing) bytes into the fresh output array
        m.put("RepParts$Enc.latin1([BII)V -> java/lang/System.arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", copy);
        m.put("StringView.encodeLatin1([BIII)[B -> java/lang/System.arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V", copy); // the ASCII prefix byte[] -> byte[]
        m.put("StringView.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("StringView.regionMatches(ZILjava/lang/String;II)Z -> java/lang/String.regionMatches(ZILjava/lang/String;II)Z", fwd);
        m.put("RopeString.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("ThreeWayString.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("FixedConcat4.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("ArrayLazyString.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("InterleavedStringArray.getBytes(Ljava/lang/String;)[B -> java/lang/String.getBytes(Ljava/lang/String;)[B", fwd);
        m.put("SingleByteString.<init>(B)V -> java/lang/String.<init>(Ljava/lang/String;)V", flatInit);
        m.put("TrivialString.<init>(B)V -> java/lang/String.<init>(Ljava/lang/String;)V", flatInit);
        m.put("SingleByteString.charAt(I)C -> java/lang/String.charAt(I)C", flatCharAt);
        m.put("TrivialString.charAt(I)C -> java/lang/String.charAt(I)C", flatCharAt);
        m.put("SingleByteString.<clinit>()V -> aastore", poolFill);
        // The alias read of AbstractStringBuilder.maybeLatin1; the argument is the StringBuilder/StringBuffer of
        // create(StringBuilder|StringBuffer), never a rep, and SubstrateUtil.cast is a no-op intrinsic (no call at runtime)
        m.put("StringView.builderMaybeLatin1(Ljava/lang/Object;)Z -> com/oracle/svm/core/SubstrateUtil.cast(Ljava/lang/Object;Ljava/lang/Class;)Ljava/lang/Object;",
                        "the builder of create(StringBuilder|StringBuffer), never a rep: SubstrateUtil.cast to the AbstractStringBuilder alias " +
                                        "(a no-op intrinsic) to read its maybeLatin1 field");
        // The alias read of AbstractStringBuilder.count under the StringBuffer's monitor; the argument
        // is the StringBuffer of create/createSkipCheck(StringBuffer), never a rep
        m.put("StringView.lockedBufferCount(Ljava/lang/StringBuffer;)I -> com/oracle/svm/core/SubstrateUtil.cast(Ljava/lang/Object;Ljava/lang/Class;)Ljava/lang/Object;",
                        "the StringBuffer of create/createSkipCheck(StringBuffer), never a rep: SubstrateUtil.cast to the AbstractStringBuilder alias " +
                                        "(a no-op intrinsic) to read its count field under the held monitor");
        // The one alias cast of the StringJoiner (ofJoiner's argument, or the rep's delimiter slot holding the
        // joiner); the argument is the joiner, never a rep
        m.put("InterleavedStringArray.alias(Ljava/lang/Object;)Lcom/oracle/svm/core/stringrep/Target_java_util_StringJoiner; -> " +
                        "com/oracle/svm/core/SubstrateUtil.cast(Ljava/lang/Object;Ljava/lang/Class;)Ljava/lang/Object;",
                        "the StringJoiner of an admitted extraction (ofJoiner's argument or the joiner held in the delimiter slot), never a rep: " +
                                        "SubstrateUtil.cast to the StringJoiner alias (a no-op intrinsic) to read its prefix/suffix/delimiter/elts/size/len fields");
        return m;
    }

    /** The pinned number of occurrences of an allowlisted finding, when it is not 1. */
    static final Map<String, Integer> COUNTS = Map.of();

    record Finding(String key, boolean autoCleared, int count) {
    }

    /** The internal names of every class of the rep package, the rep classes and everything nested in them. */
    static Map<String, ClassModel> repClassModels() throws IOException {
        Map<String, ClassModel> out = new TreeMap<>();
        Deque<String> work = new ArrayDeque<>();
        for (Class<?> c : RepPinSupport.repClasses()) {
            work.add(c.getName().replace('.', '/'));
        }
        while (!work.isEmpty()) {
            String internal = work.poll();
            if (out.containsKey(internal)) {
                continue;
            }
            ClassModel cm = ClassFile.of().parse(read(internal));
            out.put(internal, cm);
            for (InnerClassesAttribute ica : cm.findAttributes(java.lang.classfile.Attributes.innerClasses())) {
                for (InnerClassInfo ici : ica.classes()) {
                    String inner = ici.innerClass().asInternalName();
                    if (inner.startsWith(REP_PACKAGE_INTERNAL)) {
                        work.add(inner);
                    }
                }
            }
        }
        return out;
    }

    private static byte[] read(String internalName) throws IOException {
        try (InputStream in = RepEscapeTest.class.getResourceAsStream("/" + internalName + ".class")) {
            Assert.assertNotNull("class file of " + internalName, in);
            return in.readAllBytes();
        }
    }

    /** A type a rep can be passed as: a {@link #FLAGGED} type, a rep class, or an array of one. */
    static boolean flaggedType(String descriptor) {
        String d = descriptor;
        while (d.startsWith("[")) {
            d = d.substring(1);
        }
        return FLAGGED.contains(d) || d.startsWith("L" + REP_PACKAGE_INTERNAL);
    }

    static boolean flaggedParameter(MethodTypeDesc desc) {
        for (ClassDesc p : desc.parameterList()) {
            if (flaggedType(p.descriptorString())) {
                return true;
            }
        }
        return false;
    }

    static boolean declares(ClassModel cm, String name, String descriptor) {
        for (MethodModel mm : cm.methods()) {
            if (mm.methodName().stringValue().equals(name) && mm.methodType().stringValue().equals(descriptor)) {
                return true;
            }
        }
        return false;
    }

    static boolean privateField(ClassModel cm, String name, String descriptor) {
        for (var fm : cm.fields()) {
            if (fm.fieldName().stringValue().equals(name) && fm.fieldType().stringValue().equals(descriptor)) {
                return fm.flags().has(AccessFlag.PRIVATE);
            }
        }
        return false;
    }

    static boolean loadsThis(CodeElement e) {
        return e instanceof LoadInstruction li && li.slot() == 0 && li.typeKind() == java.lang.classfile.TypeKind.REFERENCE;
    }

    private static void add(Map<String, Finding> out, String key, boolean auto) {
        Finding prior = out.get(key);
        out.put(key, new Finding(key, auto && (prior == null || prior.autoCleared()), prior == null ? 1 : prior.count() + 1));
    }

    static boolean primitivesOnly(MethodTypeDesc desc) {
        for (ClassDesc p : desc.parameterList()) {
            if (!p.isPrimitive()) {
                return false;
            }
        }
        return true;
    }

    /**
     * The auto-cleared message argument: the instruction just before the {@code <init>(String)} is a
     * {@code makeConcatWithConstants} with primitive operands only, or a constant String load.
     */
    static boolean messageOfPrimitivesOrConstant(CodeElement previous) {
        if (previous instanceof InvokeDynamicInstruction indy) {
            return indy.name().stringValue().equals("makeConcatWithConstants") && primitivesOnly(indy.typeSymbol());
        }
        return previous instanceof ConstantInstruction ci && ci.constantValue() instanceof String;
    }

    static String simple(String internalName) {
        return internalName.substring(internalName.lastIndexOf('/') + 1);
    }

    /** Every finding of rep code, in scan order. */
    static Map<String, Finding> findings(Map<String, ClassModel> models) {
        Map<String, Finding> out = new TreeMap<>();
        for (ClassModel cm : models.values()) {
            String self = cm.thisClass().asInternalName();
            String caller = simple(self);
            for (MethodModel mm : cm.methods()) {
                String where = caller + "." + mm.methodName().stringValue() + mm.methodType().stringValue();
                boolean instanceMethod = !mm.flags().has(AccessFlag.STATIC);
                CodeModel code = mm.code().orElse(null);
                if (code == null) {
                    continue;
                }
                CodeElement previous = null;
                CodeElement previous2 = null;
                for (CodeElement e : code) {
                    if (e instanceof InvokeInstruction ii) {
                        String owner = ii.owner().asInternalName();
                        String name = ii.name().stringValue();
                        MethodTypeDesc desc = ii.typeSymbol();
                        String callee = owner + "." + name + ii.type().stringValue();
                        boolean virtual = ii.opcode() == Opcode.INVOKEVIRTUAL || ii.opcode() == Opcode.INVOKEINTERFACE;
                        if (!owner.startsWith(REP_PACKAGE_INTERNAL)) {
                            boolean superCall = ii.opcode() == Opcode.INVOKESPECIAL && !name.equals("<init>");
                            if (superCall || flaggedParameter(desc)) {
                                boolean auto = !superCall && name.equals("<init>") && desc.parameterCount() == 1 &&
                                                desc.parameterType(0).descriptorString().equals("Ljava/lang/String;") &&
                                                messageOfPrimitivesOrConstant(previous);
                                add(out, where + " -> " + callee, auto);
                            }
                            // (iii) this.m() with a String-supertype owner: the receiver is the aload_0 just before (or a cast of it)
                            boolean thisReceiver = instanceMethod && desc.parameterCount() == 0 &&
                                            (loadsThis(previous) || (previous instanceof TypeCheckInstruction && loadsThis(previous2)));
                            if (virtual && thisReceiver && STRING_AND_SUPERS.contains(owner) && !declares(cm, name, ii.type().stringValue())) {
                                add(out, where + " -> inherited this." + name + ii.type().stringValue() + " (owner " + owner + ")", false);
                            }
                        } else if (virtual) {
                            // (iii) a virtual call on a rep-typed receiver to a method its class does not declare: an inherited String body
                            // auto-cleared: exactly the pinned inherited pairs (RepInheritedBodyTest.EXPECTED_INHERITED)
                            ClassModel target = models.get(owner);
                            if (target != null && !declares(target, name, ii.type().stringValue())) {
                                StringBuilder params = new StringBuilder();
                                for (ClassDesc pd : desc.parameterList()) {
                                    params.append(params.length() > 0 ? "," : "").append(pd.descriptorString());
                                }
                                boolean a4 = RepInheritedBodyTest.EXPECTED_INHERITED.contains(simple(owner) + "." + name + "(" + params + ")");
                                add(out, where + " -> inherited " + simple(owner) + "." + name + ii.type().stringValue(), a4);
                            }
                        }
                    } else if (e instanceof InvokeDynamicInstruction indy && flaggedParameter(indy.typeSymbol())) {
                        add(out, where + " -> indy " + indy.bootstrapMethod().owner().descriptorString() + "." + indy.name().stringValue() + indy.typeSymbol().descriptorString(), false);
                    } else if (e instanceof FieldInstruction fi && (fi.opcode() == Opcode.PUTFIELD || fi.opcode() == Opcode.PUTSTATIC)) {
                        // (ii) a reference store: auto-cleared only into the storing class's own private field
                        String type = fi.type().stringValue();
                        if (type.startsWith("L") || type.startsWith("[")) {
                            String owner = fi.owner().asInternalName();
                            boolean own = owner.equals(self) && privateField(cm, fi.name().stringValue(), type);
                            add(out, where + " -> " + fi.opcode().name().toLowerCase() + " " + owner + "." + fi.name().stringValue() + ":" + type, own);
                        }
                    } else if (e instanceof ArrayStoreInstruction as && as.opcode() == Opcode.AASTORE) {
                        // (ii) every reference array store
                        add(out, where + " -> aastore", false);
                    }
                    if (!(e instanceof java.lang.classfile.PseudoInstruction)) {
                        previous2 = previous;
                        previous = e;
                    }
                }
            }
        }
        return out;
    }

    @Test
    public void repCodeNeverPassesARepOut() throws IOException {
        Map<String, ClassModel> models = repClassModels();
        Map<String, Finding> all = findings(models);
        Set<String> unlisted = new TreeSet<>();
        Set<String> used = new TreeSet<>();
        Set<String> miscounted = new TreeSet<>();
        for (Finding f : all.values()) {
            if (ALLOWLIST.containsKey(f.key())) {
                used.add(f.key());
                int expected = COUNTS.getOrDefault(f.key(), 1);
                if (f.count() != expected) {
                    miscounted.add(f.key() + ": " + f.count() + " occurrences, pinned " + expected);
                }
            } else if (!f.autoCleared()) {
                unlisted.add(f.key());
            }
        }
        Assert.assertTrue("allowlisted findings occurring other than as pinned:\n  " + String.join("\n  ", miscounted), miscounted.isEmpty());
        Assert.assertTrue("rep code passes a rep-typed value out of the rep classes, stores a reference, makes a super call or runs an inherited String body at:\n  " +
                        String.join("\n  ", unlisted), unlisted.isEmpty());
        Set<String> stale = new TreeSet<>(ALLOWLIST.keySet());
        stale.removeAll(used);
        Assert.assertTrue("allowlist entries with no finding (remove them):\n  " + String.join("\n  ", stale), stale.isEmpty());
    }

    /** StringView does not call Character.offsetByCodePoints (a CharSequence-taking JDK method). */
    @Test
    public void stringViewOffsetByCodePointsStaysLocal() throws IOException {
        for (String key : findings(repClassModels()).keySet()) {
            Assert.assertFalse(key, key.contains("java/lang/Character.offsetByCodePoints"));
        }
    }

    /** Positive control: the scan reads every rep class and sees their auto-cleared exception constructors. */
    @Test
    public void theScanSeesTheRepClassesAndTheirExceptionMessages() throws IOException {
        Map<String, ClassModel> models = repClassModels();
        for (Class<?> c : RepPinSupport.repClasses()) {
            Assert.assertTrue(c.getName(), models.containsKey(c.getName().replace('.', '/')));
        }
        long auto = findings(models).values().stream().filter(Finding::autoCleared).count();
        Assert.assertTrue("auto-cleared exception constructors seen: " + auto, auto >= 5);
    }

    /**
     * Non-vacuity of the three further channels, on a synthetic rep class file (built with {@code java.lang.classfile}, never
     * loaded): each escape form is a finding, and an own private field store is auto-cleared.
     */
    @Test
    public void theNewChannelsAreSeen() {
        ClassDesc fake = ClassDesc.of(RepPinSupport.REP_PACKAGE + ".FakeRep");
        ClassDesc foreign = ClassDesc.of("x.Foreign");
        ClassDesc cdString = ClassDesc.of("java.lang.String");
        ClassDesc cdObject = ClassDesc.of("java.lang.Object");
        MethodTypeDesc v = MethodTypeDesc.of(ClassDesc.ofDescriptor("V"));
        byte[] bytes = ClassFile.of().build(fake, cb -> {
            cb.withSuperclass(cdString);
            cb.withField("own", cdObject, ClassFile.ACC_PRIVATE);
            cb.withField("open", cdObject, ClassFile.ACC_PUBLIC);
            cb.withMethod("serializable", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokestatic(foreign, "take", MethodTypeDesc.of(ClassDesc.ofDescriptor("V"), ClassDesc.of("java.io.Serializable"))).return_()));
            cb.withMethod("constable", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokestatic(foreign, "take", MethodTypeDesc.of(ClassDesc.ofDescriptor("V"), ClassDesc.of("java.lang.constant.Constable"))).return_()));
            cb.withMethod("constantDesc", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokestatic(foreign, "take", MethodTypeDesc.of(ClassDesc.ofDescriptor("V"), ClassDesc.of("java.lang.constant.ConstantDesc").arrayType()))
                                            .return_()));
            cb.withMethod("repTyped", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokestatic(foreign, "take", MethodTypeDesc.of(ClassDesc.ofDescriptor("V"), fake)).return_()));
            cb.withMethod("foreignStatic", v, ClassFile.ACC_PUBLIC, mb -> mb.withCode(c -> c.aload(0).putstatic(foreign, "F", cdObject).return_()));
            cb.withMethod("foreignField", v, ClassFile.ACC_PUBLIC, mb -> mb.withCode(c -> c.aconst_null().aload(0).putfield(foreign, "f", cdObject).return_()));
            cb.withMethod("openOwnField", v, ClassFile.ACC_PUBLIC, mb -> mb.withCode(c -> c.aload(0).aload(0).putfield(fake, "open", cdObject).return_()));
            cb.withMethod("privateOwnField", v, ClassFile.ACC_PUBLIC, mb -> mb.withCode(c -> c.aload(0).aload(0).putfield(fake, "own", cdObject).return_()));
            cb.withMethod("arrayStore", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.iconst_1().anewarray(cdObject).iconst_0().aload(0).aastore().return_()));
            cb.withMethod("inheritedBody", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokevirtual(fake, "isEmpty", MethodTypeDesc.of(ClassDesc.ofDescriptor("Z"))).pop().return_()));
            cb.withMethod("inheritedViaCast", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).checkcast(cdString).invokevirtual(cdString, "strip", MethodTypeDesc.of(cdString)).pop().return_()));
            cb.withMethod("isBlank", MethodTypeDesc.of(ClassDesc.ofDescriptor("Z")), ClassFile.ACC_PUBLIC, mb -> mb.withCode(c -> c.iconst_0().ireturn()));
            cb.withMethod("declaredViaThis", v, ClassFile.ACC_PUBLIC,
                            mb -> mb.withCode(c -> c.aload(0).invokevirtual(cdString, "isBlank", MethodTypeDesc.of(ClassDesc.ofDescriptor("Z"))).pop().return_()));
        });
        Map<String, Finding> f = findings(Map.of(fake.descriptorString().substring(1, fake.descriptorString().length() - 1), ClassFile.of().parse(bytes)));
        String self = "FakeRep.";
        for (String k : new String[]{
                        self + "serializable()V -> x/Foreign.take(Ljava/io/Serializable;)V",
                        self + "constable()V -> x/Foreign.take(Ljava/lang/constant/Constable;)V",
                        self + "constantDesc()V -> x/Foreign.take([Ljava/lang/constant/ConstantDesc;)V",
                        self + "repTyped()V -> x/Foreign.take(Lcom/oracle/svm/core/stringrep/FakeRep;)V",
                        self + "foreignStatic()V -> putstatic x/Foreign.F:Ljava/lang/Object;",
                        self + "foreignField()V -> putfield x/Foreign.f:Ljava/lang/Object;",
                        self + "openOwnField()V -> putfield com/oracle/svm/core/stringrep/FakeRep.open:Ljava/lang/Object;",
                        self + "arrayStore()V -> aastore",
                        self + "inheritedBody()V -> inherited FakeRep.isEmpty()Z",
                        self + "inheritedViaCast()V -> inherited this.strip()Ljava/lang/String; (owner java/lang/String)"}) {
            Assert.assertTrue("not seen: " + k + " in " + f.keySet(), f.containsKey(k));
            Assert.assertFalse("auto-cleared: " + k, f.get(k).autoCleared());
        }
        String own = self + "privateOwnField()V -> putfield com/oracle/svm/core/stringrep/FakeRep.own:Ljava/lang/Object;";
        Assert.assertTrue(own, f.containsKey(own) && f.get(own).autoCleared());
        for (String k : f.keySet()) {
            Assert.assertFalse("a call to a declared method is no finding: " + k, k.startsWith(self + "declaredViaThis"));
        }
    }
}
