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

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.TypeKind;
import java.lang.classfile.instruction.ArrayLoadInstruction;
import java.lang.classfile.instruction.ArrayStoreInstruction;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.ConvertInstruction;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.IncrementInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.MonitorInstruction;
import java.lang.classfile.instruction.NewMultiArrayInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.NewPrimitiveArrayInstruction;
import java.lang.classfile.instruction.NewReferenceArrayInstruction;
import java.lang.classfile.instruction.NopInstruction;
import java.lang.classfile.instruction.OperatorInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.lang.classfile.instruction.StoreInstruction;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URI;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;

/**
 * Builder-append mirror ({@link AppendMirror}, {@link AppendMirrorNodePlugin}): the entry-point classification guard
 * (every builder member that takes a String/CharSequence/Object is in the table or in the reasoned exclusion list), the
 * mirror bytecode scan (a mirror reads the string only through its own calls of the overridden members and passes it to
 * no call but another mirror; runs on the JDK under test, which must carry the builder-append mirrors), and the pure
 * pins (row, mode, knob defaults, the profile line shape, the arm weight).
 */
public class AppendMirrorTest {

    private static final List<Class<?>> BUILDERS = builders();

    private static List<Class<?>> builders() {
        try {
            return List.of(Class.forName("java.lang.AbstractStringBuilder"), StringBuilder.class, StringBuffer.class);
        } catch (ClassNotFoundException e) {
            throw new AssertionError(e);
        }
    }

    /**
     * The reasoned exclusions, by name + parameter descriptor: members that take a string but are not
     * mirror entry points.
     */
    private static final Map<String, String> EXCLUDED = Map.of(
                    "indexOf(Ljava/lang/String;)", "row 14: the string is read by String statics; the walk enters a String body and refuses (stays REJECT)",
                    "indexOf(Ljava/lang/String;I)", "row 14 (as indexOf(String))",
                    "lastIndexOf(Ljava/lang/String;)", "row 14 (as indexOf(String))",
                    "lastIndexOf(Ljava/lang/String;I)", "row 14 (as indexOf(String))",
                    "repeat(Ljava/lang/CharSequence;I)",
                    "qualifies but unseen in every census: not a table entry, so its row is NONE and the body is entered under the ordinary rules; a mirror is added when a census shows it");

    private static String descriptor(Executable m) {
        StringBuilder sb = new StringBuilder("(");
        for (Class<?> p : m.getParameterTypes()) {
            sb.append(p.descriptorString());
        }
        sb.append(')');
        sb.append(m instanceof Method mm ? mm.getReturnType().descriptorString() : "V");
        return sb.toString();
    }

    private static boolean takesString(Executable m) {
        for (Class<?> p : m.getParameterTypes()) {
            if (p == String.class || p == CharSequence.class || p == Object.class) {
                return true;
            }
        }
        return false;
    }

    @Test
    public void everyStringTakingBuilderMemberIsClassifiedOnce() {
        List<String> unclassified = new ArrayList<>();
        Set<String> seenEntries = new TreeSet<>();
        for (Class<?> c : BUILDERS) {
            List<Executable> members = new ArrayList<>(Arrays.asList(c.getDeclaredMethods()));
            members.addAll(Arrays.asList(c.getDeclaredConstructors()));
            for (Executable m : members) {
                if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers()) || !takesString(m)) {
                    continue; // static/private helpers are reached only through the entry points
                }
                String name = m instanceof Constructor<?> ? "<init>" : m.getName();
                String desc = descriptor(m);
                if (AppendMirror.MIRRORS.containsKey(c.getName() + "#" + name + desc)) {
                    continue; // the invented mirror members themselves
                }
                boolean inTable = AppendMirror.lookup(c.getName(), name, desc) != null;
                boolean bridge = m instanceof Method mm && mm.isBridge();
                String params = name + desc.substring(0, desc.indexOf(')') + 1);
                boolean excluded = !bridge && EXCLUDED.containsKey(params);
                int n = (inTable ? 1 : 0) + (bridge ? 1 : 0) + (excluded ? 1 : 0);
                if (n != 1) {
                    unclassified.add(c.getName() + "#" + name + desc + " table=" + inTable + " bridge=" + bridge + " excluded=" + excluded);
                }
                if (inTable) {
                    seenEntries.add(c.getName() + "#" + name + desc);
                }
            }
        }
        Assert.assertEquals("a String/CharSequence/Object-taking builder member must be a table entry, a bridge (its internal call is a mirrorable JDK site) or a reasoned exclusion",
                        List.of(), unclassified);
        Assert.assertEquals("every table entry exists on the JDK under test", new TreeSet<>(AppendMirror.TABLE.keySet()), seenEntries);
    }

    @Test
    public void tableShape() {
        Assert.assertEquals(33, AppendMirror.TABLE.size());
        for (AppendMirror.Entry e : AppendMirror.TABLE.values()) {
            Assert.assertTrue(e.toString(), AppendMirror.OWNERS.contains(e.owner()));
            MethodTypeDesc entry = MethodTypeDesc.ofDescriptor(e.descriptor());
            MethodTypeDesc mirror = MethodTypeDesc.ofDescriptor(e.mirrorDescriptor());
            Assert.assertEquals("the mirror returns what the entry returns (the chain's phi)", entry.returnType(), mirror.returnType());
            Assert.assertEquals("the string slot holds a String in the mirror", ClassDesc.of("java.lang.String"), mirror.parameterType(e.slot() - 1));
            Assert.assertEquals(e.slot(), AppendMirror.MIRRORS.get(e.owner() + "#" + e.kind().mirrorName + e.mirrorDescriptor()).intValue());
            for (int i = 0; i < entry.parameterCount(); i++) {
                if (i != e.slot() - 1) {
                    Assert.assertEquals("the other parameters are passed unchanged", entry.parameterType(i), mirror.parameterType(i));
                }
            }
            Assert.assertEquals("INIT adds the Void disambiguator", entry.parameterCount() + (e.kind() == AppendMirror.Kind.INIT ? 1 : 0), mirror.parameterCount());
        }
    }

    // ------------------------------------------------------------------
    // The mirror bytecode scan
    // ------------------------------------------------------------------

    /** The reads a mirror may make (no whole-string getBytes([BIB)V: RopeString inherits String's, which reads value()). */
    private static final Set<String> STRING_READS = Set.of("length()I", "coder()B", "charAt(I)C", "getBytes([BIIBI)V");

    /**
     * Soundness premise of the mirrors: every value-null rep overrides each value-reading mirror read (length, charAt, the
     * ranged getBytes); coder() is String's field read, which every rep keeps set. A rep missing one would run String's
     * body on a null value (e.g. the whole-string getBytes on a rope fails that way).
     */
    @Test
    public void everyValueNullRepOverridesTheMirrorReads() throws Exception {
        List<Method> reads = List.of(String.class.getDeclaredMethod("length"), String.class.getDeclaredMethod("charAt", int.class),
                        String.class.getDeclaredMethod("getBytes", byte[].class, int.class, int.class, byte.class, int.class));
        List<String> missing = new ArrayList<>();
        int valueNull = 0;
        for (Map.Entry<String, Class<?>> r : InlineCacheRegistry.REP_CLASSES.entrySet()) {
            if (InlineCacheRegistry.isValueCarryingFlatRep(r.getValue())) {
                continue;
            }
            valueNull++;
            for (Method m : reads) {
                if (TerminalBodyKinds.implementingClass(r.getValue(), m) == String.class) {
                    missing.add(r.getKey() + " inherits String." + m.getName());
                }
            }
        }
        Assert.assertEquals(6, valueNull);
        Assert.assertEquals(List.of(), missing);
    }

    @Test
    public void mirrorsReadTheStringOnlyThroughTheirOwnCalls() throws Exception {
        FileSystem jrt = FileSystems.getFileSystem(URI.create("jrt:/"));
        List<String> violations = new ArrayList<>();
        int scanned = 0;
        for (Class<?> c : BUILDERS) {
            byte[] bytes = Files.readAllBytes(jrt.getPath("modules", "java.base", c.getName().replace('.', '/') + ".class"));
            ClassModel cm = ClassFile.of().parse(bytes);
            Set<String> found = new TreeSet<>();
            for (MethodModel mm : cm.methods()) {
                String key = c.getName() + "#" + mm.methodName().stringValue() + mm.methodType().stringValue();
                if (!AppendMirror.MIRRORS.containsKey(key)) {
                    continue;
                }
                found.add(key);
                scanned++;
                Assert.assertTrue(key + ": a mirror has code", mm.code().isPresent());
                Assert.assertEquals(key + ": no exception handlers", 0, mm.code().get().exceptionHandlers().size());
                for (String v : scan(mm, mm.code().get())) {
                    violations.add(key + ": " + v);
                }
            }
            Set<String> expected = new TreeSet<>();
            for (String k : AppendMirror.MIRRORS.keySet()) {
                if (k.startsWith(c.getName() + "#")) {
                    expected.add(k);
                }
            }
            Assert.assertEquals("the labs builder-append mirror members of " + c.getName() + " (a JDK without them cannot run the mirror lowering)", expected, found);
        }
        Assert.assertEquals(21, scanned);
        Assert.assertEquals("the string is read only through its own length/coder/charAt/getBytes calls and passed only to another mirror", List.of(), violations);
    }

    /** One abstract value slot: tainted = holds the string parameter. */
    private record State(boolean[] locals, List<Boolean> stack) {
        State copy() {
            return new State(locals.clone(), new ArrayList<>(stack));
        }

        boolean join(State o) {
            boolean changed = false;
            if (o.stack.size() != stack.size()) {
                throw new AssertionError("stack depth mismatch at a join");
            }
            for (int i = 0; i < locals.length; i++) {
                if (o.locals[i] && !locals[i]) {
                    locals[i] = true;
                    changed = true;
                }
            }
            for (int i = 0; i < stack.size(); i++) {
                if (o.stack.get(i) && !stack.get(i)) {
                    stack.set(i, true);
                    changed = true;
                }
            }
            return changed;
        }

        boolean pop() {
            return stack.remove(stack.size() - 1);
        }

        void push(boolean t, int slots) {
            if (slots >= 1) {
                stack.add(t);
            }
            if (slots == 2) {
                stack.add(false);
            }
        }
    }

    private static int slots(TypeKind k) {
        return k == TypeKind.VOID ? 0 : k.slotSize();
    }

    private static boolean isMirrorCall(InvokeInstruction inv) {
        return AppendMirror.MIRRORS.containsKey(inv.owner().asInternalName().replace('/', '.') + "#" + inv.name().stringValue() + inv.type().stringValue());
    }

    /** A worklist abstract interpretation of the taint of the String parameter(s) over the mirror's bytecode. */
    static List<String> scan(MethodModel mm, CodeModel code) {
        List<CodeElement> els = code.elementList();
        Map<Label, Integer> labelAt = new HashMap<>();
        for (int i = 0; i < els.size(); i++) {
            if (els.get(i) instanceof LabelTarget lt) {
                labelAt.put(lt.label(), i);
            }
        }
        MethodTypeDesc mt = mm.methodTypeSymbol();
        boolean[] locals = new boolean[((java.lang.classfile.attribute.CodeAttribute) code).maxLocals()];
        int slot = (mm.flags().has(java.lang.reflect.AccessFlag.STATIC)) ? 0 : 1;
        for (ClassDesc p : mt.parameterList()) {
            if (p.descriptorString().equals("Ljava/lang/String;")) {
                locals[slot] = true;
            }
            slot += TypeKind.from(p).slotSize();
        }
        State[] in = new State[els.size() + 1];
        in[0] = new State(locals, new ArrayList<>());
        ArrayDeque<Integer> work = new ArrayDeque<>();
        work.add(0);
        Set<String> out = new TreeSet<>();
        while (!work.isEmpty()) {
            int i = work.poll();
            State s = in[i].copy();
            CodeElement el = els.get(i);
            List<Integer> succ = new ArrayList<>();
            boolean falls = true;
            if (el instanceof Instruction ins) {
                falls = step(ins, s, out, labelAt, succ);
            }
            if (falls && i + 1 < els.size()) {
                succ.add(i + 1);
            }
            for (int t : succ) {
                if (in[t] == null) {
                    in[t] = s.copy();
                    work.add(t);
                } else if (in[t].join(s)) {
                    work.add(t);
                }
            }
        }
        return new ArrayList<>(out);
    }

    /** The effect of one instruction; returns whether control falls through. */
    private static boolean step(Instruction ins, State s, Set<String> out, Map<Label, Integer> labelAt, List<Integer> succ) {
        if (ins instanceof IncrementInstruction || ins instanceof NopInstruction) {
            return true;
        }
        if (ins instanceof NewObjectInstruction) {
            s.push(false, 1);
            return true;
        }
        if (ins instanceof NewPrimitiveArrayInstruction || ins instanceof NewReferenceArrayInstruction) {
            s.pop();
            s.push(false, 1);
            return true;
        }
        if (ins instanceof ThrowInstruction) {
            s.pop();
            return false;
        }
        if (ins instanceof MonitorInstruction) {
            check(s.pop(), "a monitor on the string", out);
            return true;
        }
        switch (ins) {
            case LoadInstruction l -> s.push(l.typeKind() == TypeKind.REFERENCE && s.locals()[l.slot()], slots(l.typeKind()));
            case StoreInstruction st -> {
                boolean t = s.pop();
                if (slots(st.typeKind()) == 2) {
                    s.pop();
                    s.locals()[st.slot()] = false;
                    s.locals()[st.slot() + 1] = false;
                } else {
                    s.locals()[st.slot()] = st.typeKind() == TypeKind.REFERENCE && t;
                }
            }
            case ConstantInstruction c -> s.push(false, slots(c.typeKind()));
            case OperatorInstruction o -> {
                int k = slots(o.typeKind());
                String n = o.opcode().name();
                if (n.equals("ARRAYLENGTH")) {
                    check(s.pop(), "arraylength of the string", out);
                    s.push(false, 1);
                } else if (n.endsWith("NEG")) {
                    popN(s, k);
                    s.push(false, k);
                } else if (n.equals("LCMP") || n.startsWith("FCMP") || n.startsWith("DCMP")) {
                    popN(s, 2 * k);
                    s.push(false, 1);
                } else if (n.equals("LSHL") || n.equals("LSHR") || n.equals("LUSHR")) {
                    popN(s, 3);
                    s.push(false, 2);
                } else {
                    popN(s, 2 * k);
                    s.push(false, k);
                }
            }
            case ConvertInstruction cv -> {
                popN(s, slots(cv.fromType()));
                s.push(false, slots(cv.toType()));
            }
            case FieldInstruction f -> {
                int k = slots(TypeKind.from(f.typeSymbol()));
                switch (f.opcode()) {
                    case GETFIELD -> {
                        check(s.pop(), "a field read on the string: " + f.name().stringValue(), out);
                        s.push(false, k);
                    }
                    case GETSTATIC -> s.push(false, k);
                    case PUTFIELD -> {
                        boolean v = popN(s, k);
                        check(v, "the string stored into a field " + f.name().stringValue(), out);
                        check(s.pop(), "a field write on the string", out);
                    }
                    default -> check(popN(s, k), "the string stored into a static field " + f.name().stringValue(), out);
                }
            }
            case InvokeInstruction inv -> {
                MethodTypeDesc t = inv.typeSymbol();
                List<ClassDesc> ps = t.parameterList();
                boolean mirror = isMirrorCall(inv);
                for (int p = ps.size() - 1; p >= 0; p--) {
                    boolean v = popN(s, TypeKind.from(ps.get(p)).slotSize());
                    check(v && !mirror, "the string passed to " + inv.owner().asInternalName() + "." + inv.name().stringValue() + inv.type().stringValue(), out);
                }
                if (inv.opcode() != Opcode.INVOKESTATIC) {
                    boolean r = s.pop();
                    boolean read = inv.opcode() == Opcode.INVOKEVIRTUAL && inv.owner().asInternalName().equals("java/lang/String") &&
                                    STRING_READS.contains(inv.name().stringValue() + inv.type().stringValue());
                    check(r && !read, "a call on the string that is not an overridden read: " + inv.owner().asInternalName() + "." + inv.name().stringValue() + inv.type().stringValue(), out);
                }
                s.push(false, slots(TypeKind.from(t.returnType())));
            }
            case InvokeDynamicInstruction indy -> {
                for (ClassDesc p : indy.typeSymbol().parameterList().reversed()) {
                    check(popN(s, TypeKind.from(p).slotSize()), "the string passed to an invokedynamic", out);
                }
                s.push(false, slots(TypeKind.from(indy.typeSymbol().returnType())));
            }
            case BranchInstruction br -> {
                String n = br.opcode().name();
                if (n.startsWith("IF_")) {
                    popN(s, 1);
                    popN(s, 1);
                } else if (n.startsWith("IF")) {
                    popN(s, 1);
                }
                succ.add(labelAt.get(br.target()));
                return !(br.opcode() == Opcode.GOTO || br.opcode() == Opcode.GOTO_W);
            }
            case ReturnInstruction r -> {
                if (r.typeKind() != TypeKind.VOID) {
                    check(popN(s, slots(r.typeKind())), "the string returned", out);
                }
                return false;
            }
            case ArrayLoadInstruction al -> {
                popN(s, 2);
                s.push(false, slots(al.typeKind()));
            }
            case ArrayStoreInstruction as -> {
                check(popN(s, slots(as.typeKind())), "the string stored into an array", out);
                popN(s, 2);
            }
            case StackInstruction si -> stackOp(si.opcode(), s);
            case TypeCheckInstruction tc -> {
                boolean v = s.pop();
                s.push(tc.opcode() == Opcode.CHECKCAST && v, 1);
            }
            case NewMultiArrayInstruction na -> {
                popN(s, na.dimensions());
                s.push(false, 1);
            }
            case TableSwitchInstruction ts -> {
                s.pop();
                succ.add(labelAt.get(ts.defaultTarget()));
                ts.cases().forEach(c -> succ.add(labelAt.get(c.target())));
                return false;
            }
            case LookupSwitchInstruction ls -> {
                s.pop();
                succ.add(labelAt.get(ls.defaultTarget()));
                ls.cases().forEach(c -> succ.add(labelAt.get(c.target())));
                return false;
            }
            default -> out.add("unhandled instruction " + ins.opcode());
        }
        return true;
    }

    private static void check(boolean violation, String what, Set<String> out) {
        if (violation) {
            out.add(what);
        }
    }

    /** Pops {@code n} slots; true if any was tainted. */
    private static boolean popN(State s, int n) {
        boolean t = false;
        for (int i = 0; i < n; i++) {
            t |= s.pop();
        }
        return t;
    }

    /** The slot-level stack operations (dup2 and friends copy raw slots, whatever their category). */
    private static void stackOp(Opcode op, State s) {
        List<Boolean> st = s.stack();
        int n = st.size();
        switch (op) {
            case POP -> s.pop();
            case POP2 -> popN(s, 2);
            case DUP -> st.add(st.get(n - 1));
            case DUP_X1 -> st.add(n - 2, st.get(n - 1));
            case DUP_X2 -> st.add(n - 3, st.get(n - 1));
            case DUP2 -> {
                st.add(st.get(n - 2));
                st.add(st.get(n - 1));
            }
            case DUP2_X1 -> {
                Boolean v1 = st.get(n - 1);
                Boolean v2 = st.get(n - 2);
                st.add(n - 3, v1);
                st.add(n - 3, v2);
            }
            case DUP2_X2 -> {
                Boolean v1 = st.get(n - 1);
                Boolean v2 = st.get(n - 2);
                st.add(n - 4, v1);
                st.add(n - 4, v2);
            }
            case SWAP -> {
                Boolean a = st.get(n - 1);
                st.set(n - 1, st.get(n - 2));
                st.set(n - 2, a);
            }
            default -> throw new AssertionError("stack op " + op);
        }
    }

    // ------------------------------------------------------------------
    // Pure pins
    // ------------------------------------------------------------------

    @Test
    public void knobDefaultsAndStrictOnly() {
        Assert.assertEquals("on by default", 1, AppendMirror.KNOB);
        Assert.assertFalse(AppendMirror.on(0));
        Assert.assertTrue(AppendMirror.on(1));
        Assert.assertTrue("the design's spelling mirror.append=2", AppendMirror.on(2));
        Assert.assertEquals("neutral arm weight", 0.5, AppendMirrorNodePlugin.armProfile().getDesignatedSuccessorProbability(), 0.0);
    }

    /** Runtime compilation is not covered, so MIRROR lines with it enabled fail the build (fail-closed). */
    @Test
    public void runtimeCompilationWithMirrorLinesFailsTheBuild() {
        Assert.assertNull(AppendMirrorNodePlugin.runtimeCompilationRefusal(false, 5));
        Assert.assertNull("no MIRROR line, nothing to refuse", AppendMirrorNodePlugin.runtimeCompilationRefusal(true, 0));
        String m = AppendMirrorNodePlugin.runtimeCompilationRefusal(true, 2);
        Assert.assertNotNull(m);
        Assert.assertTrue(m, m.contains("runtime compilation") && m.contains("MIRROR"));
    }

    /**
     * The mirror rep-list walk has no depth limit (the IC's is 6), so a rep 10
     * intermediate calls up is still listed; a receiver cycle terminates on the visited set.
     */
    @Test
    public void mirrorRepWalkHasNoDepthLimit() {
        StringUtilizationGraph graph = new StringUtilizationGraph();
        SugVertex rep = graph.newVertex();
        rep.setNodeType(SugNodeType.STRING_METHOD_CALL);
        List<SugVertex> chain = new ArrayList<>();
        List<SourceTag> tags = new ArrayList<>();
        SugVertex up = rep;
        for (int i = 0; i < 10; i++) {
            SugVertex v = graph.newVertex();
            v.setNodeType(SugNodeType.STRING_METHOD_CALL);
            tags.add(new SourceTag(up, UsageRole.RECEIVER, -1));
            v.getSourceTags().set(tags.size() - 1);
            chain.add(v);
            up = v;
        }
        tags.add(new SourceTag(chain.get(9), UsageRole.RECEIVER, -1)); // a cycle: chain[0] <- chain[9]
        chain.get(0).getSourceTags().set(tags.size() - 1);
        graph.setSourceTags(tags);
        Map<SugVertex, InstrumentationDecision> decisions = Map.of(rep, new InstrumentationDecision(rep, OptimizationType.STRING_VIEW, null));
        int[] visited = new int[1];
        Assert.assertEquals(Set.of("SV"), AppendMirror.repKindsFrom(graph, chain.get(9), decisions, visited));
        Assert.assertEquals("every vertex once (the cycle ends on the visited set)", 11, visited[0]);
    }

    @Test
    public void mirrorArgRow() {
        Assert.assertEquals(StringAtoms.MirrorArgRow.NONE, StringAtoms.mirrorArgRow(false, true, 1, 1, true));
        Assert.assertEquals("off: no refusal either", StringAtoms.MirrorArgRow.NONE, StringAtoms.mirrorArgRow(false, true, 2, 2, false));
        Assert.assertEquals(StringAtoms.MirrorArgRow.NONE, StringAtoms.mirrorArgRow(true, false, 1, 1, true));
        Assert.assertEquals("not an entry point", StringAtoms.MirrorArgRow.NONE, StringAtoms.mirrorArgRow(true, true, 1, -1, false));
        Assert.assertEquals("not the string slot", StringAtoms.MirrorArgRow.NONE, StringAtoms.mirrorArgRow(true, true, 0, 1, false));
        Assert.assertEquals(StringAtoms.MirrorArgRow.TERMINAL, StringAtoms.mirrorArgRow(true, true, 3, 3, true));
        Assert.assertEquals("strict, the only mode", StringAtoms.MirrorArgRow.NO_SITE, StringAtoms.mirrorArgRow(true, true, 2, 2, false));
    }

    @Test
    public void mirrorableSiteRule() {
        Assert.assertTrue(AppendMirror.mirrorableSite(true, false, true, false, false));
        Assert.assertFalse("no Phase-A vertex", AppendMirror.mirrorableSite(false, false, true, false, false));
        Assert.assertFalse("an inlined-scope invoke (keyed on the root in the child)", AppendMirror.mirrorableSite(true, true, true, false, false));
        Assert.assertFalse("the declared target is not an entry (Appendable/CharSequence/Object-declared)", AppendMirror.mirrorableSite(true, false, false, false, false));
        Assert.assertFalse("an interface invoke", AppendMirror.mirrorableSite(true, false, true, true, false));
        Assert.assertFalse("a hidden-class key", AppendMirror.mirrorableSite(true, false, true, false, true));
    }

    @Test
    public void noSiteRefusalAppendedLast() {
        RTrackRefusal[] all = RTrackRefusal.values();
        Assert.assertEquals(RTrackRefusal.MIRROR_ARG_NO_SITE, all[all.length - 1]);
        Assert.assertFalse(RTrackRefusal.MIRROR_ARG_NO_SITE.budgetClass);
        Assert.assertEquals(TransferFacts.IncompleteReason.UNTRACKABLE_CONTAINER, RTrackRefusal.MIRROR_ARG_NO_SITE.verdictReason());
    }

    @Test
    public void profileLineShape() {
        Assert.assertTrue(RepresentationProfileLoader.isMirrorLine("a.B#m(I)V@3 MIRROR APPEND SV".split(" ")));
        Assert.assertTrue(RepresentationProfileLoader.isMirrorLine("a.B#m(I)V@3 MIRROR INIT ROPE,SV".split(" ")));
        Assert.assertFalse("no key", RepresentationProfileLoader.isMirrorLine("a.B#m MIRROR APPEND SV".split(" ")));
        Assert.assertFalse("unknown kind", RepresentationProfileLoader.isMirrorLine("a.B#m(I)V@3 MIRROR PREPEND SV".split(" ")));
        Assert.assertFalse("no reps", RepresentationProfileLoader.isMirrorLine("a.B#m(I)V@3 MIRROR APPEND".split(" ")));
        Assert.assertFalse("an empty rep", RepresentationProfileLoader.isMirrorLine("a.B#m(I)V@3 MIRROR APPEND SV,,ROPE".split(" ")));
        java.util.Map<String, String> mirror = Map.of("a.B#m(I)V@3", "APPEND SV");
        RepresentationProfile p = new RepresentationProfile(Map.of(), true, Map.of(), Map.of(), Set.of(), mirror);
        Assert.assertFalse("a MIRROR line is an admit (the parent must not compile String as stock)", p.admitsNoRep());
        Assert.assertEquals("APPEND SV", p.getMirror("a.B#m(I)V@3"));
        Assert.assertTrue(new RepresentationProfile(Map.of(), true, Map.of(), Map.of(), Set.of(), Map.of()).admitsNoRep());
    }

    @Test
    public void entryLookupIsDescriptorExact() {
        Assert.assertEquals(AppendMirror.Kind.APPEND, AppendMirror.lookup("java.lang.StringBuilder", "append", "(Ljava/lang/Object;)Ljava/lang/StringBuilder;").kind());
        Assert.assertNull("a covariant bridge's descriptor is not an entry", AppendMirror.lookup("java.lang.StringBuilder", "append", "(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder;"));
        Assert.assertNull("append(StringBuffer) takes no string", AppendMirror.lookup("java.lang.StringBuilder", "append", "(Ljava/lang/StringBuffer;)Ljava/lang/StringBuilder;"));
        Assert.assertEquals(3, AppendMirror.lookup("java.lang.StringBuffer", "replace", "(IILjava/lang/String;)Ljava/lang/StringBuffer;").slot());
        Assert.assertEquals(AppendMirror.Kind.INSERT_SEQ, AppendMirror.lookup("java.lang.AbstractStringBuilder", "insert", "(ILjava/lang/CharSequence;)Ljava/lang/AbstractStringBuilder;").kind());
        Assert.assertEquals("(Ljava/lang/String;Ljava/lang/Void;)V", AppendMirror.lookup("java.lang.StringBuffer", "<init>", "(Ljava/lang/CharSequence;)V").mirrorDescriptor());
    }
}
