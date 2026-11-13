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

import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.hosted.stringanalysis.ContainerTables.RTrackRefusal;
import com.oracle.svm.hosted.stringanalysis.ForwardFixpoint.RecvAtom;
import com.oracle.svm.hosted.stringanalysis.ForwardFixpoint.RecvSink;
import com.oracle.svm.hosted.stringanalysis.ForwardFixpoint.RecvVerdict;

/**
 * The Accumulator View's pinned rules.
 * <ul>
 * <li>The receiver verdict ({@link ForwardFixpoint#receiverVerdict}) and the heuristic's owner rule.</li>
 * <li>The REJECT text is deterministic (the least foreign atom by its stable key).</li>
 * <li>A torn builder snapshot never yields an out-of-bounds view.</li>
 * <li>Every rule that does not enter the callee for a builder argument is audited read-only, derived mechanically
 * from the terminal-argument predicates and the JDK model data.</li>
 * </ul>
 */
public class AccumulatorRulesTest {

    // ------------------------------------------------------------------
    // The receiver verdict.
    // ------------------------------------------------------------------
    private static final Object BIRTH_A = new Object();
    private static final Object BIRTH_B = new Object();
    private static final Object BIRTH_JDK = new Object();
    private static final Map<Object, String> ADMITTED = Map.of(BIRTH_A, "accA", BIRTH_B, "accB");

    private static RecvSink sink(RecvAtom... atoms) {
        return new RecvSink(List.of(), List.of(atoms));
    }

    private static RecvAtom atom(Object birth, String key) {
        return new RecvAtom(birth, key);
    }

    @Test
    public void passingBirthsQualifyWithTheirOwners() {
        RecvVerdict<String> v = ForwardFixpoint.receiverVerdict(List.of(sink(atom(BIRTH_A, "a")), sink(atom(BIRTH_B, "b"), atom(BIRTH_A, "a"))), ADMITTED, false);
        Assert.assertNull(v.why());
        Assert.assertEquals(Set.of("accA", "accB"), v.owners());
        Assert.assertEquals(3, v.atoms());
    }

    @Test
    public void noSinkIsNotRun() {
        Assert.assertEquals("not run", ForwardFixpoint.receiverVerdict(List.of(), ADMITTED, false).why());
    }

    @Test
    public void aRefusedSinkRejects() {
        RecvVerdict<String> v = ForwardFixpoint.receiverVerdict(List.of(sink(atom(BIRTH_A, "a")),
                        new RecvSink(List.of(RTrackRefusal.MISSING_IR, RTrackRefusal.CALLER_FAN_CAP), List.of())), ADMITTED, false);
        Assert.assertNotNull(v.why());
        Assert.assertTrue(v.why(), v.why().startsWith("backward receiver refused [CALLER_FAN_CAP, MISSING_IR]"));
        Assert.assertTrue(v.owners().isEmpty());
        // a sink that could not be attached counts as UNRESOLVED_VALUE
        RecvVerdict<String> w = ForwardFixpoint.receiverVerdict(List.of(new RecvSink(null, List.of())), ADMITTED, false);
        Assert.assertEquals("backward receiver refused [UNRESOLVED_VALUE]", w.why());
    }

    @Test
    public void aGuardTripRejects() {
        RecvVerdict<String> v = ForwardFixpoint.receiverVerdict(List.of(sink(atom(BIRTH_A, "a"))), ADMITTED, true);
        Assert.assertEquals("backward receiver: EVALUATION_GUARD", v.why());
    }

    @Test
    public void aConstantOrForeignBirthRejects() {
        // an image-heap constant (no birth node)
        RecvVerdict<String> c = ForwardFixpoint.receiverVerdict(List.of(sink(atom(BIRTH_A, "a"), atom(null, "constant java.lang.StringBuilder"))), ADMITTED, false);
        Assert.assertEquals("backward receiver reaches an object that is not a pass-1 accumulator (constant java.lang.StringBuilder)", c.why());
        // an unmatched birth (a JDK allocation, a failed or refused seed)
        RecvVerdict<String> j = ForwardFixpoint.receiverVerdict(List.of(sink(atom(BIRTH_JDK, "birth java.util.Formatter.<init>()@4 java.lang.StringBuilder"))), ADMITTED, false);
        Assert.assertNotNull(j.why());
        Assert.assertTrue(j.owners().isEmpty());
    }

    /** The reported atom is the least by its stable key, whatever the sink or atom order (the drain order). */
    @Test
    public void theRejectTextIsOrderIndependent() {
        RecvAtom x = atom(BIRTH_JDK, "failed-seed C.run(boolean)@15");
        RecvAtom y = atom(null, "constant java.lang.StringBuilder");
        String one = ForwardFixpoint.receiverVerdict(List.of(sink(x), sink(y)), ADMITTED, false).why();
        String two = ForwardFixpoint.receiverVerdict(List.of(sink(y, x)), ADMITTED, false).why();
        Assert.assertEquals(one, two);
        Assert.assertEquals("backward receiver reaches an object that is not a pass-1 accumulator (constant java.lang.StringBuilder, +1 more)", one);
    }

    @Test
    public void anEmptyOwnerSetRejectsInTheHeuristic() {
        Assert.assertNull(ForwardFixpoint.receiverVerdict(List.of(sink()), ADMITTED, false).why()); // the child leaves it ...
        Assert.assertFalse(AccumulatorHeuristic.ownersAllGrowing(Set.of("accA"), Set.of())); // ... to the heuristic
        Assert.assertFalse(AccumulatorHeuristic.ownersAllGrowing(Set.of("accA"), Set.of("accA", "accB")));
        Assert.assertTrue(AccumulatorHeuristic.ownersAllGrowing(Set.of("accA", "accB"), Set.of("accA")));
    }

    // ------------------------------------------------------------------
    // A torn builder snapshot.
    // ------------------------------------------------------------------
    private static String content(StringView v) {
        char[] out = new char[v.length()];
        for (int i = 0; i < out.length; i++) {
            out[i] = v.charAt(i);
        }
        return new String(out);
    }

    /**
     * The JDK's {@code append(CharSequence,int,int)} writes {@code coder = UTF16} before the inflated {@code value}: a
     * racing reader may pair the old Latin-1 array (6 used of 8 bytes) with UTF16. Shared, {@code charAt(5)} would read
     * bytes 10-11 of an 8-byte array; the factory copies instead, so every read stays inside the view's own array.
     */
    @Test
    public void aTornSnapshotIsCopiedNotShared() {
        byte[] latin1 = {'a', 'b', 'c', 'd', 'e', 'f', 0, 0};
        // the copy branch is an exact String (the JDK's toString on the padded snapshot)
        String v = StringView.ofBuilderSnapshot(latin1, (byte) 1, 6, false);
        Assert.assertSame(String.class, v.getClass());
        Assert.assertEquals(6, v.length());
        String s = String.valueOf(v.toCharArray()); // no AIOOBE: the copied array holds 12 bytes (zero-padded, like the JDK's toString)
        Assert.assertEquals(6, s.length());
        // a count past a Latin-1 array (a count published before the grown value)
        String w = StringView.ofBuilderSnapshot(new byte[]{'a', 'b'}, (byte) 0, 4, false);
        Assert.assertSame(String.class, w.getClass());
        Assert.assertEquals("ab\0\0", w);
        // a consistent snapshot above the threshold still shares (the fast path)
        byte[] shared = {'a', 'b', 'c', 'd', 'e', 'f', 0, 0};
        StringView z = (StringView) StringView.ofBuilderSnapshot(shared, (byte) 0, 6, false);
        shared[0] = 'Z';
        Assert.assertEquals("Zbcdef", content(z));
    }

    // ------------------------------------------------------------------
    // The rules that do not enter the callee are read-only for a builder argument.
    // ------------------------------------------------------------------
    private static boolean canHoldABuilder(Class<?> t) {
        // a StringWriter accumulator is builder-like here (its own READ_ONLY toString, Object identity methods)
        return !t.isPrimitive() && (t.isAssignableFrom(StringBuilder.class) || t.isAssignableFrom(StringBuffer.class) ||
                        t.isAssignableFrom(java.io.StringWriter.class));
    }

    /**
     * The terminal-argument rules (a PARAMETER usage, the body not entered): the String {@code equals} / {@code compareTo}
     * argument and the JMH Blackhole sink. Every method the predicates accept is audited: a builder
     * argument there is only compared by identity / {@code instanceof String} ({@code String.equals(Object)}), cast to
     * String ({@code compareTo(Object)}: a CCE for a builder), not a builder slot ({@code compareTo(String)}), or stored
     * as a reference without any call on it (the Blackhole consumers). The concat operand: a builder is never a
     * String-declared operand, so its slot is the desugared {@code toString()} crossing (the builder's own READ_ONLY
     * {@code toString}, a recorded usage), never the NONE operand usage.
     */
    @Test
    public void terminalArgumentRulesAreReadOnlyForABuilder() {
        Set<String> audited = Set.of("java.lang.String#equals(Ljava/lang/Object;)Z", "java.lang.String#compareTo(Ljava/lang/Object;)I",
                        "java.lang.String#compareTo(Ljava/lang/String;)I");
        Set<String> accepted = new java.util.TreeSet<>();
        for (Method m : String.class.getDeclaredMethods()) {
            boolean st = java.lang.reflect.Modifier.isStatic(m.getModifiers());
            String desc = MethodType.methodType(m.getReturnType(), m.getParameterTypes()).toMethodDescriptorString();
            if (StringAtoms.isStringEquals(st, "java.lang.String", m.getName(), desc) || StringAtoms.isStringCompareTo(st, "java.lang.String", m.getName(), desc)) {
                accepted.add("java.lang.String#" + m.getName() + desc);
            }
        }
        Assert.assertEquals(new java.util.TreeSet<>(audited), accepted);
        // the Blackhole sink: exactly the three Object consumers (JMH's Blackhole public method names)
        String bh = "org.openjdk.jmh.infra.Blackhole";
        Set<String> bhAccepted = new java.util.TreeSet<>();
        for (String n : List.of("consume", "consumeFull", "consumeCompiler", "consumeCPU", "evaporate", "clearSinks", "readObject")) {
            for (boolean st : new boolean[]{false, true}) {
                for (String d : List.of("(Ljava/lang/Object;)V", "(Ljava/lang/String;)V", "(J)V", "(I)V", "()V")) {
                    if (StringAtoms.isJmhBlackholeSink(st, bh, n, d)) {
                        bhAccepted.add((st ? "static " : "") + n + d);
                    }
                }
            }
        }
        Assert.assertEquals(new java.util.TreeSet<>(Set.of("consume(Ljava/lang/Object;)V", "consumeFull(Ljava/lang/Object;)V", "static consumeCompiler(Ljava/lang/Object;)V")), bhAccepted);
        // the concat: a builder operand (not String-declared) is the desugared toString crossing; toString is READ_ONLY
        StringAtoms.Concat c = new StringAtoms.Concat(StringAtoms.ConcatKind.F1, new boolean[]{true, false}, null);
        Assert.assertEquals(StringAtoms.ConcatSlot.DESUGARED_TO_STRING, StringAtoms.concatSlot(c, 1, true));
        Assert.assertTrue(AccumulatorWhitelist.READ_ONLY_METHODS.contains("toString"));
    }

    /**
     * The JDK models (every family, enabled or not): each (op, slot) whose declared type can hold a builder, with what the
     * model does to it, derived from the model data. A model replaces the callee, so its effect kinds on a builder slot
     * must be ones whose builder use is recorded or harmless: passed into a callback ({@code PASSED}: the callback is
     * resolved and entered, or is the audited equals/compareTo terminal), {@code store}d as a value or {@code alias}ed
     * ({@code FLOWS}: the value stays tracked, its later uses are recorded), {@code ir} (entered), {@code observe} /
     * {@code classcheck} (identity, class), {@code unmodelled} (refused). A store into a builder-capable slot fails. A call on
     * the builder ({@code DISPATCHED}) must be one of the audited callbacks, each checked by reflection to resolve on
     * {@code StringBuilder}/{@code StringBuffer} to a READ_ONLY builder method, to an identity method of {@code Object}, or
     * to nothing (the builder is not of the callback's type).
     */
    @Test
    public void modelSlotsThatCanHoldABuilderAreReadOnly() throws Exception {
        Map<String, String> found = new TreeMap<>();
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (JdkModels.Op op : f.table.values()) {
                String id = op.method();
                int hash = id.indexOf('#');
                int paren = id.indexOf('(');
                String name = id.substring(hash + 1, paren);
                Class<?> holder = Class.forName(id.substring(0, hash), false, ClassLoader.getSystemClassLoader());
                MethodType mt = MethodType.fromMethodDescriptorString(id.substring(paren), ClassLoader.getSystemClassLoader());
                boolean isStatic = false;
                if (!name.equals("<init>")) {
                    Method m = findMethod(holder, name, mt.parameterArray());
                    Assert.assertNotNull("no such method " + id, m);
                    isStatic = java.lang.reflect.Modifier.isStatic(m.getModifiers());
                }
                List<Class<?>> slots = new ArrayList<>();
                if (!isStatic) {
                    slots.add(holder);
                }
                slots.addAll(mt.parameterList());
                for (int k = 0; k < slots.size(); k++) {
                    if (!canHoldABuilder(slots.get(k)) || (!isStatic && k == 0 && name.equals("<init>"))) {
                        continue;
                    }
                    found.put(f.id + " " + id + " slot " + k, effectsOn(op, k));
                }
            }
        }
        Assert.assertTrue("builder-capable model slots: " + found.size(), found.size() >= 200);
        Set<String> dispatched = new java.util.TreeSet<>();
        for (Map.Entry<String, String> e : found.entrySet()) {
            for (String kind : e.getValue().split(" ")) {
                if (kind.startsWith("DISPATCHED(")) {
                    dispatched.add(kind.substring("DISPATCHED(".length(), kind.length() - 1));
                    continue;
                }
                Assert.assertTrue("a model effect on a builder-capable slot that is not audited read-only: " + e.getKey() + " = " + e.getValue(),
                                kind.startsWith("PASSED(") || kind.startsWith("FLOWS(") || kind.equals("ENTERED(ir)") || kind.equals("OBSERVED") ||
                                                kind.equals("CLASSCHECK") || kind.equals("REFUSED") || kind.equals("UNREAD"));
            }
        }
        Set<String> audited = new java.util.TreeSet<>(AUDITED_CALLBACKS_ON_A_BUILDER);
        Assert.assertEquals("the audited callbacks ON a builder-capable model slot; audit the delta", audited, dispatched);
        for (String cb : dispatched) {
            if (cb.equals(VALUE_OF)) {
                continue; // static: the builder is valueOf's argument; valueOf's own model calls Object#toString (checked here)
            }
            int hash = cb.indexOf('#');
            int paren = cb.indexOf('(');
            Class<?> decl = Class.forName(cb.substring(0, hash));
            MethodType mt = MethodType.fromMethodDescriptorString(cb.substring(paren), ClassLoader.getSystemClassLoader());
            for (Class<?> b : new Class<?>[]{StringBuilder.class, StringBuffer.class, java.io.StringWriter.class}) {
                if (!decl.isAssignableFrom(b)) {
                    continue; // never a target on a builder
                }
                Method target = b.getMethod(cb.substring(hash + 1, paren), mt.parameterArray());
                if (target.isBridge()) {
                    Assert.assertEquals(cb, "compareTo", target.getName()); // the bridge casts and calls compareTo(<builder>)
                }
                String tdecl = target.getDeclaringClass().getName();
                if (tdecl.equals("java.lang.Object")) {
                    Assert.assertTrue(cb + " -> Object." + target.getName(), Set.of("equals", "hashCode").contains(target.getName()));
                } else {
                    Assert.assertTrue(cb + " -> " + target, AccumulatorWhitelist.BUILDER_DECLARING.contains(tdecl) && AccumulatorWhitelist.READ_ONLY_METHODS.contains(target.getName()) ||
                                    // on a StringWriter the callback is a terminal (StringWriter is a stringy declaring
                                    // type) recorded as a RECEIVER usage at the target site, which the writer table judges
                                    AccumulatorWhitelist.WRITER_DECLARING.contains(tdecl) && AccumulatorWhitelist.W_GROW_WRITER.contains(target.getName()));
                }
            }
        }
        // String.valueOf(Object)'s model: its only effect on the argument is the Object#toString callback
        Assert.assertEquals("DISPATCHED(java.lang.Object#toString()Ljava/lang/String;)", effectsOn(JdkModels.family("f6").table.get(VALUE_OF), 0));
    }

    private static final String VALUE_OF = "java.lang.String#valueOf(Ljava/lang/Object;)Ljava/lang/String;";

    /**
     * The audited callbacks the models make on a builder-capable slot: {@code equals}/{@code hashCode} (builders inherit
     * Object's identity methods), {@code toString}/{@code compareTo} (the builders' READ_ONLY methods, recorded usages),
     * {@code String.valueOf(Object)} (static: its model calls {@code toString}), and interface calls a builder never
     * receives ({@code List.iterator}, {@code Map.Entry.getKey/getValue}, {@code Set.size}).
     */
    private static final Set<String> AUDITED_CALLBACKS_ON_A_BUILDER = new java.util.TreeSet<>(Set.of(
                    "java.lang.Comparable#compareTo(Ljava/lang/Object;)I",
                    "java.lang.Object#equals(Ljava/lang/Object;)Z",
                    "java.lang.Object#hashCode()I",
                    "java.lang.Object#toString()Ljava/lang/String;",
                    VALUE_OF,
                    "java.util.List#iterator()Ljava/util/Iterator;",
                    "java.util.Map$Entry#getKey()Ljava/lang/Object;",
                    "java.util.Map$Entry#getValue()Ljava/lang/Object;",
                    "java.util.Set#size()I",
                    // the F6 Writer models (Writer.write(String) / append(CharSequence)) re-dispatch write on their
                    // Writer receiver; a StringWriter overrides both modelled methods (never their target) and the
                    // re-dispatched write resolves to StringWriter.write (a GROWING writer method, checked below)
                    "java.io.Writer#write(Ljava/lang/String;)V",
                    "java.io.Writer#write(Ljava/lang/String;II)V"));

    private static Method findMethod(Class<?> c, String name, Class<?>[] params) {
        for (Class<?> k = c; k != null; k = k.getSuperclass()) {
            try {
                return k.getDeclaredMethod(name, params);
            } catch (NoSuchMethodException e) {
                // continue
            }
        }
        for (Class<?> i : c.getInterfaces()) {
            Method m = findMethod(i, name, params);
            if (m != null) {
                return m;
            }
        }
        return null;
    }

    /** The kinds of effect the op has on argument slot {@code k} (sorted, distinct; UNREAD when none). */
    private static String effectsOn(JdkModels.Op op, int k) {
        java.util.TreeSet<String> kinds = new java.util.TreeSet<>();
        for (JdkModels.Effect e : op.effects()) {
            switch (e) {
                case JdkModels.Alias a -> {
                    if (a.a().slot() == k) {
                        kinds.add("FLOWS(alias)");
                    }
                }
                case JdkModels.Store s -> {
                    if (s.a().slot() == k) {
                        kinds.add("WRITE-INTO(" + s.member() + ")");
                    }
                    if (s.v().slot() == k) {
                        kinds.add("FLOWS(store)");
                    }
                }
                case JdkModels.Callback c -> {
                    if (c.a().slot() == k) {
                        kinds.add("DISPATCHED(" + c.cb() + ")");
                    }
                    for (JdkModels.Ref r : c.cbArgs()) {
                        if (r.slot() == k) {
                            kinds.add("PASSED(" + c.cb() + ")");
                        }
                    }
                }
                case JdkModels.Observe o -> {
                    if (o.a().slot() == k) {
                        kinds.add("OBSERVED");
                    }
                }
                case JdkModels.ClassCheck cc -> {
                    if (cc.a().slot() == k) {
                        kinds.add("CLASSCHECK");
                    }
                }
                case JdkModels.Ir ir -> {
                    if (ir.a().slot() == k) {
                        kinds.add("ENTERED(ir)");
                    }
                }
                case JdkModels.Unmodelled u -> {
                    if (u.a().slot() == k) {
                        kinds.add("REFUSED");
                    }
                }
                case JdkModels.Fresh fr -> {
                }
            }
        }
        return kinds.isEmpty() ? "UNREAD" : String.join(" ", kinds);
    }
}
