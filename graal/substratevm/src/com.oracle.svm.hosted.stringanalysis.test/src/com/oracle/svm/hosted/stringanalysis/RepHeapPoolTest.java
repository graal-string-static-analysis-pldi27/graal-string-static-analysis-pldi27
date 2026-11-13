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
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.StringView;
import com.oracle.svm.hosted.stringanalysis.RepTypeChecks.Ref;

import jdk.vm.ci.meta.JavaConstant;

/**
 * The heap-pool rule ({@link RepTypeChecks#disallowed}): a rep object may be in the image heap only as an
 * instance of its class's own static pool ({@link RepTypeChecks#POOL_FIELDS}, exactly {@code SingleByteString.POOL}),
 * referenced by nothing but the pool array (the heap value of the pool field), whose own references are only the pool
 * field and compiled code (the folded load of that static final field). The rule is checked on synthetic reference
 * graphs (as recorded by {@code NativeImageHeap.getRepObjectRefs}), the pool list against the rep classes' static
 * fields, and the pool's readers against the rep class files: the pool is private, SBS has no nestmates, and only the
 * four factories read it (they run only at replaced sites), plus the {@code <clinit>} that fills it.
 */
public class RepHeapPoolTest {

    static final String SBS = SingleByteString.class.getName();
    static final String POOL = SBS + ".POOL";

    /** A synthetic heap: object key -> class, the recorded references of the rep objects and rep arrays, the pool value. */
    static final class Heap {
        final Map<String, Class<?>> classes = new HashMap<>();
        final Map<String, List<Ref>> refs = new HashMap<>();
        final Map<String, String> pools = new HashMap<>();

        Heap obj(String key, Class<?> c, Ref... r) {
            classes.put(key, c);
            if (r.length > 0) {
                refs.put(key, List.of(r));
            }
            return this;
        }

        /** {@code key} is the heap value of SingleByteString.POOL. */
        Heap pool(String key, Class<?> c, Ref... r) {
            pools.put(POOL, key);
            return obj(key, c, r);
        }

        String why(String key) {
            return RepTypeChecks.disallowed(key, refs, classes::get, pools);
        }
    }

    /** The build's own shape: pool instances, the pool array referenced by compiled code (every load of the field folded). */
    static Heap poolOnly() {
        return new Heap().pool("pool", String[].class, Ref.code("createFromSubstring"), Ref.code("DataSection"))
                        .obj("a", SingleByteString.class, Ref.object("pool"))
                        .obj("b", SingleByteString.class, Ref.object("pool"));
    }

    @Test
    public void thePoolAloneIsAllowed() {
        Heap h = poolOnly();
        Assert.assertNull(h.why("a"));
        Assert.assertNull(h.why("b"));
        // the pool array held by its static field (an unfolded load) is the same pool
        Heap f = new Heap().pool("pool", String[].class, Ref.staticField(POOL), Ref.code("m")).obj("a", SingleByteString.class, Ref.object("pool"), Ref.object("pool"));
        Assert.assertNull(f.why("a"));
    }

    @Test
    public void anInstanceReferencedFromAnywhereElseFails() {
        // also a field or element of another heap object
        Heap h = poolOnly().obj("holder", Object[].class).obj("c", SingleByteString.class, Ref.object("pool"), Ref.object("holder"));
        Assert.assertNotNull(h.why("c"));
        // also a static field (its own, or the pool field itself holding an instance)
        Assert.assertNotNull(poolOnly().obj("c", SingleByteString.class, Ref.object("pool"), Ref.staticField("App.HELD")).why("c"));
        Assert.assertNotNull(poolOnly().obj("c", SingleByteString.class, Ref.staticField(POOL)).why("c"));
        // also embedded in compiled code (a folded pool element or a graph constant): not through the pool
        Assert.assertNotNull(poolOnly().obj("c", SingleByteString.class, Ref.object("pool"), Ref.code("main")).why("c"));
        // also the interned-strings table or any other root
        Assert.assertNotNull(poolOnly().obj("c", SingleByteString.class, Ref.object("pool"), Ref.other("InternedStringsTable")).why("c"));
        // no recorded reference at all (never through addConstant)
        Assert.assertNotNull(poolOnly().obj("c", SingleByteString.class).why("c"));
    }

    @Test
    public void thePoolArrayReferencedFromAnywhereElseFails() {
        // the pool array also stored in another object (its instances then reach a load no factory controls)
        Assert.assertNotNull(new Heap().obj("holder", Object[].class).pool("pool", String[].class, Ref.code("m"), Ref.object("holder"))
                        .obj("a", SingleByteString.class, Ref.object("pool")).why("a"));
        // also in another static field
        Assert.assertNotNull(new Heap().pool("pool", String[].class, Ref.staticField(POOL), Ref.staticField("App.POOL_COPY"))
                        .obj("a", SingleByteString.class, Ref.object("pool")).why("a"));
        // also any other root
        Assert.assertNotNull(new Heap().pool("pool", String[].class, Ref.code("m"), Ref.other("Resource"))
                        .obj("a", SingleByteString.class, Ref.object("pool")).why("a"));
        // an array that is not the value of SingleByteString.POOL (e.g. an application array), even one only in code
        Assert.assertNotNull(poolOnly().obj("arr", SingleByteString[].class, Ref.code("main")).obj("c", SingleByteString.class, Ref.object("arr")).why("c"));
        Assert.assertNotNull(poolOnly().obj("arr", SingleByteString[].class, Ref.staticField(POOL)).obj("c", SingleByteString.class, Ref.object("arr")).why("c"));
        // no pool in the heap at all
        Assert.assertNotNull(new Heap().obj("arr", String[].class, Ref.code("m")).obj("a", SingleByteString.class, Ref.object("arr")).why("a"));
        // the pool array with no recorded reference
        Assert.assertNotNull(new Heap().pool("pool", String[].class).obj("a", SingleByteString.class, Ref.object("pool")).why("a"));
    }

    @Test
    public void everyOtherRepFails() {
        // a rep class without a pool, even when held by the pool array
        Heap h = poolOnly().obj("v", StringView.class, Ref.object("pool"));
        Assert.assertEquals("not a pooled rep class", h.why("v"));
        Assert.assertEquals("not a pooled rep class", new Heap().obj("v", StringView.class, Ref.staticField("App.HELD")).why("v"));
    }

    /**
     * The pool is a {@code String[]} like any other; a rep frozen into a non-pool {@code String[]} (an
     * application array, a JDK table, a copy of the pool) still fails: the rep's own references are recorded by its class
     * whatever the holder's type, and the holder is not the pool value. Also when the pool itself holds the same rep.
     */
    @Test
    public void aRepInANonPoolStringArrayFails() {
        Assert.assertNotNull(poolOnly().obj("arr", String[].class, Ref.code("main")).obj("c", SingleByteString.class, Ref.object("arr")).why("c"));
        Assert.assertNotNull(poolOnly().obj("arr", String[].class, Ref.staticField("App.NAMES")).obj("c", SingleByteString.class, Ref.object("pool"), Ref.object("arr")).why("c"));
        Assert.assertNotNull(poolOnly().obj("arr", Object[].class, Ref.staticField("App.TABLE")).obj("c", SingleByteString.class, Ref.object("arr")).why("c"));
        Assert.assertTrue(RepTypeChecks.recordsRefsOf(SingleByteString.class, null, List.of()));
    }

    /**
     * The heap-pool rule's recording: rep objects and rep arrays by class, plus the pool value by identity (any class); not
     * any other {@code String[]}. {@code isRepOrRepArrayClass} (shared with the clinit-simulation parity hook) is not
     * widened ({@link #theRecordedClasses}).
     */
    @Test
    public void theRecordingRule() {
        JavaConstant pool = JavaConstant.forInt(1);
        JavaConstant other = JavaConstant.forInt(2);
        Assert.assertTrue(RepTypeChecks.recordsRefsOf(String[].class, pool, List.of(pool)));
        Assert.assertFalse(RepTypeChecks.recordsRefsOf(String[].class, other, List.of(pool)));
        Assert.assertFalse(RepTypeChecks.recordsRefsOf(String[].class, other, List.of()));
        Assert.assertTrue(RepTypeChecks.recordsRefsOf(SingleByteString[].class, other, List.of(pool)));
        Assert.assertTrue(RepTypeChecks.recordsRefsOf(StringView.class, other, List.of(pool)));
        Assert.assertFalse(RepTypeChecks.recordsRefsOf(Object[].class, other, List.of(pool)));
    }

    /** The heap-pool rule checks the premise of the unchecked pool read: every pool element is a non-null SingleByteString. */
    @Test
    public void thePoolContentIsChecked() {
        Assert.assertNull(RepTypeChecks.poolContentViolation(POOL, List.of(SingleByteString.class, SingleByteString.class)));
        List<Class<?>> withNull = new java.util.ArrayList<>(List.of(SingleByteString.class));
        withNull.add(null);
        Assert.assertNotNull(RepTypeChecks.poolContentViolation(POOL, withNull));
        Assert.assertNotNull(RepTypeChecks.poolContentViolation(POOL, List.of(SingleByteString.class, String.class)));
        Assert.assertNotNull(RepTypeChecks.poolContentViolation(POOL, List.of(StringView.class)));
        Assert.assertNotNull(RepTypeChecks.poolContentViolation(POOL, null));
        // the real pool, on the hosting JVM (svm.core is build-time initialised: this is the image heap's content)
        List<Class<?>> real = new java.util.ArrayList<>();
        try {
            Field f = SingleByteString.class.getDeclaredField("POOL");
            f.setAccessible(true);
            for (Object o : (Object[]) f.get(null)) {
                real.add(o == null ? null : o.getClass());
            }
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
        Assert.assertEquals(256, real.size());
        Assert.assertNull(RepTypeChecks.poolContentViolation(POOL, real));
    }

    /** The recorded classes: every rep and every array (of any dimension) of one, nothing else. */
    @Test
    public void theRecordedClasses() {
        Assert.assertTrue(RepTypeChecks.isRepOrRepArrayClass(SingleByteString.class));
        Assert.assertTrue(RepTypeChecks.isRepOrRepArrayClass(SingleByteString[].class));
        Assert.assertTrue(RepTypeChecks.isRepOrRepArrayClass(StringView[][].class));
        Assert.assertFalse(RepTypeChecks.isRepOrRepArrayClass(String.class));
        Assert.assertFalse(RepTypeChecks.isRepOrRepArrayClass(String[].class));
        Assert.assertFalse(RepTypeChecks.isRepOrRepArrayClass(Object[].class));
        Assert.assertFalse(RepTypeChecks.isRepOrRepArrayClass(int[].class));
    }

    /** A type whose values can be a rep: String, a String supertype, a rep class, or an array of one. */
    static boolean canHoldRep(Class<?> t) {
        Class<?> e = t;
        while (e.isArray()) {
            e = e.getComponentType();
        }
        return !e.isPrimitive() && (e.isAssignableFrom(String.class) || String.class.isAssignableFrom(e));
    }

    /**
     * The pool list is exact: the static fields of the rep classes that can hold a rep are exactly {@code POOL_FIELDS},
     * each a private static final {@code String[]} (no rep array type).
     */
    @Test
    public void thePoolFieldsAreExactlyTheRepClassesStaticRepFields() {
        Set<String> found = new TreeSet<>();
        for (Class<?> c : RepPinSupport.repClasses()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers()) && canHoldRep(f.getType())) {
                    found.add(c.getName() + "." + f.getName());
                    int m = f.getModifiers();
                    Assert.assertTrue(f + " is private static final", Modifier.isPrivate(m) && Modifier.isFinal(m));
                    // typed String[], not an array of its own class (no rep array type in the image)
                    Assert.assertEquals(f + " is a String[]", String[].class, f.getType());
                }
            }
        }
        Set<String> pinned = new TreeSet<>();
        RepTypeChecks.POOL_FIELDS.forEach((c, f) -> pinned.add(c + "." + f));
        Assert.assertEquals("POOL_FIELDS = the rep classes' static rep-holding fields", pinned, found);
    }

    /**
     * The readers and writers of every pool field, from the rep class files: only the pool's own class touches it (it is
     * private, and SBS has no nestmates), and only the four factories read it; {@code <clinit>} fills it. The case mappings
     * do not read it.
     */
    @Test
    public void thePoolIsReadOnlyByTheFactories() throws IOException {
        Map<String, ClassModel> models = RepEscapeTest.repClassModels();
        Map<String, Set<String>> readers = new TreeMap<>();
        for (ClassModel cm : models.values()) {
            String caller = RepEscapeTest.simple(cm.thisClass().asInternalName());
            for (MethodModel mm : cm.methods()) {
                CodeModel code = mm.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (CodeElement e : code) {
                    if (e instanceof FieldInstruction fi) {
                        String owner = fi.owner().asInternalName().replace('/', '.');
                        String q = owner + "." + fi.name().stringValue();
                        if (RepTypeChecks.POOL_FIELDS.containsKey(owner) && RepTypeChecks.POOL_FIELDS.get(owner).equals(fi.name().stringValue())) {
                            readers.computeIfAbsent(q, k -> new TreeSet<>()).add(caller + "." + mm.methodName().stringValue() + mm.methodType().stringValue() +
                                            (fi.opcode() == Opcode.GETSTATIC ? " get" : " " + fi.opcode().name().toLowerCase()));
                        }
                    }
                }
            }
        }
        Map<String, Set<String>> expected = Map.of(POOL, new TreeSet<>(Set.of(
                        "SingleByteString.<clinit>()V get",
                        "SingleByteString.<clinit>()V putstatic",
                        "SingleByteString.create(B)Lcom/oracle/svm/core/stringrep/SingleByteString; get",
                        "SingleByteString.create(C)Lcom/oracle/svm/core/stringrep/SingleByteString; get",
                        "SingleByteString.createFromSubstring(Ljava/lang/String;I)Ljava/lang/String; get",
                        "SingleByteString.createFromChar(C)Ljava/lang/String; get")));
        Assert.assertEquals("the pool's readers and writers", new TreeMap<>(expected), readers);
        // the unchecked read SingleByteString.exactPoolEntry is called only by the four factories, each time
        // directly on an element of the pool (getstatic POOL ... aaload; invokestatic exactPoolEntry)
        Set<String> exactCallers = new TreeSet<>();
        for (ClassModel cm : models.values()) {
            String caller = RepEscapeTest.simple(cm.thisClass().asInternalName());
            for (MethodModel mm : cm.methods()) {
                CodeModel code = mm.code().orElse(null);
                if (code == null) {
                    continue;
                }
                CodeElement prev = null;
                String lastStatic = null;
                for (CodeElement e : code) {
                    if (e instanceof FieldInstruction fi && fi.opcode() == Opcode.GETSTATIC) {
                        lastStatic = fi.owner().asInternalName().replace('/', '.') + "." + fi.name().stringValue();
                    }
                    if (e instanceof java.lang.classfile.instruction.InvokeInstruction ii && ii.name().stringValue().equals("exactPoolEntry")) {
                        String at = caller + "." + mm.methodName().stringValue() + mm.methodType().stringValue();
                        exactCallers.add(at);
                        Assert.assertTrue(at + ": exactPoolEntry on an aaload", prev instanceof java.lang.classfile.Instruction pi && pi.opcode() == Opcode.AALOAD);
                        Assert.assertEquals(at + ": exactPoolEntry on an element of the pool", POOL, lastStatic);
                    }
                    if (e instanceof java.lang.classfile.Instruction) {
                        prev = e;
                    }
                }
            }
        }
        Assert.assertEquals("exactPoolEntry's callers", new TreeSet<>(Set.of(
                        "SingleByteString.create(B)Lcom/oracle/svm/core/stringrep/SingleByteString;",
                        "SingleByteString.create(C)Lcom/oracle/svm/core/stringrep/SingleByteString;",
                        "SingleByteString.createFromSubstring(Ljava/lang/String;I)Ljava/lang/String;",
                        "SingleByteString.createFromChar(C)Ljava/lang/String;")), exactCallers);
        for (String cls : RepTypeChecks.POOL_FIELDS.keySet()) {
            ClassModel cm = models.get(cls.replace('.', '/'));
            Assert.assertNotNull(cls, cm);
            Assert.assertTrue(cls + " has no nest members", cm.findAttribute(java.lang.classfile.Attributes.nestMembers()).isEmpty());
            Assert.assertTrue(cls + " is no nest member", cm.findAttribute(java.lang.classfile.Attributes.nestHost()).isEmpty());
        }
    }
}
