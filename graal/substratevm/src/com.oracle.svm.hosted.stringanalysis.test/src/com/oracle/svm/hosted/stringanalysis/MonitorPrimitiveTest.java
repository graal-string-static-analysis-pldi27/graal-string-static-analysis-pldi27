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

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.bytecode.BytecodeLookupSwitch;
import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.BytecodeSwitch;
import jdk.graal.compiler.bytecode.BytecodeTableSwitch;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.ConstantPool;
import jdk.vm.ci.meta.ExceptionHandler;
import jdk.vm.ci.meta.JavaField;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.meta.Signature;

/**
 * Pins for the monitor model ({@link MonitorPrimitive}): at a call into one of SVM's monitor operations the object
 * argument is an observation and the callee is not entered at that slot.
 * <ul>
 * <li>The premise, over SVM's own bytecode: from each operation's object parameter, every use (followed through the
 * monitor implementation, its lock and condition objects and its JFR events) is an observation of the reference or of
 * its class, a raw access to the hidden monitor slot, or an identity key of the private weak monitor map; the object is
 * never stored, read as a Java object, thrown, handed to other code, or returned
 * ({@link #operationsOnlyObserveTheObject}).</li>
 * <li>The completeness of {@link MonitorPrimitive#OPERATIONS}: every operation of {@code MonitorSupport} on an
 * object is listed, and every monitor operation that any SVM class outside the monitor package calls is listed.</li>
 * <li>The checker itself catches a store, a return, a field read and an escape into unknown code (mutation controls on
 * small methods of this class).</li>
 * </ul>
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.graal.compiler/jdk.graal.compiler.bytecode", "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.nodes"})
public class MonitorPrimitiveTest {

    private static final String MONITOR_PACKAGE = "com.oracle.svm.core.monitor.";
    private static final String MONITOR_SUPPORT = "com.oracle.svm.core.monitor.MonitorSupport";
    private static final String MT_MONITOR_SUPPORT = "com.oracle.svm.core.monitor.MultiThreadedMonitorSupport";
    /** The JFR events the monitor code emits with the object (they record its class and address). */
    private static final Set<String> MONITOR_EVENTS = Set.of("com.oracle.svm.core.jfr.events.JavaMonitorEnterEvent", "com.oracle.svm.core.jfr.events.JavaMonitorWaitEvent",
                    "com.oracle.svm.core.jfr.events.JavaMonitorInflateEvent");
    /**
     * The terminal uses of the object: callee (holder.name+descriptor) -> the argument positions (0 = the receiver of an
     * instance method) at which the object may be passed. Each is an observation of the reference or of its class, or
     * the hidden monitor slot / the private weak monitor map.
     */
    private static final Map<String, Set<Integer>> OBSERVING_CALLEES = Map.of(
                    // the class (the hub's monitor offset; the JFR events record the class)
                    "java.lang.Object.getClass()Ljava/lang/Class;", Set.of(0),
                    // the raw read of the hidden monitor slot (the offset comes from the hub, never a Java field)
                    "jdk.graal.compiler.word.BarrieredAccess.readObject(Ljava/lang/Object;I)Ljava/lang/Object;", Set.of(0),
                    // the raw CAS installing a JavaMonitor into the hidden slot: the object only as the BASE
                    "jdk.internal.misc.Unsafe.compareAndSetReference(Ljava/lang/Object;JLjava/lang/Object;Ljava/lang/Object;)Z", Set.of(1),
                    "jdk.internal.misc.Unsafe.compareAndExchangeReference(Ljava/lang/Object;JLjava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;", Set.of(1),
                    // the address the JFR events record
                    "jdk.graal.compiler.word.Word.objectToUntrackedPointer(Ljava/lang/Object;)Ljdk/graal/compiler/word/Word;", Set.of(0),
                    // replaceObject: a Class (DynamicHub) is replaced by its companion, a VM object; a Class is never an
                    // allocation-site object of the analysis
                    "com.oracle.svm.core.hub.DynamicHub.getCompanion()Lcom/oracle/svm/core/hub/DynamicHubCompanion;", Set.of(0));
    /**
     * The identity key of the secondary monitor storage (a private {@code WeakIdentityHashMap}, only queried by
     * identity: pinned by {@link #weakMonitorMapIsOnlyQueriedByIdentity}); allowed in {@code MultiThreadedMonitorSupport}
     * only.
     */
    private static final Map<String, Set<Integer>> MONITOR_MAP_KEYS = Map.of(
                    "java.util.Map.get(Ljava/lang/Object;)Ljava/lang/Object;", Set.of(1),
                    "java.util.Map.put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;", Set.of(1));
    /**
     * The map mode of the checker: the only allowed use of the weak monitor map object itself is as the
     * receiver of a query by identity (the key is the object mode's {@link #MONITOR_MAP_KEYS}).
     */
    private static final Map<String, Set<Integer>> MAP_RECEIVER_USES = Map.of(
                    "java.util.Map.get(Ljava/lang/Object;)Ljava/lang/Object;", Set.of(0),
                    "java.util.Map.put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;", Set.of(0));
    /** Methods of MonitorSupport that are not operations on an object (so not modelled). */
    private static final Set<String> NOT_OBJECT_OPERATIONS = Set.of("singleton()Lcom/oracle/svm/core/monitor/MonitorSupport;", "getParkedThreadStatus(Ljava/lang/Thread;Z)I");

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private static Class<?> load(String name) {
        try {
            return Class.forName(name, false, MonitorPrimitiveTest.class.getClassLoader());
        } catch (ClassNotFoundException e) {
            throw new AssertionError("class not found: " + name, e);
        }
    }

    /** The type, linked (a class loaded without initialization is not linked, and then has no bytecode for JVMCI). */
    private ResolvedJavaType type(String name) {
        ResolvedJavaType t = metaAccess.lookupJavaType(load(name));
        t.link();
        return t;
    }

    private static String nameDesc(JavaMethod m) {
        return m.getName() + m.getSignature().toMethodDescriptor();
    }

    private static String id(JavaMethod m) {
        return m.getDeclaringClass().toJavaName() + "." + nameDesc(m);
    }

    private static ResolvedJavaMethod declared(ResolvedJavaType t, String nameDesc) {
        for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
            if (nameDesc(m).equals(nameDesc)) {
                return m;
            }
        }
        for (ResolvedJavaMethod m : t.getDeclaredConstructors(false)) {
            if (nameDesc(m).equals(nameDesc)) {
                return m;
            }
        }
        return null;
    }

    /** The implementation that runs for {@code nameDesc} on the installed MonitorSupport (MonitorFeature). */
    private ResolvedJavaMethod implementation(String nameDesc) {
        ResolvedJavaType mt = type(MT_MONITOR_SUPPORT);
        ResolvedJavaMethod decl = declared(type(MONITOR_SUPPORT), nameDesc);
        Assert.assertNotNull("MonitorSupport declares " + nameDesc, decl);
        ResolvedJavaMethod impl = mt.resolveConcreteMethod(decl, mt);
        Assert.assertNotNull("MultiThreadedMonitorSupport implements " + nameDesc, impl);
        return impl;
    }

    // ------------------------------------------------------------------
    // Completeness
    // ------------------------------------------------------------------

    @Test
    public void everyObjectOperationOfMonitorSupportIsListed() {
        Set<String> declaredOps = new TreeSet<>();
        for (Method m : load(MONITOR_SUPPORT).getDeclaredMethods()) {
            if (Modifier.isStatic(m.getModifiers()) || Modifier.isPrivate(m.getModifiers()) || m.isSynthetic()) {
                continue;
            }
            ResolvedJavaMethod rm = metaAccess.lookupJavaMethod(m);
            String nd = nameDesc(rm);
            if (m.getParameterCount() > 0 && m.getParameterTypes()[0] == Object.class) {
                declaredOps.add(nd);
            } else {
                Assert.assertTrue("a MonitorSupport method that is neither listed nor known as a non-object operation: " + nd, NOT_OBJECT_OPERATIONS.contains(nd));
            }
        }
        Assert.assertEquals("MonitorPrimitive.OPERATIONS = the object operations MonitorSupport declares", declaredOps, new TreeSet<>(MonitorPrimitive.OPERATIONS));
    }

    @Test
    public void declarationAndImplementationAreRecognised() {
        ResolvedJavaType ms = type(MONITOR_SUPPORT);
        for (String op : MonitorPrimitive.OPERATIONS) {
            Assert.assertTrue("declaration " + op, MonitorPrimitive.isOperation(declared(ms, op)));
            ResolvedJavaMethod impl = implementation(op);
            Assert.assertTrue("implementation " + id(impl), MonitorPrimitive.isOperation(impl));
            Assert.assertEquals("the object is the first declared parameter (argument slot " + MonitorPrimitive.OBJECT_SLOT + ")", JavaKind.Object,
                            impl.getSignature().getParameterKind(MonitorPrimitive.OBJECT_SLOT - 1));
        }
    }

    @Test
    public void otherMethodsAreNotMonitorOperations() {
        ResolvedJavaType mt = type(MT_MONITOR_SUPPORT);
        Assert.assertFalse(MonitorPrimitive.isOperation(declared(mt, "getParkedThreadStatus(Ljava/lang/Thread;Z)I")));
        // the internal helpers are reached only through the operations (never modelled themselves)
        Assert.assertFalse(MonitorPrimitive.isOperation(declared(mt,
                        "getOrCreateMonitor(Ljava/lang/Object;Lcom/oracle/svm/core/monitor/MonitorInflationCause;)Lcom/oracle/svm/core/monitor/JavaMonitor;")));
        // the same names elsewhere are ordinary code (the model is keyed on the declaring class)
        ResolvedJavaType object = metaAccess.lookupJavaType(Object.class);
        Assert.assertFalse(MonitorPrimitive.isOperation(declared(object, "wait(J)V")));
        Assert.assertFalse(MonitorPrimitive.isOperation(declared(object, "notify()V")));
        Assert.assertFalse(MonitorPrimitive.isOperation(declared(type("com.oracle.svm.core.monitor.JavaMonitor"), "monitorEnter(Ljava/lang/Object;)V")));
        Assert.assertFalse(MonitorPrimitive.isOperation(null));
    }

    /**
     * Every call of a monitor operation from SVM code outside the monitor package (the substitutions of
     * {@code Object.wait/notify/notifyAll}, {@code Thread.holdsLock}, {@code Throwable}, JNI, deoptimization, the
     * reference handler, the interpreter, ...) targets a listed operation or a known non-object method: a constant-pool
     * scan of every class next to {@code MonitorSupport}.
     * <p>
     * The scan covers only the jar that holds {@code MonitorSupport}. A caller in another jar costs precision only, never
     * soundness: a call of an unlisted method is entered as before, and a call of a listed one is modelled correctly.
     */
    @Test
    public void everyCalledMonitorOperationIsListed() throws IOException, URISyntaxException {
        JarScan scan = scanMonitorJar();
        Map<String, Set<String>> refs = scan.refs;
        Map<String, String> superOf = scan.superOf;
        Assert.assertTrue("scanned the SVM classes (" + scan.scanned + ")", scan.scanned > 1000);
        // the known callers must be seen (the scan works)
        Assert.assertTrue(refs.toString(), refs.containsKey("wait(Ljava/lang/Object;J)V") && refs.containsKey("notify(Ljava/lang/Object;Z)V") &&
                        refs.containsKey("isLockedByAnyThread(Ljava/lang/Object;)Z") && refs.containsKey("isLockedByCurrentThread(Ljava/lang/Object;)Z"));
        for (Map.Entry<String, Set<String>> e : refs.entrySet()) {
            Assert.assertTrue("a monitor operation called from " + e.getValue() + " is not listed: " + e.getKey(),
                            MonitorPrimitive.OPERATIONS.contains(e.getKey()) || NOT_OBJECT_OPERATIONS.contains(e.getKey()));
        }
        // the implementation the premise is checked on is the only one, and the lock and condition classes the object
        // is passed to have no subclass that could override the checked code
        Map<String, Set<String>> subclasses = new HashMap<>();
        for (Map.Entry<String, String> e : superOf.entrySet()) {
            subclasses.computeIfAbsent(e.getValue(), k -> new TreeSet<>()).add(e.getKey());
        }
        Assert.assertEquals(Set.of(MT_MONITOR_SUPPORT.replace('.', '/')), subclasses.getOrDefault(MONITOR_SUPPORT.replace('.', '/'), Set.of()));
        for (String leaf : List.of(MT_MONITOR_SUPPORT, "com.oracle.svm.core.monitor.JavaMonitor", "com.oracle.svm.core.monitor.JavaMonitorQueuedSynchronizer$JavaMonitorConditionObject")) {
            Assert.assertEquals("subclasses of " + leaf, Set.of(), subclasses.getOrDefault(leaf.replace('.', '/'), Set.of()));
        }
    }

    /** The constant-pool scan of the jar that holds MonitorSupport (one jar; see everyCalledMonitorOperationIsListed). */
    static final class JarScan {
        /** Methodref (name+descriptor) to MonitorSupport / MultiThreadedMonitorSupport -> the calling classes outside the monitor package. */
        final Map<String, Set<String>> refs = new HashMap<>();
        final Map<String, String> superOf = new HashMap<>();
        /** Fieldref (holder.name) of a MultiThreadedMonitorSupport field -> every class whose constant pool names it. */
        final Map<String, Set<String>> mtFieldRefs = new HashMap<>();
        int scanned;
    }

    private static JarScan jarScan;

    private static synchronized JarScan scanMonitorJar() throws IOException, URISyntaxException {
        if (jarScan != null) {
            return jarScan;
        }
        JarScan scan = new JarScan();
        Path root = Path.of(load(MONITOR_SUPPORT).getProtectionDomain().getCodeSource().getLocation().toURI());
        if (Files.isDirectory(root)) {
            try (Stream<Path> files = Files.walk(root)) {
                for (Path p : (Iterable<Path>) files.filter(f -> f.toString().endsWith(".class"))::iterator) {
                    try (InputStream in = Files.newInputStream(p)) {
                        scanClass(root.relativize(p).toString(), in, scan);
                        scan.scanned++;
                    }
                }
            }
        } else {
            try (JarFile jar = new JarFile(root.toFile())) {
                for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements();) {
                    JarEntry je = e.nextElement();
                    if (je.getName().endsWith(".class") && !je.getName().startsWith("META-INF/")) {
                        try (InputStream in = jar.getInputStream(je)) {
                            scanClass(je.getName(), in, scan);
                            scan.scanned++;
                        }
                    }
                }
            }
        }
        jarScan = scan;
        return scan;
    }

    /**
     * Collects the Methodrefs to MonitorSupport / MultiThreadedMonitorSupport of a class outside the monitor package, and
     * the Fieldrefs of MultiThreadedMonitorSupport's fields of every class.
     */
    private static void scanClass(String entry, InputStream raw, JarScan scan) throws IOException {
        Map<String, Set<String>> refs = scan.refs;
        Map<String, String> superOf = scan.superOf;
        String cls = entry.replace('\\', '/');
        boolean monitorPackage = cls.startsWith(MONITOR_PACKAGE.replace('.', '/'));
        DataInputStream in = new DataInputStream(raw);
        if (in.readInt() != 0xCAFEBABE) {
            return;
        }
        in.readUnsignedShort();
        in.readUnsignedShort();
        int n = in.readUnsignedShort();
        String[] utf8 = new String[n];
        int[] classNameIdx = new int[n];
        int[][] memberRef = new int[n][];
        int[][] fieldRef = new int[n][];
        int[][] nameAndType = new int[n][];
        for (int i = 1; i < n; i++) {
            int tag = in.readUnsignedByte();
            switch (tag) {
                case 1 -> utf8[i] = in.readUTF();
                case 7 -> classNameIdx[i] = in.readUnsignedShort();
                case 8, 16, 19, 20 -> in.readUnsignedShort();
                case 3, 4 -> in.readInt();
                case 5, 6 -> {
                    in.readLong();
                    i++;
                }
                case 9 -> fieldRef[i] = new int[]{in.readUnsignedShort(), in.readUnsignedShort()};
                case 10, 11 -> memberRef[i] = new int[]{in.readUnsignedShort(), in.readUnsignedShort()};
                case 12 -> nameAndType[i] = new int[]{in.readUnsignedShort(), in.readUnsignedShort()};
                case 15 -> {
                    in.readUnsignedByte();
                    in.readUnsignedShort();
                }
                case 17, 18 -> {
                    in.readUnsignedShort();
                    in.readUnsignedShort();
                }
                default -> throw new AssertionError("unknown constant pool tag " + tag + " in " + entry);
            }
        }
        in.readUnsignedShort(); // access flags
        int thisClass = in.readUnsignedShort();
        int superClass = in.readUnsignedShort();
        if (superClass != 0) {
            superOf.put(utf8[classNameIdx[thisClass]], utf8[classNameIdx[superClass]]);
        }
        for (int i = 1; i < n; i++) {
            if (fieldRef[i] != null && utf8[classNameIdx[fieldRef[i][0]]].equals(MT_MONITOR_SUPPORT.replace('.', '/'))) {
                scan.mtFieldRefs.computeIfAbsent(MT_MONITOR_SUPPORT + "." + utf8[nameAndType[fieldRef[i][1]][0]], k -> new TreeSet<>()).add(utf8[classNameIdx[thisClass]]);
            }
        }
        for (int i = 1; i < n && !monitorPackage; i++) {
            if (memberRef[i] == null) {
                continue;
            }
            String holder = utf8[classNameIdx[memberRef[i][0]]];
            if (!holder.equals(MONITOR_SUPPORT.replace('.', '/')) && !holder.equals(MT_MONITOR_SUPPORT.replace('.', '/'))) {
                continue;
            }
            int[] nt = nameAndType[memberRef[i][1]];
            refs.computeIfAbsent(utf8[nt[0]] + utf8[nt[1]], k -> new TreeSet<>()).add(cls);
        }
    }

    // ------------------------------------------------------------------
    // The premise
    // ------------------------------------------------------------------

    @Test
    public void operationsOnlyObserveTheObject() {
        ObjectUseChecker checker = new ObjectUseChecker();
        StringBuilder bad = new StringBuilder();
        for (String op : new TreeSet<>(MonitorPrimitive.OPERATIONS)) {
            ResolvedJavaMethod impl = implementation(op);
            Summary s = checker.summary(impl, 1);
            for (String v : s.violations) {
                bad.append("\n  ").append(op).append(": ").append(v);
            }
            if (s.returnsObject) {
                bad.append("\n  ").append(op).append(": returns the object");
            }
        }
        Assert.assertEquals("the monitor operations must only observe their object (the premise of the monitor model):" + bad, "", bad.toString());
        // the walk really followed the object through the implementation (not a vacuous pass)
        Assert.assertTrue(checker.analysed.toString(), checker.analysed.contains(MT_MONITOR_SUPPORT +
                        ".getOrCreateMonitorFromObject(Ljava/lang/Object;ZILcom/oracle/svm/core/monitor/MonitorInflationCause;)Lcom/oracle/svm/core/monitor/JavaMonitor;"));
        Assert.assertTrue(checker.analysed.toString(), checker.analysed.contains(MT_MONITOR_SUPPORT +
                        ".createMonitorAndAddToMap(Ljava/lang/Object;Lcom/oracle/svm/core/monitor/MonitorInflationCause;)Lcom/oracle/svm/core/monitor/JavaMonitor;"));
        Assert.assertTrue(checker.analysed.toString(), checker.analysed.contains("com.oracle.svm.core.monitor.JavaMonitor.monitorEnter(Ljava/lang/Object;)V"));
        Assert.assertTrue(checker.analysed.toString(), checker.analysed.stream().anyMatch(m -> m.startsWith("com.oracle.svm.core.jfr.events.JavaMonitorWaitEvent.")));
        Assert.assertTrue(checker.analysed.toString(), checker.analysed.stream().anyMatch(m -> m.contains("ConditionObject.await(Ljava/lang/Object;")));
    }

    /**
     * The private weak monitor map is only queried by identity: every Map call in the implementation is get or put, and
     * the map never leaves {@code MultiThreadedMonitorSupport}: only that class's constant pool names the field, and each
     * read of it is consumed only as the receiver of {@code get}/{@code put} (a taint walk: never stored, returned,
     * thrown or passed to other code, e.g. code that could iterate its keys).
     */
    @Test
    public void weakMonitorMapIsOnlyQueriedByIdentity() throws IOException, URISyntaxException {
        ResolvedJavaType mt = type(MT_MONITOR_SUPPORT);
        int mapFields = 0;
        String mapField = null;
        for (var f : mt.getInstanceFields(false)) {
            if (f.getType().getName().equals("Ljava/util/Map;") || f.getType().getName().equals("Lcom/oracle/svm/core/WeakIdentityHashMap;")) {
                mapFields++;
                mapField = f.getName();
                Assert.assertTrue("the monitor map is private: " + f, Modifier.isPrivate(f.getModifiers()));
            }
        }
        Assert.assertEquals("one map field (additionalMonitors)", 1, mapFields);
        // only MultiThreadedMonitorSupport's own code reads or writes the field (no nestmate, no other class)
        Assert.assertEquals("the classes that name the map field", Set.of(MT_MONITOR_SUPPORT.replace('.', '/')),
                        scanMonitorJar().mtFieldRefs.getOrDefault(MT_MONITOR_SUPPORT + "." + mapField, Set.of()));
        // every read of the field is used only as the receiver of get/put
        ObjectUseChecker mapChecker = new ObjectUseChecker(MT_MONITOR_SUPPORT, mapField, Set.of());
        StringBuilder bad = new StringBuilder();
        List<ResolvedJavaMethod> all = new ArrayList<>(Arrays.asList(mt.getDeclaredMethods(false)));
        all.addAll(Arrays.asList(mt.getDeclaredConstructors(false)));
        for (ResolvedJavaMethod m : all) {
            if (m.getCode() == null) {
                continue;
            }
            Summary s = mapChecker.summary(m, -1);
            for (String v : s.violations) {
                bad.append("\n  ").append(v);
            }
            if (s.returnsObject) {
                bad.append("\n  ").append(id(m)).append(": returns the map");
            }
        }
        Assert.assertEquals("the monitor map must not leave MultiThreadedMonitorSupport:" + bad, "", bad.toString());
        Assert.assertTrue("the walk saw the map's get and put (" + mapChecker.seedUses + ")", mapChecker.seedUses.containsAll(MAP_RECEIVER_USES.keySet()));
        List<ResolvedJavaMethod> ms = new ArrayList<>(Arrays.asList(mt.getDeclaredMethods(false)));
        ms.addAll(Arrays.asList(mt.getDeclaredConstructors(false)));
        int calls = 0;
        Set<String> seen = new TreeSet<>();
        for (ResolvedJavaMethod m : ms) {
            if (m.getCode() == null) {
                continue;
            }
            BytecodeStream s = new BytecodeStream(m.getCode());
            for (; s.currentBC() != Bytecodes.END; s.next()) {
                int bc = s.currentBC();
                if (bc == Bytecodes.INVOKEVIRTUAL || bc == Bytecodes.INVOKEINTERFACE) {
                    JavaMethod callee = m.getConstantPool().lookupMethod(s.readCPI(), bc, m);
                    String holder = callee.getDeclaringClass().toJavaName();
                    seen.add(id(callee));
                    if (holder.equals("java.util.Map") || holder.equals("com.oracle.svm.core.WeakIdentityHashMap")) {
                        calls++;
                        Assert.assertTrue("a Map call in " + id(m) + " other than get/put: " + id(callee), callee.getName().equals("get") || callee.getName().equals("put"));
                    }
                }
            }
        }
        Assert.assertTrue("the map is used: " + seen, calls >= 2);
    }

    // ------------------------------------------------------------------
    // Mutation controls: the checker sees what the premise excludes
    // ------------------------------------------------------------------

    static Object sink;
    Object field;

    static void storeStatic(Object o) {
        sink = o;
    }

    void storeField(Object o) {
        field = o;
    }

    static void storeArray(Object o, Object[] a) {
        a[0] = o;
    }

    static Object returnIt(Object o) {
        return o;
    }

    static String escapes(Object o) {
        return String.valueOf(o);
    }

    static int readsState(MonitorPrimitiveTest o) {
        return o.field == null ? 0 : 1;
    }

    static int observes(Object o) {
        Object c = o.getClass();
        return o == null || c == null ? 0 : o instanceof String ? 1 : 2;
    }

    static Object sinkRec;

    /**
     * The object reaches the store only through a recursive call's result. The walk meets the recursive
     * call before the {@code return} of the object (the longer path), so an in-progress summary would still say "does
     * not return the object" there.
     */
    static Object storesWhatItsRecursionReturns(Object o, int n) {
        if (n > 0) {
            sinkRec = storesWhatItsRecursionReturns(o, n - 1);
            return null;
        }
        Object p = o;
        Object q = p;
        Object r = q;
        Object t = r;
        return t;
    }

    private final Map<Object, Object> ctlMap = new HashMap<>();

    /** The map mode's allowed use: a query by identity. */
    Object mapQueried(Object k) {
        Object v = ctlMap.get(k);
        return v != null ? v : ctlMap.put(k, k);
    }

    /** The map object leaves: stored, iterated, returned. */
    void mapStored() {
        sink = ctlMap;
    }

    int mapIterated() {
        return ctlMap.keySet().size();
    }

    Map<Object, Object> mapReturned() {
        return ctlMap;
    }

    private Summary control(String name) {
        return control(new ObjectUseChecker(null, null, Set.of(MonitorPrimitiveTest.class.getName())), name, -2);
    }

    private Summary mapControl(String name) {
        return control(new ObjectUseChecker(MonitorPrimitiveTest.class.getName(), "ctlMap", Set.of()), name, -1);
    }

    private Summary control(ObjectUseChecker checker, String name, int local) {
        ResolvedJavaType t = metaAccess.lookupJavaType(MonitorPrimitiveTest.class);
        t.link();
        for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
            if (m.getName().equals(name)) {
                return checker.summary(m, local == -2 ? (m.isStatic() ? 0 : 1) : local);
            }
        }
        throw new AssertionError(name);
    }

    @Test
    public void checkerCatchesWhatThePremiseExcludes() {
        Assert.assertFalse("static store", control("storeStatic").violations.isEmpty());
        Assert.assertFalse("field store", control("storeField").violations.isEmpty());
        Assert.assertFalse("array store", control("storeArray").violations.isEmpty());
        Assert.assertTrue("return", control("returnIt").returnsObject);
        Assert.assertFalse("escape into unknown code", control("escapes").violations.isEmpty());
        Assert.assertFalse("field read", control("readsState").violations.isEmpty());
        Summary obs = control("observes");
        Assert.assertTrue(obs.violations.toString(), obs.violations.isEmpty());
        Assert.assertFalse(obs.returnsObject);
        // a use of what a recursive call returns is checked (the in-progress summary is conservative)
        Assert.assertFalse("a store of a recursive call's result", control("storesWhatItsRecursionReturns").violations.isEmpty());
        // the map mode: a query by identity passes; a store, an iteration or a return of the map is caught
        Summary q = mapControl("mapQueried");
        Assert.assertTrue(q.violations.toString(), q.violations.isEmpty());
        Assert.assertFalse(q.returnsObject);
        Assert.assertFalse("map stored", mapControl("mapStored").violations.isEmpty());
        Assert.assertFalse("map iterated", mapControl("mapIterated").violations.isEmpty());
        Assert.assertTrue("map returned", mapControl("mapReturned").returnsObject);
    }

    // ------------------------------------------------------------------
    // The checker: a bytecode taint walk of one object parameter
    // ------------------------------------------------------------------

    static final class Summary {
        final List<String> violations = new ArrayList<>();
        boolean returnsObject;
    }

    /** The conservative summary of a call into a summary that is still being computed; never written. */
    private static final Summary IN_PROGRESS = new Summary();
    static {
        IN_PROGRESS.returnsObject = true;
    }

    /**
     * Follows one reference (a parameter) through a method's bytecode, per stack word and local slot (the values
     * copied from it by load/store/dup/checkcast), over every path and exception handler. Calls into the monitor
     * implementation and its JFR events are followed (per parameter position, memoized); the uses listed in
     * {@link #OBSERVING_CALLEES} and {@link #MONITOR_MAP_KEYS} end the walk; every other use of the reference is a
     * violation, except the pure observations of the reference (null checks, reference comparisons, instanceof,
     * monitorenter/exit).
     */
    final class ObjectUseChecker {
        final Map<String, Summary> memo = new HashMap<>();
        final Set<String> analysed = new TreeSet<>();
        /** Summaries whose walk is still running (a recursive cycle reaches them before they are final). */
        private final Set<String> inProgress = new HashSet<>();
        /** The map mode: the tracked value is every read of this field (null: the object mode). */
        private final String seedHolder;
        private final String seedField;
        /** Classes (Java names) whose calls are followed besides the monitor code (the controls: this test class). */
        private final Set<String> alsoFollowed;
        /** The allowed terminal uses the walk met (the map mode's get/put: the pin is not vacuous). */
        final Set<String> seedUses = new TreeSet<>();

        /** The object mode: the premise's walk of an operation's object parameter. */
        ObjectUseChecker() {
            this(null, null, Set.of());
        }

        ObjectUseChecker(String seedHolder, String seedField, Set<String> alsoFollowed) {
            this.seedHolder = seedHolder;
            this.seedField = seedField;
            this.alsoFollowed = alsoFollowed;
        }

        /**
         * The summary of {@code m} with {@code local} tracked ({@code -1}: none; the map mode's field reads only). A
         * summary reached again during its own walk (a recursive cycle) is not final, so the caller gets the
         * conservative answer: the call may return the tracked value (its uses after the call are checked); its
         * violations are reported by the running walk.
         */
        Summary summary(ResolvedJavaMethod m, int local) {
            String key = id(m) + "#" + local;
            if (inProgress.contains(key)) {
                return IN_PROGRESS;
            }
            Summary s = memo.get(key);
            if (s != null) {
                return s;
            }
            s = new Summary();
            memo.put(key, s);
            analysed.add(id(m));
            inProgress.add(key);
            walk(m, local, s);
            inProgress.remove(key);
            return s;
        }

        private boolean followed(String holder) {
            return holder.startsWith(MONITOR_PACKAGE) || MONITOR_EVENTS.contains(holder) || alsoFollowed.contains(holder);
        }

        private boolean isSeed(JavaField fld) {
            return seedField != null && fld.getName().equals(seedField) && fld.getDeclaringClass().toJavaName().equals(seedHolder);
        }

        private void walk(ResolvedJavaMethod m, int local, Summary out) {
            byte[] code = m.getCode();
            if (code == null) {
                out.violations.add(id(m) + ": no bytecode (native or abstract)");
                return;
            }
            int maxLocals = m.getMaxLocals();
            boolean[] entryLocals = new boolean[maxLocals];
            if (local >= 0) {
                entryLocals[local] = true;
            }
            Map<Integer, Frame> states = new HashMap<>();
            ArrayDeque<Integer> work = new ArrayDeque<>();
            states.put(0, new Frame(entryLocals, new ArrayList<>()));
            work.add(0);
            BytecodeStream s = new BytecodeStream(code);
            while (!work.isEmpty()) {
                int bci = work.poll();
                Frame f = states.get(bci).copy();
                s.setBCI(bci);
                for (ExceptionHandler h : m.getExceptionHandlers()) {
                    if (bci >= h.getStartBCI() && bci < h.getEndBCI()) {
                        List<Boolean> hs = new ArrayList<>();
                        hs.add(false);
                        merge(states, work, h.getHandlerBCI(), new Frame(f.locals.clone(), hs));
                    }
                }
                List<Integer> succ = step(m, s, f, out);
                for (int t : succ) {
                    merge(states, work, t, f);
                }
            }
        }

        private void merge(Map<Integer, Frame> states, ArrayDeque<Integer> work, int bci, Frame f) {
            Frame old = states.get(bci);
            if (old == null) {
                states.put(bci, f.copy());
                work.add(bci);
                return;
            }
            Assert.assertEquals("stack height at bci " + bci, old.stack.size(), f.stack.size());
            boolean changed = false;
            for (int i = 0; i < old.locals.length; i++) {
                if (f.locals[i] && !old.locals[i]) {
                    old.locals[i] = true;
                    changed = true;
                }
            }
            for (int i = 0; i < old.stack.size(); i++) {
                if (f.stack.get(i) && !old.stack.get(i)) {
                    old.stack.set(i, true);
                    changed = true;
                }
            }
            if (changed) {
                work.add(bci);
            }
        }

        /** Executes the instruction at the stream's position on {@code f}; returns the successor bcis. */
        private List<Integer> step(ResolvedJavaMethod m, BytecodeStream s, Frame f, Summary out) {
            int bc = s.currentBC();
            int bci = s.currentBCI();
            String at = id(m) + "@" + bci + " " + Bytecodes.nameOf(bc);
            List<Integer> next = List.of(s.nextBCI());
            switch (bc) {
                case Bytecodes.ALOAD, Bytecodes.ALOAD_0, Bytecodes.ALOAD_1, Bytecodes.ALOAD_2, Bytecodes.ALOAD_3 -> f.push(f.locals[bc == Bytecodes.ALOAD ? s.readLocalIndex()
                                : bc - Bytecodes.ALOAD_0]);
                case Bytecodes.ASTORE, Bytecodes.ASTORE_0, Bytecodes.ASTORE_1, Bytecodes.ASTORE_2, Bytecodes.ASTORE_3 -> f.locals[bc == Bytecodes.ASTORE ? s.readLocalIndex()
                                : bc - Bytecodes.ASTORE_0] = f.pop();
                case Bytecodes.ISTORE, Bytecodes.FSTORE -> {
                    f.pop();
                    f.locals[s.readLocalIndex()] = false;
                }
                case Bytecodes.LSTORE, Bytecodes.DSTORE -> {
                    f.pop(2);
                    f.locals[s.readLocalIndex()] = false;
                    f.locals[s.readLocalIndex() + 1] = false;
                }
                case Bytecodes.ISTORE_0, Bytecodes.ISTORE_1, Bytecodes.ISTORE_2, Bytecodes.ISTORE_3 -> {
                    f.pop();
                    f.locals[bc - Bytecodes.ISTORE_0] = false;
                }
                case Bytecodes.FSTORE_0, Bytecodes.FSTORE_1, Bytecodes.FSTORE_2, Bytecodes.FSTORE_3 -> {
                    f.pop();
                    f.locals[bc - Bytecodes.FSTORE_0] = false;
                }
                case Bytecodes.LSTORE_0, Bytecodes.LSTORE_1, Bytecodes.LSTORE_2, Bytecodes.LSTORE_3 -> {
                    f.pop(2);
                    f.locals[bc - Bytecodes.LSTORE_0] = false;
                    f.locals[bc - Bytecodes.LSTORE_0 + 1] = false;
                }
                case Bytecodes.DSTORE_0, Bytecodes.DSTORE_1, Bytecodes.DSTORE_2, Bytecodes.DSTORE_3 -> {
                    f.pop(2);
                    f.locals[bc - Bytecodes.DSTORE_0] = false;
                    f.locals[bc - Bytecodes.DSTORE_0 + 1] = false;
                }
                case Bytecodes.POP -> f.pop();
                case Bytecodes.POP2 -> f.pop(2);
                case Bytecodes.DUP -> f.dup(1, 0);
                case Bytecodes.DUP_X1 -> f.dup(1, 1);
                case Bytecodes.DUP_X2 -> f.dup(1, 2);
                case Bytecodes.DUP2 -> f.dup(2, 0);
                case Bytecodes.DUP2_X1 -> f.dup(2, 1);
                case Bytecodes.DUP2_X2 -> f.dup(2, 2);
                case Bytecodes.SWAP -> {
                    boolean a = f.pop();
                    boolean b = f.pop();
                    f.push(a);
                    f.push(b);
                }
                case Bytecodes.CHECKCAST -> {
                    // the same reference
                }
                case Bytecodes.INSTANCEOF, Bytecodes.ARRAYLENGTH -> {
                    if (f.pop() && bc == Bytecodes.ARRAYLENGTH) {
                        out.violations.add(at + ": array access");
                    }
                    f.push(false);
                }
                case Bytecodes.MONITORENTER, Bytecodes.MONITOREXIT, Bytecodes.IFNULL, Bytecodes.IFNONNULL -> f.pop();
                case Bytecodes.IF_ACMPEQ, Bytecodes.IF_ACMPNE -> f.pop(2);
                case Bytecodes.ATHROW -> {
                    if (f.pop()) {
                        out.violations.add(at + ": thrown");
                    }
                    return List.of();
                }
                case Bytecodes.ARETURN -> {
                    if (f.pop()) {
                        out.returnsObject = true;
                    }
                    return List.of();
                }
                case Bytecodes.IRETURN, Bytecodes.LRETURN, Bytecodes.FRETURN, Bytecodes.DRETURN, Bytecodes.RETURN -> {
                    return List.of();
                }
                case Bytecodes.IALOAD, Bytecodes.FALOAD, Bytecodes.AALOAD, Bytecodes.BALOAD, Bytecodes.CALOAD, Bytecodes.SALOAD, Bytecodes.LALOAD, Bytecodes.DALOAD -> {
                    f.pop();
                    if (f.pop()) {
                        out.violations.add(at + ": array read");
                    }
                    f.pushWords(bc == Bytecodes.LALOAD || bc == Bytecodes.DALOAD ? 2 : 1);
                }
                case Bytecodes.IASTORE, Bytecodes.FASTORE, Bytecodes.AASTORE, Bytecodes.BASTORE, Bytecodes.CASTORE, Bytecodes.SASTORE, Bytecodes.LASTORE, Bytecodes.DASTORE -> {
                    boolean value = false;
                    if (bc == Bytecodes.LASTORE || bc == Bytecodes.DASTORE) {
                        f.pop(2);
                    } else {
                        value = f.pop();
                    }
                    f.pop();
                    boolean array = f.pop();
                    if (value || array) {
                        out.violations.add(at + (value ? ": stored into an array" : ": array write"));
                    }
                }
                case Bytecodes.GETSTATIC, Bytecodes.PUTSTATIC, Bytecodes.GETFIELD, Bytecodes.PUTFIELD -> {
                    JavaField fld = m.getConstantPool().lookupField(s.readCPI(), m, bc);
                    int words = fld.getJavaKind().getSlotCount();
                    if (bc == Bytecodes.PUTSTATIC || bc == Bytecodes.PUTFIELD) {
                        boolean value = words == 1 ? f.pop() : f.pop(2);
                        if (value) {
                            out.violations.add(at + ": stored into field " + fld.format("%H.%n"));
                        }
                    }
                    if (bc == Bytecodes.GETFIELD || bc == Bytecodes.PUTFIELD) {
                        if (f.pop()) {
                            out.violations.add(at + ": its field " + fld.format("%H.%n") + " is accessed");
                        }
                    }
                    if (bc == Bytecodes.GETSTATIC || bc == Bytecodes.GETFIELD) {
                        if (isSeed(fld)) {
                            f.push(true); // the map mode: a read of the tracked field
                        } else {
                            f.pushWords(words);
                        }
                    }
                }
                case Bytecodes.INVOKEVIRTUAL, Bytecodes.INVOKESPECIAL, Bytecodes.INVOKESTATIC, Bytecodes.INVOKEINTERFACE, Bytecodes.INVOKEDYNAMIC -> invoke(m, s, f, out, at, bc);
                case Bytecodes.LDC, Bytecodes.LDC_W -> f.pushWords(1);
                case Bytecodes.LDC2_W -> f.pushWords(2);
                case Bytecodes.MULTIANEWARRAY -> {
                    f.pop(s.readUByte(bci + 3));
                    f.pushWords(1);
                }
                case Bytecodes.GOTO, Bytecodes.GOTO_W -> next = List.of(s.readBranchDest());
                case Bytecodes.IFEQ, Bytecodes.IFNE, Bytecodes.IFLT, Bytecodes.IFGE, Bytecodes.IFGT, Bytecodes.IFLE -> f.pop();
                case Bytecodes.IF_ICMPEQ, Bytecodes.IF_ICMPNE, Bytecodes.IF_ICMPLT, Bytecodes.IF_ICMPGE, Bytecodes.IF_ICMPGT, Bytecodes.IF_ICMPLE -> f.pop(2);
                case Bytecodes.TABLESWITCH, Bytecodes.LOOKUPSWITCH -> {
                    f.pop();
                    BytecodeSwitch sw = bc == Bytecodes.TABLESWITCH ? new BytecodeTableSwitch(s, bci) : new BytecodeLookupSwitch(s, bci);
                    List<Integer> ts = new ArrayList<>();
                    ts.add(sw.defaultTarget());
                    for (int i = 0; i < sw.numberOfCases(); i++) {
                        ts.add(sw.targetAt(i));
                    }
                    return ts;
                }
                case Bytecodes.JSR, Bytecodes.JSR_W, Bytecodes.RET -> throw new AssertionError(at + ": jsr/ret is not supported");
                default -> {
                    // every other instruction reads and writes primitives only (or pushes a fresh reference): its
                    // inputs are never the tracked reference, so only the stack depth changes
                    int e = Bytecodes.stackEffectOf(bc);
                    if (e < 0) {
                        f.pop(-e);
                    } else {
                        f.pushWords(e);
                    }
                    if (bc == Bytecodes.ILOAD || bc == Bytecodes.LLOAD || bc == Bytecodes.FLOAD || bc == Bytecodes.DLOAD || bc == Bytecodes.IINC || (bc >= Bytecodes.NOP && bc <= Bytecodes.DLOAD_3) ||
                                    (bc >= Bytecodes.IADD && bc <= Bytecodes.DCMPG) || bc == Bytecodes.NEW || bc == Bytecodes.NEWARRAY || bc == Bytecodes.ANEWARRAY) {
                        break;
                    }
                    throw new AssertionError(at + ": an instruction the checker does not model");
                }
            }
            if (Bytecodes.isConditionalBranch(bc)) {
                return List.of(s.nextBCI(), s.readBranchDest());
            }
            return next;
        }

        private void invoke(ResolvedJavaMethod m, BytecodeStream s, Frame f, Summary out, String at, int bc) {
            ConstantPool cp = m.getConstantPool();
            JavaMethod callee = bc == Bytecodes.INVOKEDYNAMIC ? cp.lookupMethod(s.readCPI4(), bc, m) : cp.lookupMethod(s.readCPI(), bc, m);
            Signature sig = callee.getSignature();
            boolean hasReceiver = bc != Bytecodes.INVOKESTATIC && bc != Bytecodes.INVOKEDYNAMIC;
            int n = sig.getParameterCount(false);
            // pop the arguments, last first; tainted[i] = argument position i (0 = the receiver of an instance call)
            boolean[] tainted = new boolean[n + (hasReceiver ? 1 : 0)];
            for (int i = n - 1; i >= 0; i--) {
                int w = sig.getParameterKind(i).getSlotCount();
                tainted[i + (hasReceiver ? 1 : 0)] = w == 1 ? f.pop() : f.pop(2);
            }
            if (hasReceiver) {
                tainted[0] = f.pop();
            }
            boolean resultTainted = false;
            String cid = id(callee);
            for (int pos = 0; pos < tainted.length; pos++) {
                if (!tainted[pos]) {
                    continue;
                }
                Set<Integer> ok;
                if (seedField != null) {
                    ok = MAP_RECEIVER_USES.get(cid); // the map mode: only the receiver of a query by identity
                } else {
                    ok = OBSERVING_CALLEES.get(cid);
                    if (ok == null && id(m).startsWith(MT_MONITOR_SUPPORT + ".")) {
                        ok = MONITOR_MAP_KEYS.get(cid);
                    }
                }
                if (ok != null && ok.contains(pos)) {
                    seedUses.add(cid);
                    continue;
                }
                String holder = callee.getDeclaringClass().toJavaName();
                if (bc != Bytecodes.INVOKEDYNAMIC && followed(holder)) {
                    ResolvedJavaMethod target = resolve(callee, bc);
                    int local = 0;
                    for (int i = 0; i < pos; i++) {
                        local += i == 0 && hasReceiver ? 1 : sig.getParameterKind(i - (hasReceiver ? 1 : 0)).getSlotCount();
                    }
                    Summary cs = summary(target, local);
                    for (String v : cs.violations) {
                        if (!out.violations.contains(v)) {
                            out.violations.add(v);
                        }
                    }
                    resultTainted |= cs.returnsObject;
                    continue;
                }
                out.violations.add(at + ": passed to " + cid + " at argument " + pos);
            }
            JavaKind rk = sig.getReturnKind();
            if (rk != JavaKind.Void) {
                if (rk.getSlotCount() == 2) {
                    f.pushWords(2);
                } else {
                    f.push(resultTainted);
                }
            }
        }

        /** The bytecode that runs for a call into the monitor code (the abstract MonitorSupport = its implementation). */
        private ResolvedJavaMethod resolve(JavaMethod callee, int bc) {
            ResolvedJavaType holder = type(callee.getDeclaringClass().toJavaName());
            ResolvedJavaMethod decl = callee instanceof ResolvedJavaMethod rm ? rm : null;
            for (ResolvedJavaType t = holder; decl == null && t != null; t = t.getSuperclass()) {
                decl = declared(t, nameDesc(callee));
            }
            Assert.assertNotNull("resolve " + id(callee), decl);
            if (bc == Bytecodes.INVOKESTATIC || bc == Bytecodes.INVOKESPECIAL || decl.isFinal() || decl.isPrivate()) {
                return decl;
            }
            // a virtual call: MonitorSupport runs as its only implementation (MonitorFeature); the lock and condition
            // classes have no SVM subclass, so their own method runs
            ResolvedJavaType impl = holder.getName().equals("L" + MONITOR_SUPPORT.replace('.', '/') + ";") ? type(MT_MONITOR_SUPPORT) : holder;
            ResolvedJavaMethod r = impl.resolveConcreteMethod(decl, impl);
            Assert.assertNotNull("implementation of " + id(callee), r);
            return r;
        }
    }

    /** The abstract frame: the taint of each local slot and of each operand-stack word. */
    static final class Frame {
        final boolean[] locals;
        final List<Boolean> stack;

        Frame(boolean[] locals, List<Boolean> stack) {
            this.locals = locals;
            this.stack = stack;
        }

        Frame copy() {
            return new Frame(locals.clone(), new ArrayList<>(stack));
        }

        void push(boolean t) {
            stack.add(t);
        }

        void pushWords(int n) {
            for (int i = 0; i < n; i++) {
                stack.add(false);
            }
        }

        boolean pop() {
            Assert.assertFalse("operand stack underflow", stack.isEmpty());
            return stack.remove(stack.size() - 1);
        }

        /** Pops {@code n} words; true if any was tainted. */
        boolean pop(int n) {
            boolean any = false;
            for (int i = 0; i < n; i++) {
                any |= pop();
            }
            return any;
        }

        /** The dup family: duplicates the top {@code n} words and inserts them {@code below} words further down. */
        void dup(int n, int below) {
            List<Boolean> top = new ArrayList<>(stack.subList(stack.size() - n, stack.size()));
            stack.addAll(stack.size() - n - below, top);
        }
    }
}
