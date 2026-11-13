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

import java.lang.reflect.Modifier;
import java.net.URI;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
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
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;
import jdk.vm.ci.meta.Signature;

/**
 * The premise of every JDK model entry ({@link JdkModels}), checked over the builder JDK's own
 * bytecode (the code the image runs: the SVM substitutions of the modelled classes only reset cached view fields). One
 * generic checker, parametrised by a family's table and abstraction map; a family adds no checker code.
 * <p>
 * The checker is a bytecode abstract interpreter of the entry method. Each stack word and local holds a set of
 * access-path labels relative to the entry's arguments: {@code A<i>} (argument i), {@code A<i>.f} (a real reference field
 * of it, depth 2), {@code R:<p>} (the representation: an abstracted field of {@code p}), {@code E:<p>} (an element of
 * that representation, i.e. a value of the slot), {@code C:<sig>} (the result of a call on a tracked value), and
 * {@code I<k>} (an {@code ir} slot k and every value derived from it: its flows are the real callee's, which
 * the engine walks, so they raise no violation, but an {@code I<k>} that reaches the result is reported unless the entry
 * has {@code result ir}: the backward walk uses only the declared result effects). Calls with a deterministic target (static,
 * special, private, final, package-private in {@code java.*}) that receive a tracked value are followed; a few JDK
 * helpers are summarised ({@code Arrays.copyOf}, {@code System.arraycopy}). Every other use of a tracked value is an
 * observed effect: a store into a representation (slot store), a result, a call on a tracked value (a callback, with
 * its JDK-internal site {@code holder#name(desc)@bci}), or a
 * violation (a store into a real field, a static, an unmodelled array, a throw, a lambda capture, an escape of the
 * representation). The premise: every observed effect is covered by a declared effect of the entry; no violation.
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.internal.vm.ci/jdk.vm.ci.code", "jdk.graal.compiler/jdk.graal.compiler.bytecode", "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.nodes"})
public class JdkModelPremiseTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private ResolvedJavaType type(String name) {
        try {
            ResolvedJavaType t = metaAccess.lookupJavaType(Class.forName(name, false, JdkModelPremiseTest.class.getClassLoader()));
            t.link();
            return t;
        } catch (ClassNotFoundException e) {
            throw new AssertionError("class not found: " + name, e);
        }
    }

    private static String nameDesc(JavaMethod m) {
        return m.getName() + m.getSignature().toMethodDescriptor();
    }

    private static String mid(JavaMethod m) {
        return m.getDeclaringClass().toJavaName() + "#" + nameDesc(m);
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

    private ResolvedJavaMethod method(String id) {
        int h = id.indexOf('#');
        ResolvedJavaMethod m = declared(type(id.substring(0, h)), id.substring(h + 1));
        Assert.assertNotNull("the model entry's method exists in the builder JDK: " + id, m);
        return m;
    }

    /** A method by id, declared by the class or one of its supertypes (a callback named by its call site's class). */
    private ResolvedJavaMethod inherited(String id) {
        int h = id.indexOf('#');
        ArrayDeque<ResolvedJavaType> todo = new ArrayDeque<>(List.of(type(id.substring(0, h))));
        while (!todo.isEmpty()) {
            ResolvedJavaType t = todo.poll();
            ResolvedJavaMethod m = declared(t, id.substring(h + 1));
            if (m != null) {
                return m;
            }
            if (t.getSuperclass() != null) {
                todo.add(t.getSuperclass());
            }
            todo.addAll(List.of(t.getInterfaces()));
        }
        throw new AssertionError("the callback resolves in the builder JDK: " + id);
    }

    private ResolvedJavaField field(String id) {
        int dot = id.lastIndexOf('.');
        for (ResolvedJavaField f : type(id.substring(0, dot)).getInstanceFields(false)) {
            if (f.getName().equals(id.substring(dot + 1))) {
                return f;
            }
        }
        return null;
    }

    // ------------------------------------------------------------------
    // The tests
    // ------------------------------------------------------------------

    /** Every entry: the method, members and callbacks resolve; slots are in range; every reference slot is covered. */
    @Test
    public void everyEntryResolvesAndCoversItsSlots() {
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            // one collapse key = one application for several targets: their effects must be the same
            Map<String, String> byKey = new HashMap<>();
            for (JdkModels.Op op : f.table.values()) {
                String prev = byKey.putIfAbsent(op.key(), op.effects().toString() + op.resultIr());
                Assert.assertTrue(op.method() + ": the entries of collapse key " + op.key() + " have the same effects", prev == null || prev.equals(op.effects().toString() + op.resultIr()));
            }
            for (JdkModels.Op op : f.table.values()) {
                ResolvedJavaMethod m = method(op.method());
                Signature sig = m.getSignature();
                boolean recv = !m.isStatic();
                int n = sig.getParameterCount(false) + (recv ? 1 : 0);
                Set<Integer> covered = new HashSet<>();
                for (JdkModels.Effect e : op.effects()) {
                    for (JdkModels.Ref r : e.operands()) {
                        Assert.assertTrue(op.method() + ": slot in range " + e, r.slot() < n);
                        if (r.slot() >= 0) {
                            covered.add(r.slot());
                        }
                        for (String p : r.members()) {
                            Assert.assertTrue(op.method() + ": member resolves " + p, JdkModels.slot(p) != null || p.equals("[]") || field(p) != null);
                        }
                    }
                    if (e instanceof JdkModels.Store st) {
                        String p = st.member();
                        Assert.assertTrue(op.method() + ": stored member resolves " + p, JdkModels.slot(p) != null || p.equals("[]") || field(p) != null);
                    }
                    if (e instanceof JdkModels.Fresh fr) {
                        type(fr.fresh()); // the FRESH class exists in the builder JDK
                    }
                    if (e instanceof JdkModels.Callback cbk) {
                        // the callback is an instance method (its parameter k is the entry's argument k + 1); or a
                        // static method of a family whose premise observes static calls (F6's String.valueOf: `a` is its parameter 0)
                        Assert.assertTrue(op.method() + ": the callback is not static " + cbk.cb(), !inherited(cbk.cb()).isStatic() || f.stringSinks);
                        for (String site : cbk.sites()) {
                            Assert.assertNotNull(op.method() + ": the callback's site resolves " + site, method(JdkModels.Effect.siteMethod(site)));
                        }
                    }
                }
                for (int s = 0; s < n; s++) {
                    JavaKind k = s == 0 && recv ? JavaKind.Object : sig.getParameterKind(s - (recv ? 1 : 0));
                    if (k == JavaKind.Object) {
                        Assert.assertTrue(op.method() + ": reference slot " + s + " is covered by an effect", covered.contains(s));
                    }
                }
                if (sig.getReturnKind() == JavaKind.Object) {
                    Assert.assertTrue(op.method() + ": a reference result has a result effect", op.hasResultEffect());
                }
            }
        }
    }

    /**
     * Only the reviewed families (F1, F3, F4, F2, F6: those with a closed class or an abstracted field, each reviewed
     * with its obligations) close or abstract anything: every other committed family closes nothing and abstracts nothing.
     */
    @Test
    public void noCommittedFamilyClosesOrAbstractsBeforeF1() {
        Set<String> reviewed = Set.of("f1", "f3", "f4", "f2", "f6"); // F4 closes java.util.stream and abstracts AbstractPipeline's links; F2 the hash maps; F6 the collectors' record
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (reviewed.contains(f.id)) {
                continue;
            }
            Assert.assertTrue(f.id + ": no closed class before its review " + f.closed, f.closed.isEmpty());
            Assert.assertTrue(f.id + ": no abstracted field before its review " + f.abstracted, f.abstracted.isEmpty());
        }
        Assert.assertTrue("F1 is committed with its representation", JdkModels.FAMILIES.stream().anyMatch(f -> f.id.equals("f1") && !f.abstracted.isEmpty()));
    }

    /**
     * An F6 prerequisite: no entry for a terminal target (an instance method of a stringy-declared class)
     * names the receiver slot: the model would replace a String receiver's terminal usage. The rule itself is checked on
     * control entries.
     */
    @Test
    public void noEntryHidesAStringReceiver() {
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (JdkModels.Op op : f.table.values()) {
                Assert.assertFalse(op.method() + " hides a String receiver's terminal usage", hides(op));
            }
        }
        JdkModels.Family ctl = new JdkModels.Family("m8-" + System.nanoTime(), false, Set.of(), Map.of());
        Assert.assertTrue("observe 0 on String.length", hides(JdkModels.parse(ctl, "java.lang.String#length()I : observe 0")));
        Assert.assertTrue("alias 0 on StringBuilder.append", hides(JdkModels.parse(ctl, "java.lang.StringBuilder#append(Ljava/lang/String;)Ljava/lang/StringBuilder; : alias 0 ; observe 1")));
        Assert.assertFalse("slot 0 uncovered (it refuses by name)", hides(JdkModels.parse(ctl, "java.lang.StringBuilder#append(Ljava/lang/String;)Ljava/lang/StringBuilder; : observe 1 ; result ir")));
        Assert.assertFalse("a static String method", hides(JdkModels.parse(ctl, "java.lang.String#valueOf(Ljava/lang/Object;)Ljava/lang/String; : observe 0 ; result ir")));
        Assert.assertFalse("a non-stringy class", hides(JdkModels.parse(ctl, "java.util.Objects#isNull(Ljava/lang/Object;)Z : observe 0")));
    }

    private boolean hides(JdkModels.Op op) {
        ResolvedJavaMethod m = method(op.method());
        return JdkModels.hidesStringReceiver(op, m.isStatic(), m.isConstructor(), m.getDeclaringClass().toJavaName(true));
    }

    /**
     * The checked bytecode is the image's code: no SVM {@code @TargetClass} substitutes a modelled class, and no
     * substitution of a class whose method the checker follows (a callback site's holder, e.g. {@code String.valueOf})
     * declares that method. The scan's control: it sees {@code Target_java_lang_String}.
     */
    @Test
    public void noSubstitutionReplacesTheCheckedCode() throws Exception {
        Set<String> modelled = new TreeSet<>();
        Set<String> modelledMethods = new TreeSet<>();
        Set<String> followed = new TreeSet<>();
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (JdkModels.Op op : f.table.values()) {
                modelled.add(op.method().substring(0, op.method().indexOf('#')));
                modelledMethods.add(op.method());
                if (f.lazy && LAZY_REVIEWED.containsKey(op.method())) {
                    continue; // a reviewed lazy entry has no premise walk
                }
                // a lazy entry's premise walk is the lazy checker's (it follows the composed stream code too)
                Checker c = f.lazy ? new LazyChecker(op) : new Checker(f);
                c.check(method(op.method()), op);
                followed.addAll(c.followed);
            }
        }
        List<JdkModelClassScan.Substitution> subs = substitutions();
        Assert.assertTrue("the scan sees the String substitution", subs.stream().anyMatch(x -> x.target().equals("java.lang.String") && x.self().endsWith("Target_java_lang_String")));
        for (JdkModelClassScan.Substitution x : subs) {
            // a substitution of a modelled class may reset fields (Target_java_util_Collections resets `r`); it must
            // not substitute a modelled method (by name; a constructor by descriptor)
            for (String mm : modelledMethods) {
                String holder = mm.substring(0, mm.indexOf('#'));
                String nd = mm.substring(mm.indexOf('#') + 1);
                String name = nd.substring(0, nd.indexOf('('));
                boolean same = x.methods().stream().anyMatch(sm -> name.equals("<init>") ? sm.equals(nd) : sm.substring(0, sm.indexOf('(')).equals(name));
                Assert.assertFalse(x.self() + " substitutes the modelled method " + mm, holder.equals(x.target()) && same);
            }
            for (String fm : followed) {
                String holder = fm.substring(0, fm.indexOf('#'));
                String nd = fm.substring(fm.indexOf('#') + 1);
                String name = nd.substring(0, nd.indexOf('('));
                // by name (a substitution's descriptor may name its alias types); a constructor by name and descriptor
                boolean same = x.methods().stream().anyMatch(sm -> name.equals("<init>") ? sm.equals(nd) : sm.substring(0, sm.indexOf('(')).equals(name));
                Assert.assertFalse(x.self() + " substitutes the followed method " + fm, holder.equals(x.target()) && same);
            }
        }
        System.out.println("[jdkmodel-premise] substitutions scanned " + subs.size() + "; modelled " + modelled + "; followed " + followed);
    }

    /**
     * The type-check IC writes no TYPE_CHECK line in a model body ({@link JdkModels#modelBodyMethod}),
     * because the walk does not walk a modelled value through it. That exclusion must cover every method this premise
     * checker descends into from an entry (the entries, the deterministic callees, the same-package overrides, the lazy
     * composition): a followed method with a {@code checkcast}/{@code instanceof java.lang.String} outside the exclusion
     * would get a line from walked contexts only, while a modelled value reaches it unobserved.
     */
    @Test
    public void typeCheckModelBodyExclusionCoversTheFollowedMethods() {
        Set<String> followed = new TreeSet<>();
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (JdkModels.Op op : f.table.values()) {
                if (f.lazy && LAZY_REVIEWED.containsKey(op.method())) {
                    /*
                     * A reviewed lazy entry: no premise walk (the entry itself is a model body). Resolved
                     * to its declaring-class id, the form compute keys an inherited body by (mid of the resolved method).
                     */
                    followed.add(mid(inherited(op.method())));
                    continue;
                }
                Checker c = f.lazy ? new LazyChecker(op) : new Checker(f);
                c.check(method(op.method()), op);
                followed.addAll(c.followed);
            }
        }
        List<String> uncovered = new ArrayList<>();
        int withChecks = 0;
        for (String fm : followed) {
            ResolvedJavaMethod m = inherited(fm);
            if (m == null || TypeCheckSites.stringTypeCheckBcis(m).isEmpty()) {
                continue;
            }
            withChecks++;
            String cls = fm.substring(0, fm.indexOf('#'));
            if (!JdkModels.modelBodyMethod(cls, fm)) {
                uncovered.add(fm + " " + TypeCheckSites.stringTypeCheckBcis(m).keySet());
            }
        }
        System.out.println("[jdkmodel-premise] followed " + followed.size() + "; with a String type check " + withChecks + "; outside the model-body exclusion " + uncovered);
        Assert.assertTrue("followed methods with a String type check outside JdkModels.modelBodyMethod: " + uncovered, uncovered.isEmpty());
    }

    /** Every {@code @TargetClass} class of the jar (or directory) that holds the SVM core substitutions. */
    private static List<JdkModelClassScan.Substitution> substitutions() throws Exception {
        Class<?> anchor = Class.forName("com.oracle.svm.core.jdk.JavaLangSubstitutions");
        List<JdkModelClassScan.Substitution> out = new ArrayList<>();
        java.net.URL loc = anchor.getProtectionDomain().getCodeSource() != null ? anchor.getProtectionDomain().getCodeSource().getLocation() : null;
        Assert.assertNotNull("the SVM core classes have a location", loc);
        Path p = Path.of(loc.toURI());
        if (Files.isDirectory(p)) {
            try (Stream<Path> files = Files.walk(p)) {
                for (Path f : (Iterable<Path>) files::iterator) {
                    if (f.toString().endsWith(".class")) {
                        JdkModelClassScan.Substitution x = JdkModelClassScan.substitution(Files.readAllBytes(f));
                        if (x != null) {
                            out.add(x);
                        }
                    }
                }
            }
        } else {
            try (java.util.zip.ZipFile z = new java.util.zip.ZipFile(p.toFile())) {
                for (var en = z.entries(); en.hasMoreElements();) {
                    var e = en.nextElement();
                    if (e.getName().endsWith(".class")) {
                        try (var in = z.getInputStream(e)) {
                            JdkModelClassScan.Substitution x = JdkModelClassScan.substitution(in.readAllBytes());
                            if (x != null) {
                                out.add(x);
                            }
                        }
                    }
                }
            }
        }
        return out;
    }

    /**
     * The representation is closed: every abstracted field is private or package-private in a {@code java.*}
     * package (no user class can name it), and only classes of that package reference it (a constant-pool scan of
     * the whole java.base module). Its accesses from those classes are either inside modelled entries (whose premise
     * is checked below) or refused by the engine's field rule when walked.
     */
    @Test
    public void representationFieldsAreClosed() throws Exception {
        List<JdkModels.Family> families = new ArrayList<>(JdkModels.FAMILIES);
        // the scan's own control (F7 abstracts no field): a representation field of java.base, not a committed model
        families.add(new JdkModels.Family("scan-control-" + System.nanoTime(), false, Set.of(), Map.of("java.util.ArrayList.elementData", "<elem>[]")));
        Map<String, Set<String>> refs = fieldReferences();
        Assert.assertTrue("the scan sees java.base's field references", refs.getOrDefault("java.util.ArrayList.elementData", Set.of()).contains("java.util.ArrayList$Itr"));
        for (JdkModels.Family f : families) {
            for (String id : f.abstracted.keySet()) {
                ResolvedJavaField rf = field(id);
                Assert.assertNotNull("abstracted field exists: " + id, rf);
                int mod = rf.getModifiers();
                // public: any code may name it. protected (Vector.elementData): a user subclass may, and its access meets
                // the engine's field rule (a named refusal), so the closure below is about the JDK's own code
                Assert.assertFalse(id + " is not public", Modifier.isPublic(mod));
                String pkg = id.substring(0, id.lastIndexOf('.', id.lastIndexOf('.') - 1));
                Assert.assertTrue(id + " is in a java.* package", pkg.startsWith("java."));
                String kind = f.abstracted.get(id);
                Assert.assertTrue("abstracted field has a representation kind: " + kind, JdkModels.arrayRepSlot(kind) != null || JdkModels.slot(kind) != null || kind.equals("-") ||
                                kind.startsWith("-@") && field(kind.substring(2)) != null);
                Set<String> users = fieldUsers(refs, id);
                Assert.assertFalse(id + " is referenced", users.isEmpty());
                for (String u : users) {
                    Assert.assertEquals(id + " referenced only in its package: " + u, pkg, u.substring(0, u.lastIndexOf('.')));
                }
                System.out.println("[jdkmodel-premise] " + id + " referenced by " + users);
            }
        }
    }

    /**
     * The premise of every entry: its observed effects are declared, and nothing is a violation. An {@code ir} slot is
     * seeded as {@code I<k>}: its flows are the real callee's, which the engine walks; that walk's accesses to a
     * representation field (also in a closed class's {@code ir} entries) are not checked here: the engine's field rule
     * refuses them.
     */
    @Test
    public void everyEntryOverApproximatesTheJdkCode() {
        List<String> failures = new ArrayList<>();
        int checked = 0;
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (f.lazy) {
                continue; // a lazy family's premise is the lazy one (everyLazyEntryOverApproximatesTheJdkCode: its JDK code runs at the terminal operation)
            }
            for (JdkModels.Op op : f.table.values()) {
                Checker c = new Checker(f);
                Result r = c.check(method(op.method()), op);
                checked++;
                System.out.println("[jdkmodel-premise] " + op.method() + " observed=" + r.observed + " violations=" + r.violations);
                for (String v : r.violations) {
                    if (REVIEWED_VIOLATIONS.keySet().stream().noneMatch(v::startsWith)) {
                        failures.add(v);
                    }
                }
                failures.addAll(r.uncovered(op));
            }
        }
        Assert.assertTrue("checked entries", checked > 0);
        Assert.assertTrue("premise failures: " + failures, failures.isEmpty());
    }

    /**
     * The checker's reports that are reviewed false positives (the prefix of the violation, its reason). The
     * checker tracks no null constants: a call whose receiver is a constant null in one walk and a tracked argument in
     * another is reported for the untracked one.
     */
    static final Map<String, String> REVIEWED_VIOLATIONS = Map.of(
                    "java.util.HashMap#removeNode(ILjava/lang/Object;Ljava/lang/Object;ZZ)Ljava/util/HashMap$Node;@200 invokevirtual: a tracked value is passed to java.lang.Object#equals(Ljava/lang/Object;)Z [[], [E<vals>:",
                    "removeNode's matchValue is the constant null at these calls (remove(key), the eviction and the compute / merge removals: removeNode(hash, key, null, false, true)), and " +
                                    "`matchValue && (value != null && value.equals(v))` never runs then (matchValue is false); with a real matchValue (remove(key, value), EntrySet.remove) the receiver is " +
                                    "the tracked argument and the callback is declared");

    /**
     * The abstraction map is complete. Every method of every class that references an abstracted
     * field (the constant-pool scan) is checked (with every argument tracked), and the representation (an {@code R}
     * label) must not leave the abstracted fields: into an unabstracted field, a static, a non-private method's result,
     * a callback's argument or a lambda capture. An unabstracted field that caches it (as {@code VectorSpliterator.array}
     * would, were it not abstracted: the control in {@link #checkerCatchesWhatThePremiseExcludes}) would let a later IR
     * read reach the representation without meeting the field rule. The findings below are reviewed (each reason stated):
     * none of them is such a field.
     */
    @Test
    public void openUsersCacheNoRepresentation() throws Exception {
        // reviewed findings: the method (or the call that reaches the site) is never walked as IR, or the value is not kept
        String sorted = "sort is deferred: an unlisted method of a closed class, refused by name, never walked as IR; the TimSort / ComparableTimSort object that caches the array is local to that call";
        Map<String, String> reviewed = new HashMap<>(Map.of(
                        "java.util.ArrayList#sort(Ljava/util/Comparator;)V | ", sorted,
                        "java.util.ArrayList#sortRange(Ljava/util/Comparator;II)V | ", "private, called only by ArrayList.sort and ArrayList$SubList.sort (refused by name): " + sorted,
                        "java.util.ArrayList$SubList#sort(Ljava/util/Comparator;)V | ", sorted,
                        "java.util.Vector#sort(Ljava/util/Comparator;)V | ", sorted,
                        "java.util.LinkedList#node(I)Ljava/util/LinkedList$Node; | ",
                        "package-private, called only in LinkedList.java by the closed classes LinkedList and LinkedList$ListItr (their unlisted methods refuse by name, the listed ones are premise-checked with this walk); ReverseOrderLinkedListView does not call it",
                        "java.util.LinkedList#unlink(Ljava/util/LinkedList$Node;)Ljava/lang/Object; | ",
                        "returns x.item, the ELEMENT of its node argument (the checker labels an element field read from a plain argument R:, conservatively), not a representation; package-private and called only by the closed classes LinkedList and ListItr",
                        //
                        "java.util.HashMap$TreeNode#",
                        "HashMap$TreeNode is a closed class of F2 (an unlisted method refuses by name, never walked as IR) whose methods (the tree bins) are called only by F2's closed HashMap / LinkedHashMap classes; " +
                                        "the scan seeds the node receiver as a plain argument, so its key reads are labelled R: (conservatively) and the nodes it returns are its bin's: nothing is cached in an open class's field"));
        // TreeMap's unlisted helpers (closed: refused by name, never walked as IR; the scan labels a node argument's key R:)
        String treeHelpers = "TreeMap is a closed class of F2: an unlisted method refuses by name and is never walked as IR (the scan seeds a node argument as a plain argument, so its key is labelled R:)";
        for (String h : List.of("key(", "keyOrNull(", "successor(", "predecessor(", "remapValue(", "mergeValue(", "callRemappingFunctionWithCheck(", "keySpliteratorFor(")) {
            reviewed.put("java.util.TreeMap#" + h, treeHelpers);
        }
        reviewed.put("java.util.TreeMap$NavigableSubMap$",
                        "the navigable sub-map views (deferred) are open: they obtain nodes only through TreeMap's unlisted methods (getCeilingEntry, successor, ...: refused by name), " +
                                        "and a node they hold in a field is read only through its abstracted fields (key / value / left / right / parent: the field rule); a node carries no slot value outside them");

        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (f.abstracted.isEmpty() || f.lazy) {
                // F4's abstracted fields (AbstractPipeline's links) are private to AbstractPipeline (the closure test), and
                // every class of java.util.stream is closed: no open user exists to cache them (the scan's subject)
                continue;
            }
            List<String> found = cachedRepresentations(f);
            System.out.println("[jdkmodel-premise] m-7 scan " + f.id + ": " + found.size() + " findings " + found);
            for (String x : found) {
                Assert.assertTrue("the representation leaves the abstracted fields (review it, then list it with its reason): " + x,
                                reviewed.keySet().stream().anyMatch(x::startsWith));
            }
        }
    }

    /**
     * The classes that reference field {@code id} ("Class.field"), also through a subclass's name (javac names the
     * field by the qualifying type: {@code KeySpliterator.current} for {@code HashMapSpliterator.current}).
     */
    private Set<String> fieldUsers(Map<String, Set<String>> refs, String id) {
        String cls = id.substring(0, id.lastIndexOf('.'));
        String name = id.substring(id.lastIndexOf('.') + 1);
        Set<String> users = new TreeSet<>(refs.getOrDefault(id, Set.of()));
        for (Map.Entry<String, Set<String>> r : refs.entrySet()) {
            String k = r.getKey();
            if (!k.equals(id) && k.endsWith("." + name) && k.startsWith(cls.substring(0, cls.lastIndexOf('.') + 1))) {
                try {
                    ResolvedJavaType q = type(k.substring(0, k.lastIndexOf('.')));
                    if (type(cls).isAssignableFrom(q) && field(k) == null) {
                        users.addAll(r.getValue()); // the qualifying subclass declares no field of that name: it is id's
                    }
                } catch (Throwable x) {
                    // not a loadable class name: not a subclass the image can hold
                }
            }
        }
        return users;
    }

    /** The abstraction-map completeness scan's findings for {@code f} (see {@link #openUsersCacheNoRepresentation}). */
    private List<String> cachedRepresentations(JdkModels.Family f) throws Exception {
        Map<String, Set<String>> refs = fieldReferences();
        Set<String> users = new TreeSet<>();
        for (String id : f.abstracted.keySet()) {
            users.addAll(fieldUsers(refs, id)); // also through a subclass's name
        }
        List<String> out = new ArrayList<>();
        for (String u : users) {
            ResolvedJavaType t = type(u);
            List<ResolvedJavaMethod> ms = new ArrayList<>(List.of(t.getDeclaredConstructors(false)));
            ms.addAll(List.of(t.getDeclaredMethods(false)));
            for (ResolvedJavaMethod m : ms) {
                if (m.getCode() == null) {
                    continue;
                }
                Checker c = new Checker(f);
                try {
                    c.check(m, JdkModels.parse(f, mid(m) + " : observe 0"));
                } catch (Throwable x) {
                    out.add(mid(m) + ": CHECKER-ERROR " + x);
                    continue;
                }
                for (String x : c.repCached) {
                    out.add(mid(m) + " | " + x);
                }
            }
        }
        return out;
    }

    /**
     * Tooling (no assertion; runs only with {@code -Dc92.jdkmodel.propose=<class>,<class>...}): for every declared
     * method of the classes, the checker's observed effects written as a proposed table entry (and its violations), to
     * write a family's table from the builder JDK's bytecode. A proposal is reviewed by hand before it enters a table,
     * where the other tests check it.
     */
    @Test
    public void proposeEntries() {
        String classes = System.getProperty("c92.jdkmodel.propose");
        if (classes == null) {
            return;
        }
        JdkModels.Family f = JdkModels.FAMILIES.stream().filter(x -> x.id.equals(System.getProperty("c92.jdkmodel.family", "f1"))).findFirst().orElseThrow();
        for (String cn : classes.split(",")) {
            ResolvedJavaType t = type(cn);
            List<ResolvedJavaMethod> ms = new ArrayList<>(List.of(t.getDeclaredConstructors(false)));
            ms.addAll(List.of(t.getDeclaredMethods(false)));
            for (ResolvedJavaMethod m : ms) {
                if (m.isStatic() && !m.isPublic() || m.getCode() == null || Set.of("readObject", "writeObject", "internalWriteEntries").contains(m.getName())) {
                    continue; // serialization is deferred (never proposed; its walk is large)
                }
                String id = mid(m);
                Result r;
                try {
                    r = new Checker(f).check(m, JdkModels.parse(f, id + (System.getProperty("c92.jdkmodel.propose.ir0") != null && !m.isStatic() ? " : ir 0" : " : observe 0")));
                } catch (Throwable x) {
                    System.out.println("[jdkmodel-propose] " + id + " : CHECKER-ERROR " + x);
                    continue;
                }
                System.out.println("[jdkmodel-propose] " + id + " : " + proposal(m, r) + (r.violations.isEmpty() ? "" : "   VIOLATIONS " + r.violations));
            }
        }
    }

    /** The observed effects in the table syntax (see {@link #proposeEntries}). */
    private static String proposal(ResolvedJavaMethod m, Result r) {
        List<String> eff = new ArrayList<>();
        Map<String, List<String>> calls = new java.util.LinkedHashMap<>();
        Set<String> bound = new HashSet<>();
        for (String o : r.observed) {
            if (o.startsWith("call ")) {
                int at = o.lastIndexOf(" @ ");
                String sig = o.substring(5, at);
                calls.computeIfAbsent(sig, k -> new ArrayList<>()).add(o.substring(at + 3));
            }
        }
        for (String o : r.observed) {
            if (o.startsWith("result C:")) {
                bound.add(noSite(o.substring(9)));
            } else if (o.startsWith("store ")) {
                for (String v : o.split(" ")) {
                    if (v.startsWith("C:")) {
                        bound.add(noSite(v.substring(2).replace(".[]", "")));
                    }
                }
            }
        }
        for (Map.Entry<String, List<String>> c : calls.entrySet()) {
            String[] w = c.getKey().split(" on ");
            String cb = w[0];
            String[] ops = w[1].split(" ");
            StringBuilder sb = new StringBuilder("call ").append(ref(ops[0])).append(' ').append(cb);
            for (int i = 1; i < ops.length; i++) {
                sb.append(' ').append(ops[i].equals("_") ? "_" : ref(ops[i]));
            }
            if (bound.contains(cb)) {
                sb.append(r.observed.stream().anyMatch(x -> x.startsWith("result C:" + cb + "@")) ? " -> result" : " -> $");
            }
            for (String site : c.getValue()) {
                sb.append(" @ ").append(site);
            }
            eff.add(sb.toString());
        }
        for (String o : r.observed) {
            if (o.startsWith("result N:")) {
                eff.add("fresh " + o.substring(9));
            } else if (o.startsWith("result C:")) {
                continue;
            } else if (o.startsWith("result ")) {
                eff.add("alias " + ref(o.substring(7)));
            } else if (o.startsWith("store ")) {
                String[] w = o.substring(6).split(" ");
                // a NEW object that is not the result is a FRESH temp ("$N:<class>": the generator numbers it)
                String owner = !w[0].startsWith("N:") || r.observed.contains("result " + w[0]) ? "R" : "$" + w[0];
                if (!w[0].startsWith("N:")) {
                    String rf = ref(w[0]);
                    int dot = rf.indexOf('.');
                    owner = dot < 0 ? rf : rf.substring(0, dot) + " " + String.join(" ", rf.substring(dot + 1).split("/"));
                }
                eff.add("store " + owner + " " + w[1] + " " + ref(w[3]));
            }
        }
        // the class checks of an explicit family, with their sites
        Map<String, List<String>> checks = new java.util.LinkedHashMap<>();
        for (String o : r.observed) {
            if (o.startsWith("classcheck ") && o.contains(" @ ")) {
                checks.computeIfAbsent(o.substring(11, o.indexOf(" @ ")), k -> new ArrayList<>()).add(o.substring(o.indexOf(" @ ") + 3));
            }
        }
        for (Map.Entry<String, List<String>> c : checks.entrySet()) {
            eff.add("classcheck " + (c.getKey().startsWith("N:") ? c.getKey() : ref(c.getKey())) + c.getValue().stream().map(x -> " @ " + x).reduce("", String::concat));
        }
        int n = m.getSignature().getParameterCount(!m.isStatic());
        for (int k = 0; k < n; k++) {
            JavaKind kind = k == 0 && !m.isStatic() ? JavaKind.Object : m.getSignature().getParameterKind(k - (m.isStatic() ? 0 : 1));
            final String a = "A" + k;
            if (kind == JavaKind.Object && r.observed.stream().noneMatch(o -> o.matches(".*\\b" + a + "\\b.*"))) {
                eff.add("observe " + k);
            }
        }
        return String.join(" ; ", eff);
    }

    /** A callback result label's callback (the label carries its site, {@code C:<cid>@<site>}; a cid has no '@'). */
    private static String noSite(String cidAtSite) {
        int at = cidAtSite.indexOf('@');
        return at < 0 ? cidAtSite : cidAtSite.substring(0, at);
    }

    /** A checker label as a table operand: A1 -> 1, E<s>:A0 -> 0.<s>, A0{C.f} -> 0.C.f, E<s>:A0{C.f} -> 0.C.f/<s>, A0{C.f}.[] -> 0.C.f/[], C:.. -> $. */
    private static String ref(String l) {
        if (l.startsWith("C:") && System.getProperty("c92.jdkmodel.propose.temps") != null) {
            // Tooling: the callback result's identity, "$[cid@site]" (a generator numbers the temps)
            String b = l.endsWith(".[]") ? l.substring(2, l.length() - 3) : l.substring(2);
            return "$[" + b + "]" + (l.endsWith(".[]") ? ".[]" : "");
        }
        if (l.startsWith("C:")) {
            return l.endsWith(".[]") ? "$.[]" : "$";
        }
        if (l.startsWith("N:")) {
            return "$" + l; // a FRESH object (an entry handed to a callback): its temp is written by hand
        }
        if (l.startsWith("E<") && l.substring(l.indexOf(">:") + 2).startsWith("E<")) {
            // a slot value of a slot value (an entry's map's keys: E<keys>:E<map>:A0 -> 0.<map>/<keys>)
            String inner = ref(l.substring(l.indexOf(">:") + 2));
            return inner + (inner.contains(".") ? "/" : ".") + l.substring(1, l.indexOf(">:") + 1);
        }
        boolean elem = l.startsWith("E<");
        String slot = elem ? l.substring(1, l.indexOf(">:") + 1) : null;
        String x = elem ? l.substring(l.indexOf(">:") + 2) : l;
        boolean arr = x.endsWith(".[]");
        if (arr) {
            x = x.substring(0, x.length() - 3);
        }
        StringBuilder sb = new StringBuilder(x.substring(1, x.indexOf('{') < 0 ? x.length() : x.indexOf('{')));
        List<String> ms = new ArrayList<>();
        java.util.regex.Matcher mm = java.util.regex.Pattern.compile("\\{([^}]+)\\}").matcher(x);
        while (mm.find()) {
            ms.add(mm.group(1));
        }
        if (elem) {
            ms.add(slot);
        }
        if (arr) {
            ms.add("[]");
        }
        for (int i = 0; i < ms.size(); i++) {
            sb.append(i == 0 ? '.' : '/').append(ms.get(i));
        }
        return sb.toString();
    }

    /** The checker catches a dropped effect of a real entry (table mutations) and what the premise excludes (controls). */
    @Test
    public void checkerCatchesWhatThePremiseExcludes() throws Exception {
        // real F7 entries with an effect dropped or wrong: the observed effect is uncovered
        String o = "Ljava/lang/Object;";
        assertCaught(JdkModels.F7, "java.util.Objects#equals(" + o + o + ")Z : observe 0 ; observe 1", "equals without its callback");
        String eqSite = " @ java.util.Objects#equals(" + o + o + ")Z@11";
        assertCaught(JdkModels.F7, "java.util.Objects#equals(" + o + o + ")Z : call 1 java.lang.Object#equals(" + o + ")Z 0" + eqSite, "equals with receiver and argument swapped");
        // the site is table data, checked
        assertCaught(JdkModels.F7, "java.util.Objects#equals(" + o + o + ")Z : call 0 java.lang.Object#equals(" + o + ")Z 1 @ java.util.Objects#equals(" + o + o + ")Z@12", "equals at the wrong site");
        assertCaught(JdkModels.F7, "java.util.Objects#toString(" + o + ")Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; -> result @ java.util.Objects#toString(" + o +
                        ")Ljava/lang/String;@1 ; result ir",
                        "toString(o) with the call site of String.valueOf instead of its internal call");
        assertCaught(JdkModels.F7, "java.util.Objects#requireNonNullElse(" + o + o + ")" + o + " : alias 0 ; observe 1", "requireNonNullElse without alias 1");
        assertCaught(JdkModels.F7, "java.util.Objects#requireNonNull(" + o + ")" + o + " : observe 0", "requireNonNull without its alias");
        assertCaught(JdkModels.F7, "java.util.Objects#hashCode(" + o + ")I : observe 0", "hashCode without its callback");
        String tsSite = " @ java.util.Objects#toString(" + o + "Ljava/lang/String;)Ljava/lang/String;@5";
        assertCaught(JdkModels.F7, "java.util.Objects#toString(" + o + "Ljava/lang/String;)Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; -> result" + tsSite,
                        "toString(o, dflt) without alias 1");
        // `result ir` does not excuse a forward result, and an `ir` slot that reaches the result is seen
        assertCaught(JdkModels.F7, "java.util.Objects#toString(" + o + "Ljava/lang/String;)Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; -> result" + tsSite +
                        " ; observe 1 ; result ir", "toString(o, dflt) with observe 1 for alias 1 (result ir)");
        assertCaught(JdkModels.F7, "java.util.Objects#toString(" + o + ")Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; @ java.lang.String#valueOf(" + o +
                        ")Ljava/lang/String;@11",
                        "toString without its result");
        // real F1 entries with an effect of a container kind dropped or wrong (FRESH, COPY, chained STORE, element receiver, temp)
        String al = "java.util.ArrayList";
        String coll = "Ljava/util/Collection;";
        assertCaught(JdkModels.F1, al + "#toArray()[" + o + " : fresh [Ljava.lang.Object;", "toArray without the copy of the elements");
        assertCaught(JdkModels.F1, al + "#toArray([" + o + ")[" + o + " : fresh [Ljava.lang.Object; ; store R [] 0.<elem> ; store 1 [] 0.<elem> ; alias 1", "toArray(a) claiming an exact class");
        assertCaught(JdkModels.F1, al + "#toArray([" + o + ")[" + o + " : fresh ~[Ljava.lang.Object; ; store R [] 0.<elem> ; alias 1", "toArray(a) without the copy into a");
        assertCaught(JdkModels.F1, al + "#iterator()Ljava/util/Iterator; : fresh java.util.ArrayList$Itr", "iterator without its backing list");
        assertCaught(JdkModels.F1, al + "#listIterator()Ljava/util/ListIterator; : fresh java.util.ArrayList$ListItr ; store R java.util.ArrayList$Itr.this$0 0",
                        "listIterator with one of its two this$0 fields");
        assertCaught(JdkModels.F1, al + "#addAll(" + coll + ")Z : call 1 java.util.Collection#toArray()[" + o + " -> $ @ " + al + "#addAll(" + coll + ")Z@1", "addAll without the copy of the temp");
        assertCaught(JdkModels.F1, al + "#<init>(" + coll + ")V : store 0 <elem> 1", "ArrayList(c) storing c instead of c.toArray()'s elements");
        assertCaught(JdkModels.F1, al + "$SubList#set(I" + o + ")" + o + " : store 0 <elem> 2 ; load 0 java.util.ArrayList$SubList.root <elem>", "the sublist's set without the write-through");
        assertCaught(JdkModels.F1, al + "#hashCode()I : call 0 java.lang.Object#hashCode()I @ " + al + "#hashCodeRange(II)I@53", "hashCode on the list instead of each element");
        assertCaught(JdkModels.F1, al + "#replaceAll(Ljava/util/function/UnaryOperator;)V : call 1 java.util.function.UnaryOperator#apply(" + o + ")" + o + " 0.<elem> -> $ @ " + al +
                        "#replaceAllRange(Ljava/util/function/UnaryOperator;II)V@41", "replaceAll without the store of the callback's result");
        assertCaught(JdkModels.F1, "java.util.Stack#push(" + o + ")" + o + " : call 0 java.util.Vector#addElement(" + o + ")V 1 @ java.util.Stack#push(" + o + ")" + o + "@2",
                        "push without its alias");
        assertCaught(JdkModels.F1, al + "$Itr#remove()V : call 0.java.util.ArrayList$Itr.this$0 " + al + "#remove(I)" + o + " _ @ " + al + "$Itr#remove()V@26", "Itr.remove at the wrong site");
        assertCaught(JdkModels.F1, al + "#removeAll(" + coll + ")Z : call 1 java.util.Collection#contains(" + o + ")Z 0.<elem> @ " + al + "#batchRemove(" + coll + "ZII)Z@29",
                        "removeAll with one of its two callback sites");
        // controls on this class, with a representation field `rep` (a fake family: the container effect kinds)
        JdkModels.Family ctl = new JdkModels.Family("ctl-" + System.nanoTime(), false, Set.of(),
                        Map.of(JdkModelPremiseTest.class.getName() + "$Ctl.rep", "<elem>[]", JdkModelPremiseTest.class.getName() + "$Ctl.keys", "<keys>[]"));
        String c = Ctl.class.getName();
        assertCaught(ctl, c + "#setElem(" + o + ")" + o + " : store 0 <elem> 1", "set without its load");
        assertCaught(ctl, c + "#setElem(" + o + ")" + o + " : load 0 <elem> ; observe 1", "set without its store");
        assertPasses(ctl, c + "#setElem(" + o + ")" + o + " : store 0 <elem> 1 ; load 0 <elem>");
        String itr = Ctl.Itr.class.getName();
        assertCaught(ctl, itr + "#next()" + o + " : load 0 <elem>", "next with the wrong chain");
        assertPasses(ctl, itr + "#next()" + o + " : load 0 " + itr + ".this$0 <elem>");
        assertCaught(ctl, c + "#leakRep()[Ljava/lang/Object; : observe 0", "the representation escapes");
        assertCaught(ctl, c + "#storeField(Ljava/lang/Object;)V : observe 0 ; observe 1", "a store into a real field");
        assertCaught(ctl, c + "#storeElem(Ljava/lang/Object;)V : observe 0 ; observe 1", "an undeclared slot store");
        assertCaught(ctl, c + "#callOn(Ljava/lang/Object;)I : observe 0 ; observe 1", "an undeclared callback");
        // a control whose `ir` slot is its result
        assertCaught(ctl, c + "#pick(" + o + o + ")" + o + " : alias 0 ; ir 1", "an ir slot returned without result ir");
        assertPasses(ctl, c + "#pick(" + o + o + ")" + o + " : alias 0 ; ir 1 ; result ir");
        assertCaught(ctl, c + "#throwIt(Ljava/lang/RuntimeException;)V : observe 0 ; observe 1", "a throw");
        assertCaught(ctl, c + "#storeStatic(Ljava/lang/Object;)V : observe 0 ; observe 1", "a static store");
        assertCaught(ctl, c + "#capture(Ljava/lang/Object;)Ljava/lang/Runnable; : observe 0 ; observe 1 ; result ir", "a lambda capture");
        // and the declared forms pass
        assertPasses(ctl, c + "#storeElem(Ljava/lang/Object;)V : observe 0 ; store 0 <elem> 1");
        assertPasses(ctl, c + "#getElem()Ljava/lang/Object; : load 0 <elem>");
        assertPasses(ctl, c + "#callOn(Ljava/lang/Object;)I : observe 0 ; call 1 java.lang.Object#hashCode()I @ " + c + "#callOn(Ljava/lang/Object;)I@1");
        assertCaught(ctl, c + "#findElem(Ljava/lang/Object;)Z : observe 0 ; call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0 @ " + c + "#findElem(Ljava/lang/Object;)Z@7",
                        "an element argument declared as the container");
        assertPasses(ctl, c + "#findElem(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ " + c + "#findElem(Ljava/lang/Object;)Z@7");
        String open = CtlOpen.class.getName();
        assertCaught(ctl, open + "#contains(" + o + ")Z : observe 0 ; observe 1", "contains without its re-dispatch");
        assertPasses(ctl, open + "#contains(" + o + ")Z : call 0 " + open + "#indexOf(" + o + ")I 1 @ " + open + "#contains(" + o + ")Z@2");
        // two callbacks of one method bind two temps; their results are told apart by site
        String sup = "Ljava/util/function/Supplier;";
        String get = "java.util.function.Supplier#get()" + o;
        String two = c + "#twoCalls(" + sup + sup + ")" + o;
        assertPasses(ctl, two + " : call 1 " + get + " -> $ @ " + two + "@1 ; call 2 " + get + " -> result @ " + two + "@8 ; store 0 <elem> $");
        assertCaught(ctl, two + " : call 1 " + get + " -> result @ " + two + "@1 ; call 2 " + get + " -> $ @ " + two + "@8 ; store 0 <elem> $", "two temps of one callback method swapped");
        // two slots of one container are two labels
        assertPasses(ctl, c + "#getKey()" + o + " : load 0 <keys>");
        assertCaught(ctl, c + "#getKey()" + o + " : load 0 <elem>", "a load of one slot declared as another slot");
        assertCaught(ctl, c + "#putKey(" + o + ")V : store 0 <elem> 1", "a store into one slot declared as another slot");
        assertPasses(ctl, c + "#putKey(" + o + ")V : store 0 <keys> 1");
        // getClass / an exact instanceof on a value that may be a String is a class check
        assertCaught(ctl, c + "#isStr(" + o + ")Z : observe 0 ; observe 1", "getClass on an argument declared as an observation");
        // (an exact instanceof: of a final class; this JDK's String is `non-sealed`, so `instanceof String` is not exact, as in
        // the engine's StringAtoms row; `instanceof Integer` is)
        assertCaught(ctl, c + "#isInt(" + o + ")Z : observe 0 ; observe 1", "an exact instanceof on an argument declared as an observation");
        assertPasses(ctl, c + "#isStr(" + o + ")Z : observe 0 ; ir 1");
        assertPasses(ctl, c + "#isInt(" + o + ")Z : observe 0 ; ir 1");
        assertPasses(ctl, c + "#isStrOf(" + o + ")Z : observe 0 ; observe 1"); // instanceof String: not exact in this JDK
        assertPasses(ctl, c + "#isList(" + o + ")Z : observe 0 ; observe 1"); // a non-exact instanceof (an interface) stays an observation
        // a package-private java.* method's same-package overrides are walked too
        Checker dq = new Checker(JdkModels.F1);
        JdkModels.Op rm = JdkModels.F1.table.values().stream().filter(x -> x.method().equals("java.util.ArrayDeque$DeqIterator#remove()V")).findFirst().orElseThrow();
        dq.check(method(rm.method()), rm);
        Assert.assertTrue("the checker walks the same-package override DescendingIterator.postDelete: " + dq.followed, dq.followed.contains("java.util.ArrayDeque$DescendingIterator#postDelete(Z)V"));
        // the abstraction map's completeness scan finds a representation cached in an unabstracted field
        Map<String, String> noSpl = new HashMap<>(JdkModels.F1.abstracted);
        noSpl.remove("java.util.Vector$VectorSpliterator.array");
        List<String> found = cachedRepresentations(new JdkModels.Family("m7-" + System.nanoTime(), false, Set.of(), Map.copyOf(noSpl)));
        Assert.assertTrue("the scan finds VectorSpliterator.array when it is not abstracted: " + found, found.stream().anyMatch(x -> x.contains("java.util.Vector$VectorSpliterator.array")));
    }

    /**
     * F2's premise catches mutated real entries (a dropped callback, a wrong site, a missing class check, a slot
     * confusion, a missing write-through, a missing FRESH entry link or sub-object), and the real entries pass (controls).
     */
    @Test
    public void f2CheckerCatchesTableMutations() {
        JdkModels.Family f = JdkModels.F2;
        String o = "Ljava/lang/Object;";
        String get = "java.util.HashMap#get(" + o + ")" + o;
        String hash = "call 1 java.lang.Object#hashCode()I @ java.util.HashMap#hash(" + o + ")I@9";
        String eq = "call 1 java.lang.Object#equals(" + o + ")Z 0.<keys> @ java.util.HashMap#getNode(" + o + ")Ljava/util/HashMap$Node;@63 @ java.util.HashMap$TreeNode#find(I" + o +
                        "Ljava/lang/Class;)Ljava/util/HashMap$TreeNode;@68 @ java.util.HashMap#getNode(" + o + ")Ljava/util/HashMap$Node;@128";
        String cmp = "call 1 java.lang.Comparable#compareTo(" + o + ")I 0.<keys> @ java.util.HashMap#compareComparables(Ljava/lang/Class;" + o + o + ")I@21";
        String cc = "classcheck 1 @ java.util.HashMap#comparableClassFor(" + o + ")Ljava/lang/Class;@8 ; classcheck 0.<keys> @ java.util.HashMap#compareComparables(Ljava/lang/Class;" + o + o + ")I@5";
        assertF2Passes(get + " : " + String.join(" ; ", hash, eq, cmp, "alias 0.<vals>", cc));
        assertF2Caught(get + " : " + String.join(" ; ", eq, cmp, "alias 0.<vals>", cc), "get without the key's hashCode");
        assertF2Caught(get + " : " + String.join(" ; ", hash, eq.replace("@63", "@62"), cmp, "alias 0.<vals>", cc), "get with an equals site that is not the invoke");
        assertF2Caught(get + " : " + String.join(" ; ", hash, eq, cmp, "alias 0.<vals>", "classcheck 0.<keys> @ java.util.HashMap#compareComparables(Ljava/lang/Class;" + o + o + ")I@5"),
                        "get without the class check of the key (comparableClassFor: a callback on the key does not cover it in F2)");
        assertF2Caught(get + " : " + String.join(" ; ", hash, eq, cmp, "alias 0.<keys>", cc), "get returning the keys instead of the values");
        assertF2Caught(get + " : " + String.join(" ; ", hash, eq.replace(" 0.<keys> @", " 0.<vals> @"), cmp, "alias 0.<vals>", cc), "get comparing the key with the values");
        String node = "java.util.HashMap$Node";
        assertF2Passes(node + "#setValue(" + o + ")" + o + " : store 0 <map> <vals> 1 ; alias 0.<map>/<vals>");
        assertF2Caught(node + "#setValue(" + o + ")" + o + " : store 0 <vals> 1 ; alias 0.<map>/<vals>", "setValue without the write-through to the entry's map");
        assertF2Caught(node + "#getKey()" + o + " : load 0 <keys>", "getKey on the entry's own slot instead of its map's keys");
        String ei = "java.util.HashMap$EntryIterator#next()Ljava/util/Map$Entry;";
        assertF2Passes(ei + " : fresh " + node + " ; store R <map> 0.java.util.HashMap$HashIterator.this$0");
        assertF2Caught(ei + " : fresh " + node, "an entry without its map");
        assertF2Caught("java.util.HashSet#<init>()V : observe 0", "a HashSet without its FRESH map");
        assertF2Caught("java.util.HashMap$KeySet#iterator()Ljava/util/Iterator; : fresh java.util.HashMap$KeyIterator ; store R java.util.HashMap$HashIterator.this$0 0",
                        "the key iterator over the view instead of its map");
        String put = f.table.get("java.util.HashMap#put(" + o + o + ")" + o).toString();
        JdkModels.Op pop = f.table.get("java.util.HashMap#put(" + o + o + ")" + o);
        String effects = pop.effects().stream().map(Object::toString).reduce((x, y) -> x + " ; " + y).orElseThrow();
        assertF2Passes(pop.method() + " : " + effects);
        assertF2Caught(pop.method() + " : " + effects.replace(" ; store 0 <vals> 2", ""), "put without the store of the value");
        assertF2Caught(pop.method() + " : " + effects.replaceAll(" ; call 0 java.util.LinkedHashMap#removeEldestEntry\\(Ljava/util/Map\\$Entry;\\)Z \\$1 @ [^ ]+", ""),
                        "put without LinkedHashMap's removeEldestEntry callback (an eviction hook)");
        Assert.assertNotNull(put);
        // the sorted map: both comparison branches (the comparator field and the Comparable key), a FRESH map's comparator
        JdkModels.Op tget = f.table.get("java.util.TreeMap#get(" + o + ")" + o);
        String tg = tget.effects().stream().map(Object::toString).reduce((x, y) -> x + " ; " + y).orElseThrow();
        assertF2Passes(tget.method() + " : " + tg);
        java.util.function.Function<java.util.function.Predicate<String>, String> without = drop -> tget.effects().stream().map(Object::toString).filter(drop.negate())
                        .reduce((x, y) -> x + " ; " + y).orElseThrow();
        assertF2Caught(tget.method() + " : " + without.apply(e -> e.startsWith("call 0.java.util.TreeMap.comparator ")), "TreeMap.get without the comparator's compare");
        assertF2Caught(tget.method() + " : " + without.apply(e -> e.startsWith("call 1 java.lang.Comparable#compareTo")), "TreeMap.get without the Comparable branch");
        assertF2Passes("java.util.TreeSet#<init>(Ljava/util/Comparator;)V : fresh java.util.TreeMap -> $1 ; store 0 java.util.TreeSet.m $1 ; store $1 java.util.TreeMap.comparator 1");
        assertF2Caught("java.util.TreeSet#<init>(Ljava/util/Comparator;)V : fresh java.util.TreeMap -> $1 ; store 0 java.util.TreeSet.m $1 ; observe 1",
                        "a TreeSet whose FRESH map lacks the comparator");
    }

    /** Every class check's site holds a class check at its bci (getClass, an instanceof or a checkcast). */
    @Test
    public void everyClassCheckSiteIsARealCheck() {
        int n = 0;
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (JdkModels.Op op : f.table.values()) {
                for (JdkModels.Effect e : op.effects()) {
                    if (!(e instanceof JdkModels.ClassCheck cc)) {
                        continue;
                    }
                    for (String site : cc.sites()) {
                        ResolvedJavaMethod m = method(JdkModels.Effect.siteMethod(site));
                        BytecodeStream bs = new BytecodeStream(m.getCode());
                        bs.setBCI(JdkModels.Effect.siteBci(site));
                        int bc = bs.currentBC();
                        boolean ok = bc == Bytecodes.INSTANCEOF || bc == Bytecodes.CHECKCAST ||
                                        bc == Bytecodes.INVOKEVIRTUAL && nameDesc(m.getConstantPool().lookupMethod(bs.readCPI(), bc, m)).equals("getClass()Ljava/lang/Class;");
                        Assert.assertTrue(op.method() + ": the class check site " + site + " is a class check (" + Bytecodes.nameOf(bc) + ")", ok);
                        n++;
                    }
                }
            }
        }
        Assert.assertTrue("class check sites checked", n > 0);
    }

    /**
     * The view caches hold FRESH views only: every class that references a view cache is reviewed (its accesses
     * store the view its own method makes, or reset the cache).
     */
    @Test
    public void viewCachesHoldOnlyViews() throws Exception {
        String ownViews = "not a HashMap: its own view methods store their own views into its own instances' caches, which never reach an F2 entry";
        Map<String, String> reviewed = Map.of(
                        "java.util.AbstractMap", "the templates keySet() / values() store the view they make (a class that does not override them is walked as IR, consistently); clone() resets both",
                        "java.util.HashMap", "keySet() / values() / entrySet() store the FRESH view of the entry that reads them (premise-checked); reinitialize() / clone paths reset them",
                        "java.util.LinkedHashMap", "keySet() / values() / entrySet() store the FRESH linked views (premise-checked)",
                        "java.util.EnumMap", ownViews, "java.util.IdentityHashMap", ownViews, "java.util.WeakHashMap", ownViews, "java.util.TreeMap", ownViews);
        Map<String, Set<String>> refs = fieldReferences();
        List<String> unreviewed = new ArrayList<>();
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            for (String id : f.viewCaches) {
                Set<String> users = fieldUsers(refs, id);
                Assert.assertFalse(id + " is referenced", users.isEmpty());
                for (String u : users) {
                    if (!reviewed.containsKey(u)) {
                        unreviewed.add(id + " <- " + u);
                    }
                }
                System.out.println("[jdkmodel-premise] view cache " + id + " referenced by " + users);
            }
        }
        Assert.assertTrue("view caches referenced by unreviewed classes: " + unreviewed, unreviewed.isEmpty());
    }

    /** The violations of a check that are not reviewed ({@link #REVIEWED_VIOLATIONS}). */
    private static List<String> unreviewed(Result r) {
        return r.violations.stream().filter(v -> REVIEWED_VIOLATIONS.keySet().stream().noneMatch(v::startsWith)).toList();
    }

    /**
     * F6's premise (the string-sink rules: String calls observed, the exact internal writer walked, a call on the
     * {@code ir} receiver that passes the string observed, the record's components as slots) catches mutated real entries,
     * and the real entries pass (the controls).
     */
    @Test
    public void f6CheckerCatchesTableMutations() {
        String psStr = "java.io.PrintStream#print(Ljava/lang/String;)V";
        String plStr = "java.io.PrintStream#println(Ljava/lang/String;)V";
        String plObj = "java.io.PrintStream#println(Ljava/lang/Object;)V";
        String valueOf = "java.lang.String#valueOf(Ljava/lang/Object;)Ljava/lang/String;";
        String ctor = "java.util.stream.Collectors$CollectorImpl#<init>(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BinaryOperator;Ljava/util/function/Function;Ljava/util/Set;)V";
        String supplier = "java.util.stream.Collectors$CollectorImpl#supplier()Ljava/util/function/Supplier;";
        String asb = "java.lang.AbstractStringBuilder#append(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder;";
        String pwPrint = "java.io.PrintWriter#print(Ljava/lang/String;)V";
        String wWrite = "java.io.Writer#write(Ljava/lang/String;)V";
        for (String m : List.of(psStr, plStr, plObj, valueOf, ctor, supplier, asb, pwPrint, wWrite)) {
            assertPasses(JdkModels.F6, f6Line(m, x -> true, x -> x));
        }
        assertCaught(JdkModels.F6, f6Line(plStr, x -> !x.startsWith("call 0 java.io.PrintStream#print"), x -> x), "println(String) without the subclass path's print(x) re-dispatch");
        assertCaught(JdkModels.F6, f6Line(psStr, x -> !x.contains("#indexOf(I)I"), x -> x), "print(String) without indexOf('\\n') on the print path");
        assertCaught(JdkModels.F6, f6Line(psStr, x -> true, x -> x.replace("@ java.io.BufferedWriter#write(Ljava/lang/String;II)V@68", "@ java.io.Writer#write(Ljava/lang/String;)V@4")),
                        "print(String) with getChars at a wrong site");
        assertCaught(JdkModels.F6, f6Line(plStr, x -> true, x -> x.startsWith("call 1 java.lang.String#valueOf") ? x.replace("call 1 ", "call _ ") : x),
                        "println(String) whose valueOf does not get the string");
        assertCaught(JdkModels.F6, f6Line(plObj, x -> true, x -> x.startsWith("call 0 java.io.PrintStream#print") ? x.replace(" $2 @", " $1 @") : x),
                        "println(Object) re-dispatching the second valueOf's result");
        assertCaught(JdkModels.F6, f6Line(valueOf, x -> !x.startsWith("call 0"), x -> x) + " ; observe 0", "String.valueOf without the toString() callback");
        assertCaught(JdkModels.F6, f6Line(ctor, x -> true, x -> x.equals("store 0 <supplier> 1") ? "store 0 <accumulator> 1" : x), "the record constructor storing the supplier into another slot");
        assertCaught(JdkModels.F6, f6Line(supplier, x -> false, x -> x) + "load 0 <finisher>", "supplier() loading another component");
        assertCaught(JdkModels.F6, f6Line(asb, x -> !x.contains("#getBytes("), x -> x), "AbstractStringBuilder.append(String) without getBytes");
        assertCaught(JdkModels.F6, f6Line(pwPrint, x -> !x.startsWith("call 0 java.io.PrintWriter#write"), x -> x), "PrintWriter.print(String) without the write(String) re-dispatch");
        assertCaught(JdkModels.F6, f6Line(wWrite, x -> !x.contains("#length()I"), x -> x), "Writer.write(String) without length()");
    }

    /** A real F6 entry in the table syntax, its effects filtered and mapped (a mutation; {@code result ir} kept). */
    private static String f6Line(String method, java.util.function.Predicate<String> keep, java.util.function.UnaryOperator<String> map) {
        return familyLine(JdkModels.F6, method, keep, map);
    }

    /** A real entry of family {@code f} rewritten: the effects {@code keep} accepts, each mapped by {@code map}. */
    private static String familyLine(JdkModels.Family f, String method, java.util.function.Predicate<String> keep, java.util.function.UnaryOperator<String> map) {
        JdkModels.Op op = f.table.get(method);
        Assert.assertNotNull("an " + f.id + " entry " + method, op);
        List<String> eff = new ArrayList<>();
        for (JdkModels.Effect e : op.effects()) {
            String x = e.toString();
            if (keep.test(x)) {
                eff.add(map.apply(x));
            }
        }
        if (op.resultIr()) {
            eff.add("result ir");
        }
        return method + " : " + String.join(" ; ", eff);
    }

    private void assertF2Caught(String line, String what) {
        JdkModels.Op op = JdkModels.parse(JdkModels.F2, line);
        Result r = new Checker(JdkModels.F2).check(method(op.method()), op);
        Assert.assertFalse("the checker catches: " + what + " (" + r.observed + ")", unreviewed(r).isEmpty() && r.uncovered(op).isEmpty());
    }

    private void assertF2Passes(String line) {
        JdkModels.Op op = JdkModels.parse(JdkModels.F2, line);
        Result r = new Checker(JdkModels.F2).check(method(op.method()), op);
        Assert.assertTrue("passes: " + line + " " + unreviewed(r) + r.uncovered(op), unreviewed(r).isEmpty() && r.uncovered(op).isEmpty());
    }

    private void assertCaught(JdkModels.Family f, String line, String what) {
        JdkModels.Op op = JdkModels.parse(f, line);
        Result r = new Checker(f).check(method(op.method()), op);
        Assert.assertFalse("the checker catches: " + what + " (" + r.observed + ")", r.violations.isEmpty() && r.uncovered(op).isEmpty());
    }

    private void assertPasses(JdkModels.Family f, String line) {
        JdkModels.Op op = JdkModels.parse(f, line);
        Result r = new Checker(f).check(method(op.method()), op);
        Assert.assertTrue("passes: " + line + " " + r.violations + r.uncovered(op), r.violations.isEmpty() && r.uncovered(op).isEmpty());
    }

    /** The control class (a fake family's representation {@code rep}). */
    static final class Ctl {
        Object[] rep = new Object[1];
        /** A second representation field (slot {@code <keys>}). */
        Object[] keys = new Object[1];
        Object other;
        static Object sink;

        /** Two callbacks of one method, their results bound to two temps. */
        Object twoCalls(java.util.function.Supplier<Object> a, java.util.function.Supplier<Object> b) {
            Object x = a.get();
            Object y = b.get();
            rep[0] = x;
            return y;
        }

        Object getKey() {
            return keys[0];
        }

        void putKey(Object k) {
            keys[0] = k;
        }

        /** A class check on the argument. */
        boolean isStr(Object o) {
            return o.getClass() == String.class;
        }

        boolean isStrOf(Object o) {
            return o instanceof String;
        }

        boolean isInt(Object o) {
            return o instanceof Integer;
        }

        boolean isList(Object o) {
            return o instanceof List;
        }

        Object setElem(Object o) {
            Object old = rep[0];
            rep[0] = o;
            return old;
        }

        /** An inner iterator: reads the list's representation through {@code this$0} (the chained load). */
        final class Itr {
            Object next() {
                return rep[0];
            }
        }

        Object[] leakRep() {
            return rep;
        }

        void storeField(Object o) {
            other = o;
        }

        void storeElem(Object o) {
            rep[0] = o;
        }

        Object getElem() {
            return rep[0];
        }

        int callOn(Object o) {
            return o.hashCode();
        }

        /** Declared {@code alias 0 ; ir 1}, it returns its {@code ir} slot. */
        static Object pick(Object a, Object b) {
            return b;
        }

        boolean findElem(Object o) {
            return o.equals(rep[0]);
        }

        void throwIt(RuntimeException e) {
            throw e;
        }

        void storeStatic(Object o) {
            sink = o;
        }

        Runnable capture(Object o) {
            return () -> System.out.println(o);
        }
    }

    /** An open class: {@code contains} is a template whose {@code indexOf} a subclass may override (a callback on this). */
    public static class CtlOpen {
        public int indexOf(Object o) {
            return o == null ? -1 : 0;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }
    }

    // ------------------------------------------------------------------
    // The java.base constant-pool scan (Fieldref users of each field)
    // ------------------------------------------------------------------
    private static Map<String, Set<String>> fieldRefs;
    private static final Map<String, List<String>> packageClasses = new HashMap<>();

    /** The classes of a java.base package (a jrt listing, cached). */
    static synchronized List<String> packageClasses(String pkg) {
        return packageClasses.computeIfAbsent(pkg, k -> {
            List<String> out = new ArrayList<>();
            try {
                FileSystem jrt = FileSystems.getFileSystem(URI.create("jrt:/"));
                Path dir = jrt.getPath("/modules/java.base/" + pkg.replace('.', '/'));
                if (Files.isDirectory(dir)) {
                    try (Stream<Path> files = Files.list(dir)) {
                        files.map(x -> x.getFileName().toString()).filter(n -> n.endsWith(".class") && !n.equals("module-info.class") && !n.equals("package-info.class"))
                                        .sorted().forEach(n -> out.add(pkg + "." + n.substring(0, n.length() - ".class".length())));
                    }
                }
            } catch (Exception e) {
                throw new AssertionError("the java.base listing of " + pkg, e);
            }
            return out;
        });
    }

    private static synchronized Map<String, Set<String>> fieldReferences() throws Exception {
        if (fieldRefs != null) {
            return fieldRefs;
        }
        Map<String, Set<String>> out = new HashMap<>();
        FileSystem jrt = FileSystems.getFileSystem(URI.create("jrt:/"));
        Path base = jrt.getPath("/modules/java.base");
        try (Stream<Path> files = Files.walk(base)) {
            for (Path p : (Iterable<Path>) files::iterator) {
                if (!p.toString().endsWith(".class")) {
                    continue;
                }
                String cls = base.relativize(p).toString().replace('/', '.').replaceAll("\\.class$", "");
                for (String ref : JdkModelClassScan.fieldrefs(Files.readAllBytes(p))) {
                    out.computeIfAbsent(ref, k -> new TreeSet<>()).add(cls);
                }
            }
        }
        fieldRefs = out;
        return out;
    }

    // ------------------------------------------------------------------
    // The checker
    // ------------------------------------------------------------------

    /** The observed effects of one entry and its violations. */
    static final class Result {
        final Set<String> observed = new LinkedHashSet<>();
        final List<String> violations = new ArrayList<>();

        /** The observed effects no declared effect of {@code op} covers. */
        List<String> uncovered(JdkModels.Op op) {
            Set<String> allowed = allowed(op);
            List<String> out = new ArrayList<>();
            for (String o : observed) {
                // `result ir` states only an `ir` slot's result (the engine applies it backward only); every
                // other observed result must be declared (forward, the result flows only through the declared effects)
                if (!allowed.contains(o) && !(op.resultIr() && (o.matches("result I\\d+") || o.startsWith("result N:")))) {
                    out.add(op.method() + ": undeclared effect `" + o + "`");
                }
            }
            return out;
        }

        /** The effects the entry declares, in the checker's vocabulary. */
        static Set<String> allowed(JdkModels.Op op) {
            return allowed(op, Result::labels);
        }

        /** {@link #allowed(JdkModels.Op)} over a labeller (the lazy premise expands a FRESH temp's slot into its stores). */
        static Set<String> allowed(JdkModels.Op op, java.util.function.BiFunction<JdkModels.Op, JdkModels.Ref, List<String>> labels) {
            Set<String> allowed = new HashSet<>();
            for (JdkModels.Effect ef : op.effects()) {
                switch (ef) {
                    case JdkModels.Alias e -> labels.apply(op, e.a()).forEach(l -> allowed.add("result " + l));
                    case JdkModels.Store e -> {
                        for (String a : labels.apply(op, e.a())) {
                            for (String v : labels.apply(op, e.v())) {
                                allowed.add("store " + a + " " + memberName(e.member()) + " <- " + v);
                            }
                        }
                    }
                    case JdkModels.Fresh e -> {
                        if (e.bind() == JdkModels.BIND_RESULT) {
                            allowed.add("result N:" + freshLabel(e));
                        }
                    }
                    case JdkModels.Callback e -> {
                        // every combination of the operands' labels (a temp has one label per site of its binder)
                        List<String> prefixes = new ArrayList<>();
                        for (String recv : labels.apply(op, e.a())) {
                            prefixes.add("call " + e.cb() + " on " + recv);
                        }
                        for (JdkModels.Ref r : e.cbArgs()) {
                            List<String> next = new ArrayList<>();
                            for (String pre : prefixes) {
                                for (String l : r.slot() == JdkModels.Ref.NONE ? List.of("_") : labels.apply(op, r)) {
                                    next.add(pre + " " + l);
                                }
                            }
                            prefixes = next;
                        }
                        for (String site : e.sites()) {
                            for (String pre : prefixes) {
                                allowed.add(pre + " @ " + site); // the site is checked too
                            }
                            if (e.bind() == JdkModels.BIND_RESULT) {
                                allowed.add("result C:" + e.cb() + "@" + site); // the result of this callback, at its site
                            }
                        }
                    }
                    case JdkModels.Observe e -> {
                    }
                    case JdkModels.Ir e -> {
                    }
                    case JdkModels.Unmodelled e -> {
                    }
                    case JdkModels.ClassCheck e -> {
                        // a declared class check (with its sites: an explicit family's observations carry them)
                        for (String l : labels.apply(op, e.a())) {
                            allowed.add("classcheck " + l);
                            for (String site : e.sites()) {
                                allowed.add("classcheck " + l + " @ " + site);
                            }
                        }
                    }
                }
            }
            return allowed;
        }

        static String freshLabel(JdkModels.Fresh fe) {
            return (fe.exact() ? "" : "~") + fe.fresh();
        }

        /**
         * A table operand in the checker's labels: A<k>, N:<class>, C:<cb>@<site>, then {field}, E<slot>: (a value of the
         * slot, the slot is part of the label), .[] (an array element). A temp {@code $k} has one label per site of
         * its binder (an observed callback result is labelled by its call site, so two temps of one callback
         * method are not confused).
         */
        static List<String> labels(JdkModels.Op op, JdkModels.Ref r) {
            List<String> bases = new ArrayList<>();
            if (r.slot() == JdkModels.Ref.SINK) {
                bases.add("S"); // the op's sink (the lazy premise's label of what the JDK hands to a consumer it passes on)
            } else if (r.slot() == JdkModels.Ref.RESULT) {
                JdkModels.Fresh fe = op.fresh();
                bases.add("N:" + (fe == null ? "?" : freshLabel(fe)));
            } else if (JdkModels.Ref.isTemp(r.slot())) {
                JdkModels.Effect b = op.tempBinder(JdkModels.Ref.tempIndex(r.slot()));
                if (b instanceof JdkModels.Callback cb) {
                    for (String site : cb.sites()) {
                        bases.add("C:" + cb.cb() + "@" + site);
                    }
                } else if (b instanceof JdkModels.Fresh fr) {
                    bases.add("N:" + freshLabel(fr)); // a FRESH temp is a NEW object of the op
                } else {
                    bases.add("C:?");
                }
            } else if (r.slot() == JdkModels.Ref.NONE) {
                return List.of("_"); // a static callback's untracked first argument
            } else if (op.effects().stream().anyMatch(e -> e instanceof JdkModels.Ir ir && ir.a().slot() == r.slot())) {
                return List.of("I" + r.slot()); // an ir slot (seeded I<k>; its fields are ir values too)
            } else {
                bases.add("A" + r.slot());
            }
            List<String> out = new ArrayList<>();
            for (String s : bases) {
                for (String m : r.members()) {
                    if (JdkModels.slot(m) != null) {
                        s = "E" + m + ":" + s;
                    } else if (m.equals("[]")) {
                        s = s + ".[]";
                    } else {
                        s = s + "{" + m + "}";
                    }
                }
                out.add(s);
            }
            return out;
        }

        static String memberName(String m) {
            return m; // a slot, [] or a qualified field "Class.field"
        }
    }

    /** A NEW node or array linked into {@code owner}'s representation (an array: of slot {@code slot}; a node: null). */
    record Joined(String owner, String slot) {
    }

    /** One abstract frame: a label set per local and per operand-stack word. */
    static final class Frame {
        final List<Set<String>> locals;
        final List<Set<String>> stack;

        Frame(List<Set<String>> locals, List<Set<String>> stack) {
            this.locals = locals;
            this.stack = stack;
        }

        Frame copy() {
            List<Set<String>> l = new ArrayList<>();
            for (Set<String> s : locals) {
                l.add(new TreeSet<>(s));
            }
            List<Set<String>> st = new ArrayList<>();
            for (Set<String> s : stack) {
                st.add(new TreeSet<>(s));
            }
            return new Frame(l, st);
        }

        void push(Set<String> s) {
            stack.add(new TreeSet<>(s));
        }

        void pushWords(int n) {
            for (int i = 0; i < n; i++) {
                stack.add(new TreeSet<>());
            }
        }

        Set<String> pop() {
            Assert.assertFalse("operand stack underflow", stack.isEmpty());
            return stack.remove(stack.size() - 1);
        }

        Set<String> pop(int n) {
            Set<String> all = new TreeSet<>();
            for (int i = 0; i < n; i++) {
                all.addAll(pop());
            }
            return all;
        }

        void dup(int n, int below) {
            List<Set<String>> top = new ArrayList<>();
            for (Set<String> s : stack.subList(stack.size() - n, stack.size())) {
                top.add(new TreeSet<>(s));
            }
            stack.addAll(stack.size() - n - below, top);
        }
    }

    /**
     * The generic premise checker for one family. Labels, besides {@code A<i>}, {@code A<i>.f}, {@code R:<p>},
     * {@code E:<p>}, {@code C:<sig>}, {@code I<k>}: {@code N:<class>} (a NEW object or array of the entry: its field and
     * element stores are pending until the end: they are the FRESH result's initial stores if it is returned, a node
     * representation's element stores if it is linked into one, else a violation), {@code K=:<elem>} /
     * {@code K~:<elem>} (a copy of an array whose elements are {@code <elem>}: {@code Arrays.copyOf} without / with a
     * class argument, i.e. an exact or an inexact class), {@code C:<sig>.[]} / {@code A<i>.[]} (an element of a callback's
     * or an argument's array).
     */
    class Checker {
        final JdkModels.Family family;
        /**
         * The lazy premise's checker ({@link LazyChecker}): a NEW object's stores need not end in the result or a
         * representation (the composition's sinks and terminal ops are the JDK's internal objects of one evaluation; an
         * escape of one to user code is still recorded), and a NEW object stored into a NEW object is a pending store.
         */
        boolean lazyMode;
        final Result result = new Result();
        /** The methods walked (their code must be the image's). */
        final Set<String> followed = new TreeSet<>();
        private final Set<String> inProgress = new HashSet<>();
        private int depth;
        /** The pending stores into NEW objects (N label -> observations), their links into a node representation, their escapes. */
        final Map<String, Set<String>> pendingN = new HashMap<>();
        private final Map<String, Set<Joined>> joinedN = new HashMap<>();
        final List<String[]> escapedN = new ArrayList<>();
        /** Where the representation leaves the abstracted fields (an unabstracted field, a static, a return, a call, a capture). */
        final List<String> repCached = new ArrayList<>();
        /** NEW objects held in a real field of an argument or of a NEW object (their stores are that object's state). */
        final Set<String> heldN = new HashSet<>();
        /** The links of NEW nodes ("N:<class> <field>" -> the linked NEW nodes / representation nodes). */
        final Map<String, Set<String>> nodeLinks = new HashMap<>();
        /** The NEW views this walk stored into a view cache (by the cache's field). */
        final Map<String, Set<String>> cacheStores = new HashMap<>();

        /** The entry being checked (its parameter types). */
        ResolvedJavaMethod entry;

        Checker(JdkModels.Family family) {
            this.family = family;
        }

        Result check(ResolvedJavaMethod m, JdkModels.Op op) {
            entry = m;
            Set<Integer> irSlots = new HashSet<>();
            for (JdkModels.Effect e : op.effects()) {
                if (e instanceof JdkModels.Ir ir) {
                    irSlots.add(ir.a().slot());
                }
            }
            List<Set<String>> args = new ArrayList<>();
            int n = m.getSignature().getParameterCount(!m.isStatic());
            for (int i = 0; i < n; i++) {
                args.add(Set.of((irSlots.contains(i) ? "I" : "A") + i)); // an ir slot is seeded as I<k>
            }
            if (!m.isStatic() && !irSlots.contains(0) && family.entryClasses.containsValue(m.getDeclaringClass().toJavaName())) {
                // a method of a Map.Entry node class runs on a node of some map's representation: the receiver is
                // that node (R:), its owner the entry's map (E<map>:A0), so its key / value fields are that map's slots
                args.set(0, Set.of("R:" + eLabel("<map>", "A0")));
            }
            Set<String> ret = afterWalk(m, op, walk(m, args));
            Set<String> returnedN = new HashSet<>();
            for (String l : ret) {
                String entryL = entryLabel(l);
                if (entryL != null) {
                    // a node of the representation returned = a FRESH entry of its map (Map.Entry)
                    result.observed.add("result " + entryL);
                    result.observed.add("store " + entryL + " <map> <- " + owner(l));
                    continue;
                }
                if (isR(l)) {
                    result.violations.add(mid(m) + ": the representation is returned (" + l + ")");
                    if (!m.isPrivate()) {
                        repCached.add(mid(m) + ": the representation is returned (" + l + ")");
                    }
                } else if (l.startsWith("N:")) {
                    returnedN.add(l);
                    result.observed.add("result " + l);
                    result.observed.addAll(pendingN.getOrDefault(l, Set.of()));
                } else if (l.startsWith("K")) {
                    String fresh = "N:" + (l.startsWith("K~") ? "~" : "") + "[Ljava.lang.Object;";
                    result.observed.add("result " + fresh);
                    result.observed.add("store " + fresh + " [] <- " + l.substring(3));
                } else {
                    result.observed.add("result " + l);
                }
            }
            // a NEW node array joined into a node representation (a resized table) makes the NEW nodes stored into it
            // part of that representation too (transitively)
            for (boolean changed = true; changed;) {
                changed = false;
                for (Map.Entry<String, Set<Joined>> j : new ArrayList<>(joinedN.entrySet())) {
                    for (Joined o : new ArrayList<>(j.getValue())) {
                        if (o.slot() != null) {
                            continue;
                        }
                        for (String obs : pendingN.getOrDefault(j.getKey(), Set.of())) {
                            String pre = "store " + j.getKey() + " [] <- ";
                            if (obs.startsWith(pre) && obs.substring(pre.length()).startsWith("N:")) {
                                changed |= joinedN.computeIfAbsent(obs.substring(pre.length()), k -> new LinkedHashSet<>()).add(o);
                            }
                        }
                        for (Map.Entry<String, Set<String>> link : nodeLinks.entrySet()) {
                            if (link.getKey().startsWith(j.getKey() + " ")) {
                                for (String x : link.getValue()) {
                                    if (x.startsWith("N:")) {
                                        changed |= joinedN.computeIfAbsent(x, k -> new LinkedHashSet<>()).add(o);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for (Map.Entry<String, Set<String>> p : pendingN.entrySet()) {
                if (returnedN.contains(p.getKey()) || p.getValue().isEmpty()) {
                    continue;
                }
                if (heldN.contains(p.getKey())) {
                    result.observed.addAll(p.getValue()); // a NEW object held in a real field: its initial stores are observed
                    continue;
                }
                Set<Joined> owners = joinedN.getOrDefault(p.getKey(), Set.of());
                if (owners.isEmpty()) {
                    if (lazyMode) {
                        continue; // an internal object of the evaluation (its escapes are checked below)
                    }
                    result.violations.add(mid(m) + ": tracked values stored into a NEW object that is neither the result nor linked into a representation: " + p);
                    continue;
                }
                for (Joined j : owners) {
                    String o = j.owner();
                    for (String obs : p.getValue()) {
                        if (obs.matches(".* <- E<[^>]+>:" + java.util.regex.Pattern.quote(o))) {
                            continue; // an element of the same representation moved into its new array / node (a shift)
                        }
                        if (j.slot() == null && (obs.endsWith(" <- R:" + o) || obs.matches("store " + java.util.regex.Pattern.quote(p.getKey()) + " \\[\\] <- N:.*"))) {
                            continue; // a node of the same representation (or a NEW node joined with it) moved into its new node array
                        }
                        // "store N:<node> <s> <- v" / "store N:<array> [] <- v": the node / array joined o's representation
                        // (an array joins as the representation of slot s: its elements are the slot's values)
                        String x = j.slot() == null ? obs : obs.replace("store " + p.getKey() + " [] ", "store " + o + " " + j.slot() + " ");
                        result.observed.add(x.replace("store " + p.getKey() + " ", "store " + o + " "));
                    }
                }
            }
            for (String[] esc : escapedN) {
                if (!pendingN.getOrDefault(esc[0], Set.of()).isEmpty()) {
                    result.violations.add(esc[1] + ": a NEW object holding tracked values escapes (" + esc[0] + ")");
                }
            }
            return result;
        }

        /** The lazy premise: the result labels after the entry's walk (the eager checker: unchanged). */
        Set<String> afterWalk(ResolvedJavaMethod m, JdkModels.Op op, Set<String> ret) {
            return ret;
        }

        /** The lazy premise: a call's result labels, when the lazy composition handles the call (the eager checker: never, null). */
        Set<String> lazyInvoke(ResolvedJavaMethod m, BytecodeStream s, String at, int bc, JavaMethod callee, String cid, int rawIndex, List<Set<String>> args) {
            return null;
        }

        /** The lazy premise: the labels of a static field's value (the eager checker: untracked, null). */
        Set<String> lazyStatic(JavaField fld) {
            return null;
        }

        /** The lazy premise: a store into a pipeline link, handled (the eager checker: never, false). */
        boolean lazyPut(String at, JavaField fld, Set<String> obj, Set<String> value) {
            return false;
        }

        /** An {@code ir} slot's label (or one derived from it). */
        static boolean ir(String l) {
            return l.startsWith("I");
        }

        /** No label, or only {@code ir} labels: nothing the model states (the IR states it). */
        static boolean irOnly(Set<String> ls) {
            return ls.stream().allMatch(Checker::ir);
        }

        /** The labels without the {@code ir} ones and without NEW objects (their escapes are recorded apart). */
        Set<String> modelled(Set<String> ls, String at) {
            Set<String> out = new TreeSet<>(ls);
            out.removeIf(Checker::ir);
            for (String l : ls) {
                if (l.startsWith("N:")) {
                    escapedN.add(new String[]{l, at});
                }
            }
            out.removeIf(l -> l.startsWith("N:"));
            return out;
        }

        /** An argument, or a (qualified) field chain of it: {@code A<k>}, {@code A<k>{Class.f}}, {@code A<k>{Class.f}{Class.g}}. */
        static final String ARG = "A\\d+(\\{[^}]+\\}){0,2}";

        /** A field's qualified name, as the tables write it ("Class.field"). */
        static String qn(JavaField f) {
            return f.getDeclaringClass().toJavaName() + "." + f.getName();
        }

        /** The representation kind of an abstracted field ("<elem>[]", "<elem>", "-", "-@Class.field"), or null. */
        private String repKind(JavaField f) {
            return family.abstracted.get(f.getDeclaringClass().toJavaName() + "." + f.getName());
        }

        /*
         * The representation labels carry their slot. R<s>:p = an array representation of p whose
         * elements are the slot s (an abstracted "<s>[]" field, or a "-@" link to one); R:p = a node representation of p
         * or a link into it (its slot is the element field's, "<s>"); E<s>:p = a value of p's slot s. So two slots of one
         * container (F2's <keys> and <vals>) are never the same label.
         */
        static boolean isR(String l) {
            return l.startsWith("R:") || l.startsWith("R<");
        }

        static boolean isE(String l) {
            return l.startsWith("E<");
        }

        /** The owner p of R:p, R<s>:p or E<s>:p. */
        static String owner(String l) {
            return l.startsWith("R:") ? l.substring(2) : l.substring(l.indexOf(">:") + 2);
        }

        /** The slot s of R<s>:p or E<s>:p (null for R:p). */
        static String slotOf(String l) {
            return l.startsWith("R:") ? null : l.substring(1, l.indexOf(">:") + 1);
        }

        static String eLabel(String slot, String owner) {
            return "E" + slot + ":" + owner;
        }

        /** The label of an element of array label {@code a} (null: not an array the checker knows). */
        static String elem(String a) {
            if (isR(a)) {
                return slotOf(a) == null ? null : eLabel(slotOf(a), owner(a)); // a node representation is no array
            }
            if (a.startsWith("K")) {
                return a.substring(3);
            }
            if (a.startsWith("C:") && !a.endsWith(".[]") || a.matches(ARG)) {
                return a + ".[]";
            }
            return null;
        }

        /** The rep owner p of a representation array label (R<s>:p, or a copy K..:E<s>:p of it), else null. */
        static String repOwner(String a) {
            if (isR(a)) {
                return owner(a);
            }
            if (a.startsWith("K") && isE(a.substring(3))) {
                return owner(a.substring(3));
            }
            return null;
        }

        /** The slot of {@link #repOwner}'s representation array (null: a node representation). */
        static String repSlot(String a) {
            if (isR(a)) {
                return slotOf(a);
            }
            if (a.startsWith("K") && isE(a.substring(3))) {
                return slotOf(a.substring(3));
            }
            return null;
        }

        /** The label of the representation of {@code o} in an abstracted field of kind {@code kind} (with its slot). */
        private String repLabel(String kind, String o) {
            if (kind.startsWith("-@")) {
                String link = kind.substring(2);
                String s = linkedArraySlot(link);
                return (s == null ? "R:" : "R" + s + ":") + o + "{" + link + "}";
            }
            String s = JdkModels.arrayRepSlot(kind) != null ? kind.substring(0, kind.length() - 2) : null;
            return (s == null ? "R:" : "R" + s + ":") + o;
        }

        /** The slot of the array representation of the object a "-@" link's field holds (null: a node representation). */
        private String linkedArraySlot(String linkField) {
            ResolvedJavaField lf = field(linkField);
            Assert.assertNotNull("the link field exists: " + linkField, lf);
            ResolvedJavaType owner = type(lf.getType().toJavaName());
            Set<String> slots = new TreeSet<>();
            for (Map.Entry<String, String> a : family.abstracted.entrySet()) {
                String cls = a.getKey().substring(0, a.getKey().lastIndexOf('.'));
                if (JdkModels.arrayRepSlot(a.getValue()) != null && type(cls).isAssignableFrom(owner)) {
                    slots.add(a.getValue().substring(0, a.getValue().length() - 2));
                }
            }
            Assert.assertTrue("a link into one array representation: " + linkField + " " + slots, slots.size() <= 1);
            return slots.isEmpty() ? null : slots.iterator().next();
        }

        /** Walks {@code m} with the given argument labels (per argument, not per local word); returns the result labels. */
        Set<String> walk(ResolvedJavaMethod m, List<Set<String>> args) {
            String key = mid(m) + args;
            if (nodeArrays() && inProgress.contains(key)) {
                // a recursive walk over a representation (TreeNode.find, checkInvariants) with the same labels: its
                // observations are the enclosing walk's; its result is the method's summary so far (iterated to a fixpoint)
                recursed.add(key);
                return new TreeSet<>(summaries.getOrDefault(key, Set.of()));
            }
            if (inProgress.contains(key) || depth > 12) {
                if (args.stream().allMatch(Checker::irOnly)) {
                    // only `ir` values: the IR states their flows; conservatively, the callee may return any of them
                    Set<String> all = new TreeSet<>();
                    args.forEach(all::addAll);
                    return all;
                }
                result.violations.add(mid(m) + ": recursion or depth bound (" + args + ")");
                return Set.of();
            }
            followed.add(mid(m));
            byte[] code = m.getCode();
            if (code == null) {
                result.violations.add(mid(m) + ": no bytecode");
                return Set.of();
            }
            inProgress.add(key);
            depth++;
            Set<String> ret;
            for (int round = 0;; round++) {
                ret = walkBody(m, args, code);
                if (!recursed.remove(key) || ret.equals(summaries.get(key))) {
                    break;
                }
                summaries.put(key, ret);
                if (round > 8) {
                    result.violations.add(mid(m) + ": no recursion fixpoint (" + args + ")");
                    break;
                }
            }
            depth--;
            inProgress.remove(key);
            return ret;
        }

        /** The recursive walks' result summaries (key = method + argument labels) and the keys that recursed. */
        private final Map<String, Set<String>> summaries = new HashMap<>();
        private final Set<String> recursed = new HashSet<>();

        /** One abstract interpretation of {@code m}'s bytecode {@code code} with the argument labels {@code args}. */
        private Set<String> walkBody(ResolvedJavaMethod m, List<Set<String>> args, byte[] code) {
            List<Set<String>> locals = new ArrayList<>();
            for (int i = 0; i < m.getMaxLocals(); i++) {
                locals.add(new TreeSet<>());
            }
            int slot = 0;
            Signature sig = m.getSignature();
            for (int i = 0; i < args.size(); i++) {
                locals.get(slot).addAll(args.get(i));
                boolean recv = !m.isStatic() && i == 0;
                slot += recv ? 1 : sig.getParameterKind(i - (m.isStatic() ? 0 : 1)).getSlotCount();
            }
            Set<String> ret = new TreeSet<>();
            Map<Integer, Frame> states = new HashMap<>();
            ArrayDeque<Integer> work = new ArrayDeque<>();
            states.put(0, new Frame(locals, new ArrayList<>()));
            work.add(0);
            BytecodeStream s = new BytecodeStream(code);
            while (!work.isEmpty()) {
                int bci = work.poll();
                Frame f = states.get(bci).copy();
                s.setBCI(bci);
                for (ExceptionHandler h : m.getExceptionHandlers()) {
                    if (bci >= h.getStartBCI() && bci < h.getEndBCI()) {
                        List<Set<String>> hs = new ArrayList<>();
                        hs.add(new TreeSet<>()); // the caught exception: fresh (a tracked throw is a violation)
                        merge(states, work, h.getHandlerBCI(), new Frame(f.copy().locals, hs));
                    }
                }
                List<Integer> succ;
                try {
                    succ = step(m, s, f, ret);
                } catch (AssertionError x) {
                    throw new AssertionError(mid(m) + "@" + bci + ": " + x.getMessage(), x); // a checker error names its bytecode
                }
                for (int t : succ) {
                    merge(states, work, t, f);
                }
            }
            return ret;
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
            for (int i = 0; i < old.locals.size(); i++) {
                changed |= old.locals.get(i).addAll(f.locals.get(i));
            }
            for (int i = 0; i < old.stack.size(); i++) {
                changed |= old.stack.get(i).addAll(f.stack.get(i));
            }
            if (changed) {
                work.add(bci);
            }
        }

        private List<Integer> step(ResolvedJavaMethod m, BytecodeStream s, Frame f, Set<String> ret) {
            int bc = s.currentBC();
            int bci = s.currentBCI();
            String at = mid(m) + "@" + bci + " " + Bytecodes.nameOf(bc);
            List<Integer> next = List.of(s.nextBCI());
            switch (bc) {
                case Bytecodes.ALOAD -> f.push(f.locals.get(s.readLocalIndex()));
                case Bytecodes.ALOAD_0, Bytecodes.ALOAD_1, Bytecodes.ALOAD_2, Bytecodes.ALOAD_3 -> f.push(f.locals.get(bc - Bytecodes.ALOAD_0));
                case Bytecodes.ASTORE -> f.locals.set(s.readLocalIndex(), f.pop());
                case Bytecodes.ASTORE_0, Bytecodes.ASTORE_1, Bytecodes.ASTORE_2, Bytecodes.ASTORE_3 -> f.locals.set(bc - Bytecodes.ASTORE_0, f.pop());
                case Bytecodes.ISTORE, Bytecodes.FSTORE -> {
                    f.pop();
                    f.locals.set(s.readLocalIndex(), new TreeSet<>());
                }
                case Bytecodes.LSTORE, Bytecodes.DSTORE -> {
                    f.pop(2);
                    f.locals.set(s.readLocalIndex(), new TreeSet<>());
                    f.locals.set(s.readLocalIndex() + 1, new TreeSet<>());
                }
                case Bytecodes.ISTORE_0, Bytecodes.ISTORE_1, Bytecodes.ISTORE_2, Bytecodes.ISTORE_3 -> {
                    f.pop();
                    f.locals.set(bc - Bytecodes.ISTORE_0, new TreeSet<>());
                }
                case Bytecodes.FSTORE_0, Bytecodes.FSTORE_1, Bytecodes.FSTORE_2, Bytecodes.FSTORE_3 -> {
                    f.pop();
                    f.locals.set(bc - Bytecodes.FSTORE_0, new TreeSet<>());
                }
                case Bytecodes.LSTORE_0, Bytecodes.LSTORE_1, Bytecodes.LSTORE_2, Bytecodes.LSTORE_3 -> {
                    f.pop(2);
                    f.locals.set(bc - Bytecodes.LSTORE_0, new TreeSet<>());
                    f.locals.set(bc - Bytecodes.LSTORE_0 + 1, new TreeSet<>());
                }
                case Bytecodes.DSTORE_0, Bytecodes.DSTORE_1, Bytecodes.DSTORE_2, Bytecodes.DSTORE_3 -> {
                    f.pop(2);
                    f.locals.set(bc - Bytecodes.DSTORE_0, new TreeSet<>());
                    f.locals.set(bc - Bytecodes.DSTORE_0 + 1, new TreeSet<>());
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
                    Set<String> a = f.pop();
                    Set<String> b = f.pop();
                    f.push(a);
                    f.push(b);
                }
                case Bytecodes.CHECKCAST -> {
                    // the same reference; an exact type test of a value that may be a user String is a class check
                    if (exactType(m, s, bc)) {
                        classCheck(f.stack.get(f.stack.size() - 1), mid(m) + "@" + bci);
                    }
                }
                case Bytecodes.INSTANCEOF, Bytecodes.ARRAYLENGTH -> {
                    if (bc == Bytecodes.INSTANCEOF && exactType(m, s, bc)) {
                        classCheck(f.stack.get(f.stack.size() - 1), mid(m) + "@" + bci); // StringAtoms: an exact InstanceOf is CLASS_CHECK
                    }
                    f.pop(); // an observation of the reference (or of the representation's length)
                    f.pushWords(1);
                }
                case Bytecodes.MONITORENTER, Bytecodes.MONITOREXIT, Bytecodes.IFNULL, Bytecodes.IFNONNULL -> f.pop();
                case Bytecodes.IF_ACMPEQ, Bytecodes.IF_ACMPNE -> f.pop(2);
                case Bytecodes.ATHROW -> {
                    Set<String> v = modelled(f.pop(), at);
                    if (!v.isEmpty()) {
                        result.violations.add(at + ": a tracked value is thrown " + v);
                    }
                    return List.of();
                }
                case Bytecodes.ARETURN -> {
                    ret.addAll(f.pop());
                    return List.of();
                }
                case Bytecodes.IRETURN, Bytecodes.LRETURN, Bytecodes.FRETURN, Bytecodes.DRETURN, Bytecodes.RETURN -> {
                    return List.of();
                }
                case Bytecodes.AALOAD -> {
                    f.pop();
                    Set<String> arr = f.pop();
                    Set<String> out = new TreeSet<>();
                    for (String l : arr) {
                        String el = elem(l);
                        if (ir(l)) {
                            out.add(l); // an element of an ir value: an ir value
                        } else if (l.startsWith("N:")) {
                            // an element of a NEW array the entry filled: its pending stores (a read-back)
                            for (String p : pendingN.getOrDefault(l, Set.of())) {
                                out.add(p.substring(p.indexOf(" <- ") + 4));
                            }
                        } else if (el != null) {
                            out.add(el); // an element of the representation = a value of the slot; of a copy, a callback's or an argument's array
                        } else if (nodeArrays() && isR(l) && slotOf(l) == null) {
                            out.add(l); // an element of a node array (a hash table) = a node of the representation
                        } else {
                            result.violations.add(at + ": an element of an unmodelled array is read (" + l + ")");
                        }
                    }
                    f.push(out);
                }
                case Bytecodes.IALOAD, Bytecodes.FALOAD, Bytecodes.BALOAD, Bytecodes.CALOAD, Bytecodes.SALOAD, Bytecodes.LALOAD, Bytecodes.DALOAD -> {
                    f.pop(2);
                    f.pushWords(bc == Bytecodes.LALOAD || bc == Bytecodes.DALOAD ? 2 : 1);
                }
                case Bytecodes.AASTORE -> {
                    Set<String> vAll = f.pop();
                    f.pop();
                    Set<String> arrAll = f.pop();
                    Set<String> v = modelledValue(vAll, at);
                    boolean nodeArray = false;
                    if (nodeArrays()) {
                        v = nodeArrayStore(at, arrAll, v); // node arrays (a hash table) and NEW nodes in NEW arrays
                        nodeArray = arrAll.stream().anyMatch(a -> isR(a) && slotOf(a) == null);
                        arrAll = new TreeSet<>(arrAll);
                        arrAll.removeIf(a -> isR(a) && slotOf(a) == null);
                    }
                    if (!v.isEmpty() && !(nodeArray && arrAll.isEmpty())) {
                        storeInto(at, arrAll, v);
                    }
                }
                case Bytecodes.IASTORE, Bytecodes.FASTORE, Bytecodes.BASTORE, Bytecodes.CASTORE, Bytecodes.SASTORE -> f.pop(3);
                case Bytecodes.LASTORE, Bytecodes.DASTORE -> f.pop(4);
                case Bytecodes.GETSTATIC, Bytecodes.PUTSTATIC, Bytecodes.GETFIELD, Bytecodes.PUTFIELD -> {
                    JavaField fld = m.getConstantPool().lookupField(s.readCPI(), m, bc);
                    int words = fld.getJavaKind().getSlotCount();
                    Set<String> value = Set.of();
                    if (bc == Bytecodes.PUTSTATIC || bc == Bytecodes.PUTFIELD) {
                        value = f.pop(words);
                    }
                    Set<String> obj = bc == Bytecodes.GETFIELD || bc == Bytecodes.PUTFIELD ? f.pop() : Set.of();
                    if (bc == Bytecodes.PUTSTATIC && !modelled(value, at).isEmpty()) {
                        result.violations.add(at + ": a tracked value is stored into a static " + value);
                        value.stream().filter(Checker::isR).forEach(l -> repCached.add(at + ": the static " + qn(fld) + " <- " + l));
                    }
                    if (bc == Bytecodes.PUTFIELD) {
                        putField(at, fld, obj, value);
                    }
                    if (bc == Bytecodes.GETSTATIC) {
                        Set<String> st = lazyStatic(fld); // a static terminal op of the lazy premise
                        if (st != null) {
                            f.push(st);
                        } else {
                            f.pushWords(words);
                        }
                    }
                    if (bc == Bytecodes.GETFIELD) {
                        f.push(getField(at, fld, obj));
                        if (words == 2) {
                            f.pushWords(1);
                        }
                    }
                }
                case Bytecodes.INVOKEVIRTUAL, Bytecodes.INVOKESPECIAL, Bytecodes.INVOKESTATIC, Bytecodes.INVOKEINTERFACE, Bytecodes.INVOKEDYNAMIC -> invoke(m, s, f, at, bc);
                case Bytecodes.LDC, Bytecodes.LDC_W -> f.pushWords(1);
                case Bytecodes.LDC2_W -> f.pushWords(2);
                case Bytecodes.MULTIANEWARRAY -> {
                    f.pop(s.readUByte(bci + 3));
                    f.pushWords(1);
                }
                case Bytecodes.NEW -> {
                    String cls = m.getConstantPool().lookupType(s.readCPI(), bc).toJavaName();
                    // a NEW node of an entry class is not the FRESH entry of that class (a node joins a representation)
                    f.push(Set.of("N:" + cls + (family.entryClasses.containsValue(cls) ? "#new" : "")));
                }
                case Bytecodes.ANEWARRAY -> {
                    f.pop();
                    f.push(Set.of("N:[L" + m.getConstantPool().lookupType(s.readCPI(), bc).toJavaName() + ";"));
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
                    int e = Bytecodes.stackEffectOf(bc);
                    if (e < 0) {
                        f.pop(-e);
                    } else {
                        f.pushWords(e);
                    }
                    if (bc == Bytecodes.ILOAD || bc == Bytecodes.LLOAD || bc == Bytecodes.FLOAD || bc == Bytecodes.DLOAD || bc == Bytecodes.IINC || (bc >= Bytecodes.NOP && bc <= Bytecodes.DLOAD_3) ||
                                    (bc >= Bytecodes.IADD && bc <= Bytecodes.DCMPG) || bc == Bytecodes.NEWARRAY) {
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

        /** The type operand of this CHECKCAST / INSTANCEOF is exact (a final class, not an array or an interface). */
        private static boolean exactType(ResolvedJavaMethod m, BytecodeStream s, int bc) {
            jdk.vm.ci.meta.JavaType t = m.getConstantPool().lookupType(s.readCPI(), bc);
            if (t.getName().startsWith("[")) {
                return false;
            }
            try {
                // a final class by its class file (this JDK's java.lang.String is `non-sealed`: not exact, as in StringAtoms)
                Class<?> c = Class.forName(t.toJavaName(), false, JdkModelPremiseTest.class.getClassLoader());
                return !c.isInterface() && Modifier.isFinal(c.getModifiers());
            } catch (ClassNotFoundException e) {
                return true; // an unknown class: conservatively exact
            }
        }

        /** A stored value's modelled labels; a NEW object stored somewhere escapes (recorded), a node joining a representation is kept. */
        private Set<String> modelledValue(Set<String> v, String at) {
            Set<String> out = new TreeSet<>(v);
            out.removeIf(Checker::ir);
            return out;
        }

        /** {@code arr[i] = v} with tracked {@code v}: a slot store when {@code arr} is a representation (or a copy of one). */
        private void storeInto(String at, Set<String> arr, Set<String> vAll) {
            Set<String> v = new TreeSet<>(vAll);
            v.removeIf(l -> l.startsWith("N:") && !recordEscape(l, at));
            if (v.isEmpty()) {
                return;
            }
            if (arr.isEmpty()) {
                result.violations.add(at + ": a tracked value is stored into an unmodelled array " + v);
                return;
            }
            for (String a : arr) {
                if (ir(a)) {
                    continue;
                }
                String owner = repOwner(a);
                if (a.startsWith("N:")) {
                    for (String l : v) {
                        pendingN.computeIfAbsent(a, k -> new LinkedHashSet<>()).add("store " + a + " [] <- " + l);
                    }
                    continue;
                }
                if (owner == null && elem(a) != null && !a.startsWith("C:") && !a.startsWith("K")) {
                    for (String l : v) {
                        result.observed.add("store " + a + " [] <- " + l); // an argument's array (a user array: Arrays.asList)
                    }
                    continue;
                }
                if (owner == null) {
                    result.violations.add(at + ": a tracked value is stored into an array " + a + " <- " + v);
                    continue;
                }
                String slot = repSlot(a);
                if (slot == null) {
                    result.violations.add(at + ": a tracked value is stored into a node representation as into an array " + a + " <- " + v);
                    continue;
                }
                for (String l : v) {
                    if (l.equals(eLabel(slot, owner))) {
                        continue; // an element of the same representation moved inside it (a shift)
                    }
                    if (isR(l) || isE(l) || l.startsWith("K")) {
                        result.violations.add(at + ": a representation value is stored into a representation " + l);
                        continue;
                    }
                    result.observed.add("store " + owner + " " + slot + " <- " + l);
                }
            }
        }

        /** A NEW object stored as a value (true: keep it as a value, e.g. a node linked into a representation). */
        private boolean recordEscape(String n, String at) {
            escapedN.add(new String[]{n, at});
            return false;
        }

        private void putField(String at, JavaField fld, Set<String> objAll, Set<String> valueAll) {
            if (lazyPut(at, fld, objAll, valueAll)) {
                return; // a pipeline link (the lazy composition interprets it)
            }
            Set<String> obj = new TreeSet<>(objAll);
            obj.removeIf(Checker::ir);
            Set<String> value = new TreeSet<>(valueAll);
            value.removeIf(Checker::ir);
            if (family.viewCaches.contains(qn(fld))) {
                // a view cache holds a NEW view of this entry (its pending stores are the FRESH result's, read back below)
                for (String l : value) {
                    if (l.startsWith("N:")) {
                        cacheStores.computeIfAbsent(qn(fld), k -> new TreeSet<>()).add(l);
                    } else {
                        result.violations.add(at + ": a tracked value that is no NEW view is stored into the view cache " + qn(fld) + " " + l);
                    }
                }
                return;
            }
            String recordSlot = family.recordSlots.get(qn(fld));
            if (recordSlot != null) {
                // a record component the family models as a slot (its real field is never accessed by the engine)
                for (String o : obj) {
                    for (String v : value) {
                        result.observed.add("store " + o + " " + recordSlot + " <- " + v);
                    }
                }
                return;
            }
            String kind = repKind(fld);
            if (kind != null) {
                String arraySlot = JdkModels.arrayRepSlot(kind) != null ? kind.substring(0, kind.length() - 2) : null;
                for (String o : obj) {
                    String owner = isR(o) ? owner(o) : o.startsWith("N:") ? o : kind.startsWith("-@") ? o + "{" + kind.substring(2) + "}" : o;
                    for (String l : value) {
                        if (nodeArrays() && owner.startsWith("N:") && JdkModels.slot(kind) == null && (l.startsWith("N:") || isR(l))) {
                            // a NEW node's link (to a NEW node or into the representation): read back below; a NEW node
                            // linked from a joined NEW node joins its representation too (the join fixpoint)
                            nodeLinks.computeIfAbsent(owner + " " + qn(fld), k -> new TreeSet<>()).add(l);
                        }
                        if (JdkModels.slot(kind) != null) {
                            // a node representation's element field (of slot `kind`): a slot store (pending for a NEW node until it is linked)
                            if (owner.startsWith("N:")) {
                                pendingN.computeIfAbsent(owner, k -> new LinkedHashSet<>()).add("store " + owner + " " + kind + " <- " + l);
                            } else {
                                result.observed.add("store " + owner + " " + kind + " <- " + l);
                            }
                        } else if (l.startsWith("N:")) {
                            // a NEW node (or array: of slot arraySlot) becomes (part of) the representation of the owner
                            if (!owner.startsWith("N:")) {
                                joinedN.computeIfAbsent(l, k -> new LinkedHashSet<>()).add(new Joined(owner, arraySlot));
                            }
                        } else if (isR(l) && owner(l).equals(owner) || repOwner(l) != null && repOwner(l).equals(owner) || isR(l) && owner.startsWith("N:")) {
                            // the representation (or a copy of it: grow) stays the representation; an iterator's link into it
                        } else if (arraySlot != null && (l.startsWith("C:") || l.startsWith("K") && !isE(l.substring(3)))) {
                            // COPY: the representation := a copy of (or) a callback's / an argument's array: its elements
                            String el = l.startsWith("C:") ? elem(l) : l.substring(3);
                            result.observed.add("store " + owner + " " + arraySlot + " <- " + el);
                        } else {
                            result.violations.add(at + ": the representation " + fld.getName() + " of " + o + " := " + l);
                        }
                    }
                }
                return;
            }
            if (nodeArrays() && value.stream().anyMatch(l -> l.startsWith("N:"))) {
                // a NEW JDK object held in a real field of a tracked object (a HashSet's map) is part of that object's
                // state: an observed store (the table declares it: a FRESH temp stored there), never an unrecorded escape
                Set<String> nv = new TreeSet<>();
                for (String l : value) {
                    if (!l.startsWith("N:")) {
                        nv.add(l);
                        continue;
                    }
                    for (String o : obj) {
                        if (o.startsWith("N:")) {
                            pendingN.computeIfAbsent(o, k -> new LinkedHashSet<>()).add("store " + o + " " + qn(fld) + " <- " + l);
                            heldN.add(l);
                        } else if (o.matches(ARG)) {
                            result.observed.add("store " + o + " " + qn(fld) + " <- " + l);
                            heldN.add(l);
                        } else {
                            recordEscape(l, at);
                        }
                    }
                }
                value = nv;
            }
            for (String l : value) {
                if (isR(l)) {
                    repCached.add(at + ": the unabstracted field " + qn(fld) + " <- " + l); // a cached representation
                }
            }
            for (String o : obj) {
                if (o.startsWith("N:")) {
                    for (String l : value) {
                        if (l.startsWith("N:") && !lazyMode) {
                            recordEscape(l, at);
                        } else {
                            pendingN.computeIfAbsent(o, k -> new LinkedHashSet<>()).add("store " + o + " " + qn(fld) + " <- " + l);
                        }
                    }
                } else if (isE(o) || o.startsWith("C:") || isR(o) || o.startsWith("K")) {
                    if (nodeArrays() && isR(o) && fld.getJavaKind() != JavaKind.Object && value.isEmpty()) {
                        continue; // a primitive field of a representation node (a tree bin's `red`): no tracked value
                    }
                    result.violations.add(at + ": a field of a tracked element is written " + o);
                }
            }
            // in the lazy premise a NEW object stored into NEW objects stays pending (above), not an escape
            Set<String> real = lazyMode && !obj.isEmpty() && obj.stream().allMatch(x -> x.startsWith("N:")) ? Set.of() : modelled(value, at);
            for (String o : obj) {
                if (real.isEmpty() || o.startsWith("N:")) {
                    continue;
                }
                if (o.matches(ARG)) {
                    for (String l : real) {
                        result.observed.add("store " + o + " " + qn(fld) + " <- " + l); // a real field's store (a declared STORE)
                    }
                } else if (!(isE(o) || o.startsWith("C:") || isR(o) || o.startsWith("K"))) {
                    result.violations.add(at + ": a tracked value is stored into the real field " + fld.format("%H.%n") + " of " + o + " " + real);
                }
            }
            if (!real.isEmpty() && obj.isEmpty()) {
                result.violations.add(at + ": a tracked value is stored into the real field " + fld.format("%H.%n") + " of an untracked object " + real);
            }
        }

        private Set<String> getField(String at, JavaField fld, Set<String> obj) {
            Set<String> out = new TreeSet<>();
            boolean ref = fld.getJavaKind() == JavaKind.Object;
            String kind = repKind(fld);
            if (family.viewCaches.contains(qn(fld))) {
                // a view cache's value is a NEW view made by an earlier call of this method (the same FRESH view: its
                // stores), or the one this walk stored (read back); the cache's writers are reviewed (viewCachesHoldOnlyViews)
                return new TreeSet<>(cacheStores.getOrDefault(qn(fld), Set.of()));
            }
            String exact = family.exactFields.get(qn(fld));
            String recordSlot = family.recordSlots.get(qn(fld));
            for (String o : obj) {
                if (exact != null && (ir(o) || o.matches(ARG) || o.startsWith("X:"))) {
                    out.add("X:" + exact); // an internal object of exact class (premise data, reviewed)
                    continue;
                }
                if (o.startsWith("X:")) {
                    continue; // a field of an internal object: untracked
                }
                if (recordSlot != null && !ir(o)) {
                    out.add(eLabel(recordSlot, o)); // a record component the family models as a slot
                    continue;
                }
                if (ir(o)) {
                    if (ref) {
                        out.add(o); // a field of an ir value: an ir value
                    }
                    continue;
                }
                if (isR(o) && kind != null) {
                    // a node representation: its element field is a value of that field's slot, its links stay the representation
                    out.add(JdkModels.slot(kind) != null ? eLabel(kind, owner(o)) : o);
                    continue;
                }
                if (o.startsWith("N:") && nodeArrays() && kind != null && JdkModels.slot(kind) == null) {
                    out.addAll(nodeLinks.getOrDefault(o + " " + qn(fld), Set.of())); // a NEW node's link, read back
                    continue;
                }
                if (o.startsWith("N:")) {
                    if (ref) {
                        // a NEW node's element field was stored as its slot (a pending slot store)
                        String member = kind != null && JdkModels.slot(kind) != null ? kind : qn(fld);
                        for (String p : pendingN.getOrDefault(o, Set.of())) {
                            if (p.startsWith("store " + o + " " + member + " <- ")) {
                                out.add(p.substring(p.indexOf(" <- ") + 4)); // a read-back of the entry's own store
                            }
                        }
                    }
                    continue;
                }
                if (isE(o) || o.startsWith("C:") || isR(o) || o.startsWith("K")) {
                    if (ref) {
                        result.violations.add(at + ": a field of a tracked element is read " + o);
                    }
                    continue;
                }
                if (kind != null) {
                    out.add(repLabel(kind, o));
                } else if (ref) {
                    if (o.startsWith("D:")) {
                        out.add(o);
                    } else if (o.endsWith(".[]")) {
                        result.violations.add(at + ": a field of an array element is read " + o + "{" + qn(fld) + "}");
                    } else if (o.chars().filter(c -> c == '{').count() >= 2) {
                        out.add("D:" + o); // too deep to name: tracked, but any effect it takes part in is undeclared (a violation)
                    } else {
                        out.add(o + "{" + qn(fld) + "}");
                    }
                }
            }
            return out;
        }

        private void invoke(ResolvedJavaMethod m, BytecodeStream s, Frame f, String at, int bc) {
            ConstantPool cp = m.getConstantPool();
            int rawIndex = bc == Bytecodes.INVOKEDYNAMIC ? s.readCPI4() : s.readCPI();
            JavaMethod callee = cp.lookupMethod(rawIndex, bc, m);
            Signature sig = callee.getSignature();
            boolean hasReceiver = bc != Bytecodes.INVOKESTATIC && bc != Bytecodes.INVOKEDYNAMIC;
            // a linked invokedynamic or signature-polymorphic call site resolves to its adapter, whose
            // parameters are the call site's plus the appendix (last) and, for a static adapter of a virtual call site,
            // the receiver (first): only the call site's own words are on the operand stack
            List<JavaKind> kinds = new ArrayList<>();
            for (int i = 0; i < sig.getParameterCount(false); i++) {
                kinds.add(sig.getParameterKind(i));
            }
            if (callee instanceof ResolvedJavaMethod rm && (bc == Bytecodes.INVOKEDYNAMIC || bc == Bytecodes.INVOKEVIRTUAL) && cp.lookupAppendix(rawIndex, bc) != null) {
                kinds.remove(kinds.size() - 1);
                if (hasReceiver && rm.isStatic()) {
                    kinds.remove(0);
                }
            }
            int n = kinds.size();
            List<Set<String>> args = new ArrayList<>();
            for (int i = 0; i < n + (hasReceiver ? 1 : 0); i++) {
                args.add(null);
            }
            for (int i = n - 1; i >= 0; i--) {
                args.set(i + (hasReceiver ? 1 : 0), f.pop(kinds.get(i).getSlotCount()));
            }
            if (hasReceiver) {
                args.set(0, f.pop());
            }
            // a NEW object counts as tracked only once it holds a tracked value (an exception's construction is not followed)
            boolean anyTracked = args.stream().anyMatch(a -> a.stream().anyMatch(l -> !l.startsWith("N:") && !l.startsWith("X:") || l.startsWith("N:") && !pendingN.getOrDefault(l, Set.of())
                            .isEmpty()));
            Set<String> res = new TreeSet<>();
            String cid = mid(callee);
            if (cid.equals("java.lang.reflect.Array#newInstance(Ljava/lang/Class;I)Ljava/lang/Object;")) {
                res.add("N:~[Ljava.lang.Object;"); // a NEW array of a runtime class (its class is not exact)
                anyTracked = false;
            }
            Set<String> hooked = lazyInvoke(m, s, at, bc, callee, cid, rawIndex, args);
            // (a collection's construction: a java.util class that is no Throwable; exceptions are observations)
            boolean newState = nodeArrays() && !anyTracked && callee.getDeclaringClass().toJavaName().startsWith("java.util.") &&
                            !type("java.lang.Throwable").isAssignableFrom(type(callee.getDeclaringClass().toJavaName())) &&
                            (bc == Bytecodes.INVOKESPECIAL && callee.getName().equals("<init>") && args.get(0).stream().anyMatch(l -> l.startsWith("N:")) ||
                                            bc == Bytecodes.INVOKESTATIC && sig.getReturnKind() == JavaKind.Object);
            if (hooked != null) {
                res.addAll(hooked); // the lazy premise's composition
            } else if (newState && deterministic(callee, bc) != null) {
                // the construction of a NEW JDK object (its constructor, a static factory) is walked even with no
                // tracked argument: the NEW objects it keeps in its real fields are its state (declared FRESH temps)
                for (ResolvedJavaMethod target : deterministic(callee, bc)) {
                    res.addAll(walk(target, args));
                }
            } else if (anyTracked) {
                args.forEach(a -> a.stream().filter(Checker::isR).forEach(l -> {
                    if (bc == Bytecodes.INVOKEDYNAMIC) {
                        repCached.add(at + ": captured " + l);
                    }
                }));
                if (bc == Bytecodes.INVOKEDYNAMIC) {
                    if (args.stream().allMatch(Checker::irOnly)) {
                        args.forEach(a -> res.addAll(a)); // an ir value captured: the IR states it; the capture is an ir value
                    } else {
                        result.violations.add(at + ": a tracked value is captured by invokedynamic " + args);
                    }
                } else if (cid.startsWith("java.util.Arrays#copyOf([Ljava/lang/Object;I") || cid.startsWith("java.util.Arrays#copyOfRange([Ljava/lang/Object;II")) {
                    // a copy with the same elements: of a representation (K), of a callback's or an argument's array.
                    // `K=` (an EXACT Object[]) for copyOf(T[], int) relies on the JDK invariant that a
                    // representation array (ArrayList/Vector.elementData, ListN.elements, ...) is exactly an Object[] (every
                    // JDK store into it is one). A user Vector subclass can store another array class into its protected
                    // elementData, but that store meets the engine's field rule (a named refusal), never this copy.
                    boolean exact = cid.endsWith("I)[Ljava/lang/Object;") || cid.endsWith("II)[Ljava/lang/Object;");
                    for (String l : args.get(0)) {
                        String el = elem(l);
                        if (ir(l)) {
                            res.add(l);
                        } else if (el != null) {
                            res.add((exact ? "K=:" : "K~:") + el);
                        } else if (!l.startsWith("N:")) {
                            result.violations.add(at + ": a copy of an unmodelled array " + l);
                        }
                    }
                } else if (cid.equals("java.lang.System#arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V")) {
                    arraycopy(at, args.get(0), args.get(2));
                } else if (family.stringSinks && stringSinkCall(m, s, at, bc, callee, cid, hasReceiver, args, res)) {
                    // a String method (observed), a call on an exact internal object (walked), on an ir receiver
                } else if (nameDesc(callee).equals("getClass()Ljava/lang/Class;")) {
                    // an observation of the reference (Object.getClass is final and native); of a value
                    // that may be a user String, a CLASS_CHECK usage (the engine's StringAtoms row), which only a callback
                    // on it (its usages are the callback's) or an `ir` slot (the IR walk sees it) covers
                    classCheck(args.get(0), mid(m) + "@" + s.currentBCI());
                } else if (cid.equals("java.lang.System#identityHashCode(Ljava/lang/Object;)I")) {
                    // an observation of the reference
                } else {
                    List<ResolvedJavaMethod> targets = deterministic(callee, bc);
                    if (targets != null) {
                        for (ResolvedJavaMethod target : targets) {
                            res.addAll(walk(target, args)); // a package-private method and its same-package overrides
                        }
                    } else if (hasReceiver && irReceiverCall(m, s, at, cid, args, res)) {
                        // a tracked value passed to a call on an ir receiver: a callback on it (every family)
                    } else if (!args.get(0).isEmpty() && irOnly(args.get(0))) {
                        // a call on an ir value (e.g. messageSupplier.get()): the IR states it; its result is an ir value
                        res.addAll(args.get(0));
                        args.forEach(a -> res.addAll(a.stream().filter(Checker::ir).toList()));
                    } else {
                        String site = mid(m) + "@" + s.currentBCI();
                        callback(at, site, cid, args);
                        res.add("C:" + cid + "@" + site); // the result of this call (a temp's binder is compared by site)
                    }
                }
            }
            JavaKind rk = sig.getReturnKind();
            if (rk != JavaKind.Void) {
                if (rk == JavaKind.Object) {
                    f.push(res);
                } else {
                    f.pushWords(rk.getSlotCount());
                }
            }
        }

        /**
         * F6 ({@link JdkModels.Family#stringSinks}): (1) a call into {@code java.lang.String} with a tracked value is
         * the walk's own business (a terminal usage of a tracked receiver, the Phase-A usage of an argument and the callee's
         * IR or model): an observed callback, never walked; a static one is {@code call <cid> on <arg 0 | _> <args> @ site};
         * (2) a call on an internal object of exact class ({@code X:<class>}, an {@link JdkModels.Family#exactFields}
         * value) that passes a tracked value is that class's code: walked (an untracked call on it is no effect); (3) a call
         * on an {@code ir} receiver that passes a tracked value is a callback on it ({@code call <cid> on I<k> ...}: the
         * receiver's override receives the value, which is otherwise silently dropped). False: none applies.
         */
        private boolean stringSinkCall(ResolvedJavaMethod m, BytecodeStream s, String at, int bc, JavaMethod callee, String cid, boolean hasReceiver, List<Set<String>> args, Set<String> res) {
            String site = mid(m) + "@" + s.currentBCI();
            if (callee.getDeclaringClass().toJavaName().equals("java.lang.String")) {
                if (hasReceiver) {
                    callback(at, site, cid, args);
                } else {
                    List<String> obs = new ArrayList<>(List.of("call " + cid + " on"));
                    for (Set<String> a0 : args) {
                        Set<String> a = modelled(a0, at);
                        List<String> vs = a.isEmpty() ? List.of("_") : List.copyOf(a);
                        List<String> next = new ArrayList<>();
                        for (String o : obs) {
                            for (String v : vs) {
                                next.add(o + " " + v);
                            }
                        }
                        obs = next;
                    }
                    if (args.isEmpty()) {
                        obs = List.of("call " + cid + " on _");
                    }
                    for (String o : obs) {
                        result.observed.add(o + " @ " + site);
                    }
                }
                res.add("C:" + cid + "@" + site);
                return true;
            }
            boolean otherTracked = args.stream().skip(hasReceiver ? 1 : 0).anyMatch(a -> a.stream().anyMatch(l -> !ir(l) && !l.startsWith("X:") && (!l.startsWith("N:") || !pendingN.getOrDefault(l, Set
                            .of()).isEmpty())));
            if (hasReceiver && !args.get(0).isEmpty() && args.get(0).stream().allMatch(l -> l.startsWith("X:"))) {
                if (otherTracked) {
                    for (String x : args.get(0)) {
                        ResolvedJavaMethod target = type(x.substring(2)).resolveConcreteMethod((ResolvedJavaMethod) callee, type(x.substring(2)));
                        Assert.assertNotNull(at + ": the exact class " + x + " implements " + cid, target);
                        res.addAll(walk(target, args));
                    }
                }
                return true;
            }
            return false;
        }

        /**
         * Rule (3): for every family, a call (no deterministic target) on an {@code ir}
         * receiver that passes a tracked value is a callback on it ({@code call <cid> on I<k> ...}): the receiver's override
         * receives the value (otherwise it is silently dropped outside F6). False: not such a call.
         */
        private boolean irReceiverCall(ResolvedJavaMethod m, BytecodeStream s, String at, String cid, List<Set<String>> args, Set<String> res) {
            String site = mid(m) + "@" + s.currentBCI();
            boolean otherTracked = args.stream().skip(1).anyMatch(a -> a.stream().anyMatch(l -> !ir(l) && !l.startsWith("X:") && (!l.startsWith("N:") || !pendingN.getOrDefault(l, Set.of())
                            .isEmpty())));
            if (!args.get(0).isEmpty() && irOnly(args.get(0)) && otherTracked) {
                List<String> obs = new ArrayList<>();
                for (String r : args.get(0)) {
                    obs.add("call " + cid + " on " + r);
                }
                for (int i = 1; i < args.size(); i++) {
                    Set<String> a = modelled(args.get(i), at);
                    List<String> vs = a.isEmpty() ? List.of("_") : List.copyOf(a);
                    List<String> next = new ArrayList<>();
                    for (String o : obs) {
                        for (String v : vs) {
                            next.add(o + " " + v);
                        }
                    }
                    obs = next;
                }
                for (String o : obs) {
                    result.observed.add(o + " @ " + site);
                }
                res.add("C:" + cid + "@" + site);
                return true;
            }
            return false;
        }

        /** {@code System.arraycopy(src, .., dst, ..)}: inside one representation, or a bulk copy into / out of one. */
        private void arraycopy(String at, Set<String> srcAll, Set<String> dstAll) {
            Set<String> src = new TreeSet<>(srcAll);
            src.removeIf(Checker::ir);
            Set<String> dst = new TreeSet<>(dstAll);
            dst.removeIf(Checker::ir);
            for (String sl : src) {
                String el = elem(sl);
                if (el == null && !sl.startsWith("N:")) {
                    result.violations.add(at + ": arraycopy from an unmodelled array " + sl);
                    continue;
                }
                for (String d : dst) {
                    String owner = repOwner(d);
                    String slot = repSlot(d);
                    if (sl.startsWith("N:")) {
                        continue; // a NEW array's elements (none tracked unless pending): its escape is recorded
                    }
                    if (owner != null && el.equals(eLabel(slot, owner))) {
                        continue; // a shift inside one representation
                    }
                    if (owner != null && !isE(el)) {
                        result.observed.add("store " + owner + " " + slot + " <- " + el); // a callback's / an argument's array into the slot
                    } else if (owner == null && d.startsWith("N:")) {
                        pendingN.computeIfAbsent(d, k -> new LinkedHashSet<>()).add("store " + d + " [] <- " + el);
                    } else if (owner == null && elem(d) != null && !d.startsWith("C:") && !d.startsWith("K")) {
                        result.observed.add("store " + d + " [] <- " + el); // the slot's elements into an argument's array
                    } else {
                        result.violations.add(at + ": arraycopy " + sl + " -> " + d);
                    }
                }
                if (dst.isEmpty()) {
                    result.violations.add(at + ": arraycopy of " + sl + " into an unmodelled array");
                }
            }
        }

        /** A call on a tracked value that is not followed: a callback (a virtual call of user-reachable code) at {@code site}. */
        void callback(String at, String site, String cid, List<Set<String>> allArgs) {
            List<Set<String>> args = new ArrayList<>();
            for (Set<String> a : allArgs) {
                Set<String> x = modelled(a, at); // an ir value passed along: the IR states it; a NEW object's escape is recorded
                for (String l : List.copyOf(x)) {
                    String entryL = entryLabel(l);
                    if (entryL != null) {
                        // a node handed to the callback (receiver or argument) = a FRESH entry of its map
                        x.remove(l);
                        x.add(entryL);
                        result.observed.add("store " + entryL + " <map> <- " + owner(l));
                    }
                }
                args.add(x);
            }
            Set<String> recv = args.get(0);
            String entryOperand = family.entryClasses.values().stream().map(e -> "N:" + java.util.regex.Pattern.quote(e)).reduce((x, y) -> x + "|" + y).orElse("N:\\b\\B");
            String recvOperand = ARG + "|E<[^>]+>:" + ARG + "|(" + ARG + ")\\.\\[\\]|C:[^ ]+|" + entryOperand; // a callback's result (a temp) may be a receiver; a FRESH entry
            String operand = recvOperand + "|C:[^ ]+|S"; // S, the op's sink (a consumer the JDK code passes on)
            for (String r : recv) {
                if (!r.matches(recvOperand)) {
                    result.violations.add(at + ": a call on a tracked derived value " + r + " " + cid);
                    continue;
                }
                List<String> obs = new ArrayList<>(List.of("call " + cid + " on " + r));
                for (int i = 1; i < args.size(); i++) {
                    Set<String> a = args.get(i);
                    a.stream().filter(Checker::isR).forEach(l -> repCached.add(at + ": passed to the callback " + cid + " " + l));
                    boolean perValue = lazyMode || nodeArrays(); // F2's key protocol meets a query key or a stored key at one site
                    if (a.size() > 1 && !perValue || a.stream().anyMatch(l -> !l.matches(operand))) {
                        result.violations.add(at + ": a callback argument that is not one operand " + a);
                    }
                    // the lazy premise's argument may be one of several values (a sink's state): one observation per value
                    List<String> vs = a.isEmpty() ? List.of("_") : perValue ? List.copyOf(a) : List.of(String.join(" ", a));
                    List<String> next = new ArrayList<>();
                    for (String o : obs) {
                        for (String v : vs) {
                            next.add(o + " " + v);
                        }
                    }
                    obs = next;
                }
                for (String o : obs) {
                    result.observed.add(o + " @ " + site);
                }
            }
            if (recv.isEmpty() && args.stream().anyMatch(a -> !a.isEmpty())) {
                result.violations.add(at + ": a tracked value is passed to " + cid + " " + args);
            }
        }

        /**
         * The methods that can run for a call, when the bytecode fixes them: the one target of a static, special,
         * private or final call (or a final class); for a package-private method in a {@code java.*} package, the method
         * and every override of it in the same package of java.base (no class outside the package can
         * override it, but one inside can: {@code ArrayDeque$DescendingIterator.postDelete}, F2's {@code LinkedHashMap}
         * hooks). Null: a virtual call (a callback).
         */
        List<ResolvedJavaMethod> deterministic(JavaMethod callee, int bc) {
            ResolvedJavaType holder = type(callee.getDeclaringClass().toJavaName());
            ResolvedJavaMethod decl = null;
            for (ResolvedJavaType t = holder; decl == null && t != null; t = t.getSuperclass()) {
                decl = declared(t, nameDesc(callee));
            }
            if (decl == null) {
                return null;
            }
            int mod = decl.getModifiers();
            boolean pkgPrivate = !Modifier.isPublic(mod) && !Modifier.isProtected(mod) && !Modifier.isPrivate(mod) && decl.getDeclaringClass().toJavaName().startsWith("java.");
            if (bc == Bytecodes.INVOKESTATIC || bc == Bytecodes.INVOKESPECIAL || decl.isPrivate() || decl.isFinal() || decl.getDeclaringClass().isFinalFlagSet()) {
                return decl.isAbstract() ? null : List.of(decl);
            }
            if (pkgPrivate) {
                List<ResolvedJavaMethod> out = new ArrayList<>();
                if (!decl.isAbstract()) {
                    out.add(decl);
                }
                out.addAll(samePackageOverrides(decl));
                return out.isEmpty() ? null : out;
            }
            return null;
        }

        /** The overrides of package-private {@code decl} declared by the other classes of its java.base package. */
        private List<ResolvedJavaMethod> samePackageOverrides(ResolvedJavaMethod decl) {
            ResolvedJavaType holder = decl.getDeclaringClass();
            String cls = holder.toJavaName();
            List<ResolvedJavaMethod> out = new ArrayList<>();
            for (String c : packageClasses(cls.substring(0, cls.lastIndexOf('.')))) {
                if (c.equals(cls)) {
                    continue;
                }
                ResolvedJavaType t;
                try {
                    t = type(c);
                } catch (Throwable x) {
                    continue; // not loadable by name here: not a subclass the image can instantiate either (checked: none in java.util)
                }
                if (!t.isInterface() && holder.isAssignableFrom(t)) {
                    ResolvedJavaMethod o = declared(t, nameDesc(decl));
                    if (o != null && !o.isStatic() && !o.isAbstract() && !o.isPrivate()) {
                        out.add(o);
                    }
                }
            }
            return out;
        }

        /**
         * A class check of the values {@code ls}: an observed {@code classcheck} of each that may be a user String;
         * also with its site (the table states the sites); in every family.
         */
        private void classCheck(Set<String> ls, String site) {
            for (String l : ls) {
                if (mayBeString(l)) {
                    result.observed.add("classcheck " + l);
                    // in every family a class check is explicit (a callback on the value records
                    // only its terminal usage, never the CLASS_CHECK): the table states it with its site
                    result.observed.add("classcheck " + l + " @ " + site);
                }
            }
        }

        /** The family has node arrays (a node representation whose table is an array of nodes: F2). */
        boolean nodeArrays() {
            return !family.entryClasses.isEmpty();
        }

        /**
         * {@code arr[i] = v} in a family with node arrays: into a node array of owner p (R:p, a hash table): a NEW
         * node joins p's representation, a node of p's representation moves inside it; into a NEW array: a NEW node is a
         * pending store of the array (not an escape: it joins a representation with the array, or is reported). Returns
         * the values left for {@link #storeInto} (the other arrays).
         */
        private Set<String> nodeArrayStore(String at, Set<String> arr, Set<String> v) {
            Set<String> rest = new TreeSet<>(v);
            for (String a : arr) {
                if (isR(a) && slotOf(a) == null) {
                    String p = owner(a);
                    for (String l : v) {
                        if (l.startsWith("N:")) {
                            joinedN.computeIfAbsent(l, k -> new LinkedHashSet<>()).add(new Joined(p, null));
                        } else if (!(isR(l) && slotOf(l) == null && owner(l).equals(p))) {
                            result.violations.add(at + ": a value that is not a node of the same representation is stored into the node array " + a + " <- " + l);
                        }
                    }
                    rest.clear();
                } else if (a.startsWith("N:")) {
                    for (String l : v) {
                        if (l.startsWith("N:")) {
                            pendingN.computeIfAbsent(a, k -> new LinkedHashSet<>()).add("store " + a + " [] <- " + l);
                            rest.remove(l);
                        }
                    }
                }
            }
            return rest;
        }

        /**
         * The FRESH entry label of node label {@code l} (a node R:p of a representation whose owner p's class has
         * an entry class in the family: "N:" + that class), or null.
         */
        String entryLabel(String l) {
            if (!isR(l) || slotOf(l) != null || family.entryClasses.isEmpty()) {
                return null;
            }
            ResolvedJavaType t = ownerType(owner(l));
            if (t == null) {
                return null;
            }
            for (Map.Entry<String, String> e : family.entryClasses.entrySet()) {
                if (type(e.getKey()).isAssignableFrom(t)) {
                    return "N:" + e.getValue();
                }
            }
            return null;
        }

        /** The static type of an owner label {@code A<k>} / {@code A<k>{C.f}...} (the last field's type), or null. */
        private ResolvedJavaType ownerType(String p) {
            java.util.regex.Matcher fm = java.util.regex.Pattern.compile("\\{([^}]+)\\}$").matcher(p);
            if (fm.find()) {
                ResolvedJavaField rf = field(fm.group(1));
                return rf == null ? null : type(rf.getType().toJavaName());
            }
            if (p.matches("A\\d+")) {
                int k = Integer.parseInt(p.substring(1));
                if (k == 0 && !entry.isStatic()) {
                    return entry.getDeclaringClass();
                }
                String tn = entry.getSignature().getParameterType(k - (entry.isStatic() ? 0 : 1), null).toJavaName();
                return tn.contains("[") ? null : type(tn);
            }
            return null;
        }

        /**
         * May label {@code l} be a user-supplied object whose code runs at a call on it: an argument
         * {@code A<k>} (or a field path of it) or a callback result {@code C:} whose static type is not a final
         * {@code java.*} class (unknown: yes).
         */
        boolean userObject(String l) {
            ResolvedJavaType t;
            if (l.matches(ARG)) {
                t = ownerType(l);
            } else if (l.startsWith("C:")) {
                String cid = noSite(l.substring(2));
                String rt = cid.substring(cid.indexOf(')') + 1);
                if (!rt.startsWith("L")) {
                    return !rt.startsWith("[");
                }
                t = type(rt.substring(1, rt.length() - 1).replace('/', '.'));
            } else {
                return false;
            }
            return t == null || !(t.toJavaName().startsWith("java.") && t.isFinalFlagSet());
        }

        /** May label {@code l} be a user String (its declared type admits one; an element or a deep path: yes)? */
        boolean mayBeString(String l) {
            if (ir(l) || l.startsWith("N:") || isR(l) || l.startsWith("K") || l.startsWith("X:")) {
                return false; // the IR's, a NEW JDK object, the representation (an array or a node), a copy of it, an internal object
            }
            if (isE(l) || l.startsWith("D:") || l.endsWith(".[]")) {
                return true; // a slot's value, an element of an array: any Object
            }
            if (l.startsWith("C:")) {
                String cid = noSite(l.substring(2));
                return admitsString(cid.substring(cid.indexOf(')') + 1));
            }
            java.util.regex.Matcher fm = java.util.regex.Pattern.compile("\\{([^}]+)\\}$").matcher(l);
            if (fm.find()) {
                ResolvedJavaField rf = field(fm.group(1));
                return rf == null || admitsString(rf.getType().getName());
            }
            if (l.matches("A\\d+")) {
                int k = Integer.parseInt(l.substring(1));
                if (k == 0 && !entry.isStatic()) {
                    return entry.getDeclaringClass().isAssignableFrom(type("java.lang.String"));
                }
                return admitsString(entry.getSignature().getParameterType(k - (entry.isStatic() ? 0 : 1), null).getName());
            }
            return true;
        }

        /** Does the type with descriptor {@code desc} ({@code Ljava/lang/Object;}) admit a String value? */
        private boolean admitsString(String desc) {
            if (!desc.startsWith("L")) {
                return false; // a primitive or an array
            }
            return type(desc.substring(1, desc.length() - 1).replace('/', '.')).isAssignableFrom(type("java.lang.String"));
        }
    }

    // ------------------------------------------------------------------
    // the lazy premise (F4, java.util.stream)
    // ------------------------------------------------------------------

    /** The downstream sink of a stage's sink (its {@code accept(x)} is the stage's {@code store R <elem> x}). */
    static final String DOWN = "DOWN";
    /** The site of a head's source traversal handing the head's elements to a consumer ({@code Head.forEach}'s sequential path). */
    static final String SOURCE_SITE = "<source-traversal>";
    static final String AP = "java.util.stream.AbstractPipeline";
    /** AbstractPipeline's links: the pipeline structure (abstracted in F4), which the lazy composition interprets. */
    static final Set<String> LINKS = Set.of(AP + ".previousStage", AP + ".nextStage", AP + ".sourceStage", AP + ".sourceSpliterator", AP + ".sourceSupplier");

    /**
     * The F4 entries whose premise the composition does not check (reviewed; each reason stated): their JDK code is not a
     * stage / sink composition the checker walks. Every entry is still resolved and slot-covered ({@link
     * #everyEntryResolvesAndCoversItsSlots}) and every callback site is a real invoke of the callback ({@link
     * #everyLazySiteIsARealInvoke}).
     */
    static final Map<String, String> LAZY_REVIEWED = Map.ofEntries(
                    Map.entry("java.util.stream.ReferencePipeline#toArray()[Ljava/lang/Object;",
                                    "the Nodes machinery (Nodes.builder / FixedNodeBuilder / SpinedBuffer / conc nodes, Node.asArray / flatten): the elements are copied into a NEW Object[] (toArray(Object[]::new))"),
                    Map.entry("java.util.stream.ReferencePipeline#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object;",
                                    "the Nodes machinery: the generator's array receives the elements and is returned (ArrayNode(size, generator) when the size is known, SpinedBuffer.asArray via Nodes.flatten otherwise; the table lists the flatten site, the ArrayNode.<init>@26 site is a second real site of the same callback, no String argument)"),
                    Map.entry("java.util.stream.ReferencePipeline#toList()Ljava/util/List;",
                                    "listFromTrustedArrayNullsAllowed(toArray()): the toArray machinery, then ListN over the array or List12 of its elements (F1's immutable lists, real fields)"),
                    Map.entry("java.util.stream.AbstractPipeline#spliterator()Ljava/util/Spliterator;",
                                    "a WrappingSpliterator over the stage (its real field ph; its buffer / pusher lambdas / SpinedBuffer are the terminal machinery of a pulled pipeline); the view entries below read ph's elements"),
                    Map.entry("java.util.stream.StreamSpliterators$WrappingSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V",
                                    "a pulled pipeline (ph.wrapAndCopyInto(consumer::accept, spliterator) or the buffered tryAdvance): the consumer receives ph's elements"),
                    Map.entry("java.util.stream.StreamSpliterators$WrappingSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z",
                                    "the buffered pull (fillBuffer: SpinedBuffer + a pusher lambda over the source spliterator and the wrapped sink): the consumer receives ph's elements from the buffer at @29"),
                    Map.entry("java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#trySplit()Ljava/util/Spliterator;",
                                    "a NEW WrappingSpliterator over the same ph (parallel evaluation = sequential, [ID 3])"),
                    Map.entry("java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#estimateSize()J", "an observation (a primitive result)"),
                    Map.entry("java.util.stream.Stream#empty()Ljava/util/stream/Stream;",
                                    "a head over the empty spliterator constant (Spliterators.EMPTY_SPLITERATOR, a static: its traversal hands nothing to the sink): no elements, the entry states none"),
                    Map.entry("java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#getExactSizeIfKnown()J", "an observation (a primitive result)"),
                    Map.entry("java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#characteristics()I", "an observation (a primitive result)"));

    /**
     * The terminal ops that are static constants (reviewed): a GETSTATIC of the field is the op, whose sink is a NEW
     * object of the class (FindOps.java: {@code OP_FIND_FIRST = new FindOp<>(true, REFERENCE, Optional.empty(),
     * Optional::isPresent, FindSink.OfRef::new)}, {@code OP_FIND_ANY} the same with false): the composition walks the sink
     * and its {@code get()}.
     */
    static final Map<String, String> STATIC_TERMINALS = Map.of(
                    "java.util.stream.FindOps$FindSink$OfRef.OP_FIND_FIRST", "java.util.stream.FindOps$FindSink$OfRef",
                    "java.util.stream.FindOps$FindSink$OfRef.OP_FIND_ANY", "java.util.stream.FindOps$FindSink$OfRef");

    /**
     * Reviewed equivalences of an observed call and a declared one: (observed callee, the observed site's prefix, the
     * declared callee the entry states instead at one of its sites, why). {@code ReferencePipeline$7$1FlatMap.accept}, when the downstream asked for cancellation, passes the
     * FlatMap sink itself as a Predicate to the mapped stream's {@code allMatch}; its {@code test(o)} is {@code
     * downstream.accept(o); return !cancellationRequested()} (the composition walks it: an S): the same elements reach the
     * same downstream as {@code forEach(S)} (@57), so the entry states forEach only; neither call has a String argument.
     */
    static final List<String[]> LAZY_EQUIVALENT = List.of(
                    new String[]{"java.util.stream.Stream#allMatch(Ljava/util/function/Predicate;)Z", "java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@",
                                    "java.util.stream.Stream#forEach(Ljava/util/function/Consumer;)V",
                                    "FlatMap's cancellation path: allMatch(this) with this.test = downstream.accept = forEach(S)"},
                    new String[]{"java.util.function.Consumer#accept(Ljava/lang/Object;)V", SOURCE_SITE, "java.util.function.Consumer#accept(Ljava/lang/Object;)V",
                                    "[ID 4] Head.forEach's sequential path hands the head's elements to the action inside the source spliterator's traversal (" + SOURCE_SITE +
                                                    "); the entry's site is ForEachOp's accept (the parallel path), the same elements and the same callback"});

    /**
     * The lazy premise's checker. A lazy family's JDK code runs later (a stage's sink when the terminal pulls, a
     * terminal's sink over the stage's elements), so the entry's walk is composed with that code: (1) the op method is
     * walked (the eager checker, with the pipeline links interpreted: a stage's upstream must be the receiver, a head's
     * source spliterator is recorded); (2) a NEW stage's {@code opWrapSink(flags, DOWN)} is walked, then the returned
     * sink's begin / accept(an element of the receiver) / combine / end: {@code DOWN.accept(x)} is the stage's {@code
     * store R <elem> x} and DOWN handed to a callback is the op's sink {@code S} (its elements are what the callback hands
     * to it); a head's source spliterator is traversed with DOWN ({@code AbstractPipeline.copyInto}); (3) a terminal's
     * {@code evaluate(op)} walks {@code op.evaluateSequential(this, _)}, whose {@code wrapAndCopyInto(sink, _)} walks the
     * sink over the receiver's elements (begin, accept, combine(itself, itself): parallel = sequential with the combiner
     * applied on the states, [ID 3], end). A NEW object's virtual call (its class is exact) is walked; a lambda capture is a
     * NEW object whose SAM call walks the lambda's body with its captures; a call on the stage itself walks every
     * implementation in the closed package (or is a declared re-dispatch). A call on a tracked receiver with no other
     * tracked argument and a primitive (or no) result carries no tracked value in or out (the plumbing: flags, sizes,
     * cancellation): not an effect.
     */
    final class LazyChecker extends Checker {
        final JdkModels.Op op;
        /** The links of each NEW stage (field -> labels). */
        final Map<String, Map<String, Set<String>>> links = new HashMap<>();
        /** The NEW stage whose sink is walked ({@code DOWN.accept(x)} is its {@code store R <elem> x}). */
        String stage;
        final Map<String, ResolvedJavaMethod> lambdaImpl = new HashMap<>();
        final Map<String, List<Set<String>>> lambdaCaptures = new HashMap<>();
        final Set<String> reDispatched = new HashSet<>();

        LazyChecker(JdkModels.Op op) {
            super(new JdkModels.Family("f4lazy-" + System.nanoTime(), false, Set.of(), Map.of()));
            this.op = op;
            this.lazyMode = true;
            for (JdkModels.Effect e : op.effects()) {
                if (e instanceof JdkModels.Callback c && c.a().slot() == 0 && c.a().members().isEmpty()) {
                    reDispatched.add(c.cb().substring(c.cb().indexOf('#') + 1)); // a declared re-dispatch on the receiver: observed as a callback
                }
            }
        }

        /** The exact class of a NEW object label (null: not one). */
        String exactClass(String l) {
            if (!l.startsWith("N:") || l.startsWith("N:~") || l.startsWith("N:[") || lambdaImpl.containsKey(l)) {
                return null;
            }
            return l.substring(2);
        }

        /** The implementation of {@code nameDesc} that runs for an exact receiver of class {@code c} (null: none). */
        ResolvedJavaMethod concrete(String c, String nameDesc) {
            ResolvedJavaType t = type(c);
            for (ResolvedJavaType x = t; x != null; x = x.getSuperclass()) {
                ResolvedJavaMethod d = declared(x, nameDesc);
                if (d != null) {
                    return d.isAbstract() ? null : d;
                }
            }
            ArrayDeque<ResolvedJavaType> todo = new ArrayDeque<>(List.of(t.getInterfaces()));
            for (ResolvedJavaType x = t.getSuperclass(); x != null; x = x.getSuperclass()) {
                todo.addAll(List.of(x.getInterfaces()));
            }
            while (!todo.isEmpty()) {
                ResolvedJavaType i = todo.poll();
                ResolvedJavaMethod d = declared(i, nameDesc);
                if (d != null && d.isDefault()) {
                    return d;
                }
                todo.addAll(List.of(i.getInterfaces()));
            }
            return null;
        }

        boolean tracked(Set<String> a) {
            return a.stream().anyMatch(l -> !ir(l) && (!l.startsWith("N:") || !pendingN.getOrDefault(l, Set.of()).isEmpty() || lambdaImpl.containsKey(l)));
        }

        void violation(String v) {
            result.violations.add(v);
        }

        void addElem(String v) {
            if (stage == null) {
                violation("a downstream outside a stage composition receives " + v);
                return;
            }
            pendingN.computeIfAbsent(stage, k -> new LinkedHashSet<>()).add("store " + stage + " <elem> <- " + v);
        }

        @Override
        Set<String> afterWalk(ResolvedJavaMethod m, JdkModels.Op o, Set<String> ret) {
            for (String l : new ArrayList<>(ret)) {
                String c = exactClass(l);
                if (c != null && type(AP).isAssignableFrom(type(c))) {
                    composeStage(l);
                }
            }
            return ret;
        }

        /** (2): the lazy code of the NEW stage {@code n}. */
        void composeStage(String n) {
            Map<String, Set<String>> lk = links.getOrDefault(n, Map.of());
            String outer = stage;
            stage = n;
            String elem = "E<elem>:A0";
            if (lk.containsKey(AP + ".sourceSpliterator") || lk.containsKey(AP + ".sourceSupplier")) {
                if (!lk.getOrDefault(AP + ".sourceSupplier", Set.of()).isEmpty()) {
                    violation(n + ": a supplier source (not modelled) " + lk);
                }
                // a head: the terminal traverses its source spliterator with the wrapped sink
                walk(method(AP + "#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V"), List.of(Set.of(n), Set.of(DOWN), lk.getOrDefault(AP + ".sourceSpliterator", Set.of())));
            } else {
                Set<String> prev = lk.getOrDefault(AP + ".previousStage", Set.of());
                if (!prev.equals(Set.of("A0"))) {
                    violation(n + ": the stage's upstream is not the receiver " + prev);
                }
                ResolvedJavaMethod ows = concrete(exactClass(n), "opWrapSink(ILjava/util/stream/Sink;)Ljava/util/stream/Sink;");
                if (ows == null) {
                    violation(n + ": no opWrapSink");
                } else {
                    for (String k : walk(ows, List.of(Set.of(n), Set.of(), Set.of(DOWN)))) {
                        if (k.equals(DOWN)) {
                            addElem(elem); // the stage's sink is the downstream itself
                        } else {
                            walkSink(k, Set.of(elem));
                        }
                    }
                }
            }
            // the stage's own captured fields are read by its sink code (composed above), not effects of the op
            Set<String> p = pendingN.get(n);
            if (p != null) {
                p.removeIf(x -> !x.startsWith("store " + n + " <elem> <- "));
            }
            stage = outer;
        }

        /** A sink over {@code elems}: begin, accept, combine with itself ([ID 3]), end. */
        void walkSink(String k, Set<String> elems) {
            String c = exactClass(k);
            if (c == null) {
                violation("a sink of an unknown class " + k);
                return;
            }
            // to a fixpoint of the sink's state (a field its accept both reads and writes: ReduceOps$2ReducingSink.state)
            for (int round = 0, before = -1; round < 5 && before != pendingSize(); round++) {
                before = pendingSize();
                walkIf(c, "begin(J)V", List.of(Set.of(k), Set.of()));
                walkIf(c, "accept(Ljava/lang/Object;)V", List.of(Set.of(k), elems));
                for (ResolvedJavaType x = type(c); x != null; x = x.getSuperclass()) {
                    for (ResolvedJavaMethod d : x.getDeclaredMethods(false)) {
                        if (d.getName().equals("combine") && !d.isBridge() && !d.isAbstract() && d.getSignature().getParameterCount(false) == 1 &&
                                        ((ResolvedJavaType) d.getSignature().getParameterType(0, x)).isAssignableFrom(type(c))) {
                            walk(d, List.of(Set.of(k), Set.of(k)));
                        }
                    }
                }
                walkIf(c, "end()V", List.of(Set.of(k)));
            }
        }

        int pendingSize() {
            return pendingN.values().stream().mapToInt(Set::size).sum();
        }

        Set<String> walkIf(String c, String nameDesc, List<Set<String>> args) {
            ResolvedJavaMethod t = concrete(c, nameDesc);
            return t == null ? Set.of() : walk(t, args);
        }

        @Override
        boolean lazyPut(String at, JavaField fld, Set<String> obj, Set<String> value) {
            String q = qn(fld);
            if (!LINKS.contains(q)) {
                return false;
            }
            for (String o : obj) {
                if (o.startsWith("N:")) {
                    links.computeIfAbsent(o, k -> new HashMap<>()).computeIfAbsent(q, k -> new TreeSet<>()).addAll(value);
                }
                // else a link of an existing stage (the upstream's nextStage, a consumed source's := null): no value flow
            }
            return true;
        }

        /** A lambda / method reference's target (LambdaMetafactory's implementation method), or null. */
        ResolvedJavaMethod lambdaTarget(ResolvedJavaMethod m, int rawIndex) {
            try {
                ConstantPool.BootstrapMethodInvocation bmi = m.getConstantPool().lookupBootstrapMethodInvocation(rawIndex, Bytecodes.INVOKEDYNAMIC);
                if (bmi == null || !bmi.getMethod().getDeclaringClass().toJavaName().equals("java.lang.invoke.LambdaMetafactory")) {
                    return null;
                }
                jdk.vm.ci.meta.JavaConstant mh = bmi.getStaticArguments().get(1);
                jdk.vm.ci.meta.ConstantReflectionProvider cr = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getConstantReflection();
                for (ResolvedJavaType t = metaAccess.lookupJavaType(mh); t != null; t = t.getSuperclass()) {
                    if (t.toJavaName().equals("java.lang.invoke.DirectMethodHandle")) {
                        for (ResolvedJavaField f : t.getInstanceFields(false)) {
                            if (f.getName().equals("member")) {
                                return cr.getMethodHandleAccess().resolveLinkToTarget(cr.readFieldValue(f, mh));
                            }
                        }
                    }
                }
            } catch (Throwable x) {
                violation(mid(m) + ": the lambda target does not resolve " + x);
            }
            return null;
        }

        @Override
        Set<String> lazyInvoke(ResolvedJavaMethod m, BytecodeStream s, String at, int bc, JavaMethod callee, String cid, int rawIndex, List<Set<String>> args) {
            String site = mid(m) + "@" + s.currentBCI();
            if (bc == Bytecodes.INVOKEDYNAMIC) {
                ResolvedJavaMethod impl = lambdaTarget(m, rawIndex);
                if (impl == null) {
                    return null; // the eager rule: a capture of a tracked value is a violation
                }
                String l = "N:lambda" + lambdaImpl.size() + ":" + mid(impl);
                lambdaImpl.put(l, impl);
                lambdaCaptures.put(l, List.copyOf(args));
                Set<String> caps = new LinkedHashSet<>();
                for (int i = 0; i < args.size(); i++) {
                    for (String v : args.get(i)) {
                        caps.add("store " + l + " cap" + i + " <- " + v);
                    }
                }
                pendingN.put(l, caps); // an escape of the lambda to user code is an escape of its captures
                return Set.of(l);
            }
            if (nameDesc(callee).equals("evaluate(Ljava/util/stream/TerminalOp;)Ljava/lang/Object;") && type(AP).isAssignableFrom(type(callee.getDeclaringClass().toJavaName()))) {
                return terminal(at, args);
            }
            boolean hasReceiver = bc != Bytecodes.INVOKESTATIC;
            JavaKind rk = callee.getSignature().getReturnKind();
            String name = callee.getName();
            Set<String> recv = hasReceiver ? args.get(0) : Set.of();
            if (recv.contains(DOWN)) {
                if (!recv.equals(Set.of(DOWN))) {
                    violation(at + ": the downstream mixed with other receivers " + recv);
                }
                if (name.equals("accept") && args.size() == 2 && callee.getSignature().getParameterKind(0) == JavaKind.Object) {
                    for (String v : args.get(1)) {
                        if (!ir(v)) {
                            addElem(v);
                        }
                    }
                } else if (args.subList(1, args.size()).stream().anyMatch(this::tracked) || rk == JavaKind.Object) {
                    violation(at + ": a call on the downstream that is not accept or a signal " + cid);
                }
                return Set.of();
            }
            if (!recv.isEmpty() && recv.stream().allMatch(lambdaImpl::containsKey)) {
                Set<String> out = new TreeSet<>();
                for (String l : recv) {
                    ResolvedJavaMethod impl = lambdaImpl.get(l);
                    List<Set<String>> a = new ArrayList<>(lambdaCaptures.get(l));
                    a.addAll(args.subList(1, args.size()));
                    if (impl.isConstructor()) {
                        String n = "N:" + impl.getDeclaringClass().toJavaName();
                        a.add(0, Set.of(n));
                        walk(impl, a);
                        out.add(n);
                    } else if (!impl.isStatic() && !impl.isPrivate() && !impl.isFinal() && !impl.getDeclaringClass().isFinalFlagSet()) {
                        violation(at + ": a method reference with a virtual target " + mid(impl));
                    } else {
                        out.addAll(walk(impl, a));
                    }
                }
                return out;
            }
            boolean virtual = bc == Bytecodes.INVOKEVIRTUAL || bc == Bytecodes.INVOKEINTERFACE;
            if (recv.equals(Set.of("A0")) && name.equals("wrapAndCopyInto") && !entry.isStatic() && type(AP).isAssignableFrom(entry.getDeclaringClass())) {
                // the terminal's sink over the stage's elements
                for (String k : args.get(1)) {
                    walkSink(k, Set.of("E<elem>:A0"));
                }
                return args.get(1);
            }
            if (virtual && !recv.isEmpty() && recv.stream().allMatch(l -> exactClass(l) != null && (exactClass(l).startsWith("java.util.stream.") || !pendingN.getOrDefault(l, Set.of()).isEmpty()) &&
                            !type("java.lang.Throwable").isAssignableFrom(type(exactClass(l))))) {
                // a NEW object's call (its class is exact): its implementation
                Set<String> out = new TreeSet<>();
                for (String l : recv) {
                    ResolvedJavaMethod t = concrete(exactClass(l), nameDesc(callee));
                    if (t == null) {
                        violation(at + ": no implementation of " + cid + " in " + l);
                        continue;
                    }
                    List<Set<String>> a = new ArrayList<>(args);
                    a.set(0, Set.of(l));
                    out.addAll(walk(t, a));
                }
                return out;
            }
            List<ResolvedJavaMethod> det = deterministic(callee, bc);
            if (det != null) {
                if (callee.getDeclaringClass().toJavaName().startsWith("java.util.stream.")) {
                    // the closed package's deterministic code is walked, a tracked value or not (a constructor that links a
                    // stage, a factory of stream machinery: ReduceOps.makeRefCounting, FindOps.makeRef)
                    Set<String> out = new TreeSet<>();
                    det.forEach(t -> out.addAll(walk(t, args)));
                    return out;
                }
                return null; // the eager rules (a deterministic call is walked when a value is tracked)
            }
            if (!hasReceiver || recv.isEmpty()) {
                return null;
            }
            boolean othersTracked = args.subList(1, args.size()).stream().anyMatch(this::tracked);
            if (recv.equals(Set.of("A0")) && !entry.isStatic() && type(AP).isAssignableFrom(entry.getDeclaringClass())) {
                // a call on the stage itself
                if (rk != JavaKind.Object && !othersTracked) {
                    return Set.of(); // the pipeline's own plumbing (flags, sizes, isParallel)
                }
                if (reDispatched.contains(nameDesc(callee))) {
                    return null; // a declared re-dispatch (an observed callback) / a deterministic call (walked)
                }
                Set<String> out = new TreeSet<>();
                List<ResolvedJavaMethod> impls = packageImplementations(callee);
                if (impls.isEmpty()) {
                    violation(at + ": no implementation of " + cid + " in java.util.stream");
                }
                for (ResolvedJavaMethod t : impls) {
                    out.addAll(walk(t, args));
                }
                return out;
            }
            if (recv.stream().allMatch(l -> l.endsWith("{" + AP + ".sourceSupplier}"))) {
                return Set.of(); // a supplier source: no modelled source sets it (StreamSupport.stream(Supplier, ..) is unlisted: refused by name)
            }
            if (recv.stream().allMatch(l -> l.endsWith("{" + AP + ".sourceCloseAction}"))) {
                // close()'s `sourceStage.sourceCloseAction.run()`: no modelled op sets a close
                // action (onClose / Stream.concat are unlisted in the closed package: a Runnable handed to them refuses by name,
                // and so does every value it captures), so a modelled stage's close action is null
                return Set.of();
            }
            if (recv.stream().allMatch(l -> l.endsWith("{" + AP + ".sourceSpliterator}")) && (name.equals("forEachRemaining") || name.equals("tryAdvance"))) {
                // the head's own source traversal (Head.forEach's sequential path): the head's elements to the action
                for (String a : args.get(1)) {
                    if (a.equals(DOWN)) {
                        addElem("E<elem>:A0");
                    } else if (lambdaImpl.containsKey(a) || exactClass(a) != null) {
                        lazyInvokeOn(a, "accept(Ljava/lang/Object;)V", Set.of("E<elem>:A0"), at);
                    } else if (a.matches(ARG)) {
                        result.observed.add("call java.util.function.Consumer#accept(Ljava/lang/Object;)V on " + a + " E<elem>:A0 @ " + SOURCE_SITE);
                    } else {
                        violation(at + ": a source traversal with the action " + a);
                    }
                }
                return Set.of();
            }
            // a callback: a sink handed on is the op's sink S
            Signature sig = callee.getSignature();
            for (int i = 1; i < args.size(); i++) {
                Set<String> a = args.get(i);
                if (a.contains(DOWN)) {
                    addElem("S");
                    Set<String> b = new TreeSet<>(a);
                    b.remove(DOWN);
                    b.add("S");
                    args.set(i, b);
                }
                for (String l : List.copyOf(args.get(i))) {
                    String c = exactClass(l);
                    if (l.equals("A0") && !entry.isStatic() && consumerSelf(entry.getDeclaringClass())) {
                        c = entry.getDeclaringClass().toJavaName(); // the entry's own object handed on as a consumer (Spliterators$1Adapter)
                    }
                    if (c != null && (c.startsWith("java.util.stream.") || l.equals("A0")) && samOf(sig.getParameterType(i - 1, null).getName()) != null &&
                                    type(sig.getParameterType(i - 1, null).toJavaName()).isAssignableFrom(type(c))) {
                        // a JDK sink / consumer object handed on as a functional argument: its functional method over S
                        String sam = samOf(sig.getParameterType(i - 1, null).getName());
                        if (sam == null) {
                            violation(at + ": a sink handed on as a non-functional argument " + l);
                            continue;
                        }
                        ResolvedJavaMethod t = concrete(c, sam);
                        if (t == null) {
                            violation(at + ": no " + sam + " in " + c);
                            continue;
                        }
                        walk(t, List.of(Set.of(l), Set.of("S")));
                        Set<String> b = new TreeSet<>(args.get(i));
                        b.remove(l);
                        b.add("S");
                        args.set(i, b);
                    }
                }
            }
            if (!args.subList(1, args.size()).stream().anyMatch(this::tracked) && rk != JavaKind.Object && !nameDesc(callee).equals("getClass()Ljava/lang/Class;") &&
                            recv.stream().noneMatch(l -> mayBeString(l) || userObject(l))) {
                // the receiver only, no reference result, on a JDK-internal receiver (the stage's / terminal's own
                // bookkeeping): no tracked value in or out. Not on an element, an argument or a
                // callback result that may be a String or a user object (e.length(), e.hashCode(), a user spliterator's
                // estimateSize): there the call is a usage or user code, so the table must declare it (a callback)
                return Set.of();
            }
            return null; // the eager rules (a callback)
        }

        /** A SAM call {@code nameDesc} on a lambda / an exact NEW object {@code l} with argument {@code v}. */
        void lazyInvokeOn(String l, String nameDesc, Set<String> v, String at) {
            if (lambdaImpl.containsKey(l)) {
                List<Set<String>> a = new ArrayList<>(lambdaCaptures.get(l));
                a.add(v);
                walk(lambdaImpl.get(l), a);
                return;
            }
            ResolvedJavaMethod t = concrete(exactClass(l), nameDesc);
            if (t == null) {
                violation(at + ": no " + nameDesc + " in " + l);
                return;
            }
            walk(t, List.of(Set.of(l), v));
        }

        /** {@code t} (a java.* class) has no subclass in its package: its object is exactly it (a local class: Spliterators$1Adapter). */
        boolean consumerSelf(ResolvedJavaType t) {
            String cn = t.toJavaName();
            if (!cn.startsWith("java.")) {
                return false;
            }
            for (String c : packageClasses(cn.substring(0, cn.lastIndexOf('.')))) {
                if (!c.equals(cn)) {
                    try {
                        if (t.isAssignableFrom(type(c))) {
                            return false;
                        }
                    } catch (Throwable x) {
                        // not loadable here
                    }
                }
            }
            return true;
        }

        @Override
        Set<String> lazyStatic(JavaField fld) {
            String k = STATIC_TERMINALS.get(qn(fld));
            return k == null ? null : Set.of("T:" + k);
        }

        /** The single abstract method of the interface with descriptor {@code desc} (null: none or several). */
        String samOf(String desc) {
            if (!desc.startsWith("L")) {
                return null;
            }
            ResolvedJavaType t = type(desc.substring(1, desc.length() - 1).replace('/', '.'));
            String out = null;
            for (ResolvedJavaMethod d : t.getDeclaredMethods(false)) {
                if (d.isAbstract()) {
                    if (out != null) {
                        return null;
                    }
                    out = nameDesc(d);
                }
            }
            return out;
        }

        /** Every implementation of the virtual {@code callee} in java.util.stream (the closed package). */
        List<ResolvedJavaMethod> packageImplementations(JavaMethod callee) {
            ResolvedJavaType holder = type(callee.getDeclaringClass().toJavaName());
            List<ResolvedJavaMethod> out = new ArrayList<>();
            for (String c : packageClasses("java.util.stream")) {
                ResolvedJavaType t;
                try {
                    t = type(c);
                } catch (Throwable x) {
                    continue;
                }
                if (!t.isInterface() && holder.isAssignableFrom(t)) {
                    ResolvedJavaMethod d = declared(t, nameDesc(callee));
                    if (d != null && !d.isAbstract() && !d.isStatic()) {
                        out.add(d);
                    }
                }
            }
            return out;
        }

        /** (3): {@code evaluate(op)} on the stage: the op's sequential evaluation (its sink over the stage's elements). */
        Set<String> terminal(String at, List<Set<String>> args) {
            Set<String> out = new TreeSet<>();
            if (!args.get(0).equals(Set.of("A0"))) {
                violation(at + ": a terminal evaluated on " + args.get(0));
                return out;
            }
            for (String t : args.get(1)) {
                if (t.startsWith("T:")) {
                    // a static terminal op (reviewed): its sink class
                    String k = "N:" + t.substring(2);
                    walkSink(k, Set.of("E<elem>:A0"));
                    out.addAll(walkIf(t.substring(2), "get()Ljava/lang/Object;", List.of(Set.of(k))));
                    continue;
                }
                String c = exactClass(t);
                if (c == null) {
                    violation(at + ": a terminal op of an unknown class " + t);
                    continue;
                }
                walkIf(c, "getOpFlags()I", List.of(Set.of(t)));
                ResolvedJavaMethod es = concrete(c, "evaluateSequential(Ljava/util/stream/PipelineHelper;Ljava/util/Spliterator;)Ljava/lang/Object;");
                if (es == null) {
                    violation(at + ": no evaluateSequential in " + c);
                    continue;
                }
                out.addAll(walk(es, List.of(Set.of(t), Set.of("A0"), Set.of())));
            }
            if (args.get(1).isEmpty()) {
                violation(at + ": an untracked terminal op");
            }
            return out;
        }

        /** The entry's observed effects that no declared effect covers (the lazy vocabulary: a FRESH temp's slot = its stores). */
        List<String> lazyUncovered() {
            Set<String> allowed = Result.allowed(op, this::lazyLabels);
            List<String> out = new ArrayList<>();
            for (String o : result.observed) {
                if (allowed.contains(o) || op.resultIr() && (o.matches("result I\\d+") || o.startsWith("result N:"))) {
                    continue;
                }
                if (equivalent(o, allowed) || untrackedArgCovered(o, allowed)) {
                    continue;
                }
                out.add(op.method() + ": undeclared effect `" + o + "`");
            }
            return out;
        }

        /**
         * An observed callback whose untracked arguments ({@code _}: no value of the entry, e.g. a sink state read before its
         * first store) are covered by a declared callback with any operands there: nothing flows at such a position.
         */
        boolean untrackedArgCovered(String o, Set<String> allowed) {
            if (!o.startsWith("call ") || !o.contains(" _")) {
                return false;
            }
            int at = o.lastIndexOf(" @ ");
            String[] w = o.substring(0, at).split(" ");
            StringBuilder re = new StringBuilder();
            for (int i = 0; i < w.length; i++) {
                re.append(i == 0 ? "" : " ").append(i >= 4 && w[i].equals("_") ? "\\S+" : java.util.regex.Pattern.quote(w[i]));
            }
            re.append(java.util.regex.Pattern.quote(o.substring(at)));
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(re.toString());
            return allowed.stream().anyMatch(a -> p.matcher(a).matches());
        }

        /** A reviewed equivalence ({@link #LAZY_EQUIVALENT}) covers the observed call {@code o}. */
        boolean equivalent(String o, Set<String> allowed) {
            if (!o.startsWith("call ")) {
                return false;
            }
            int on = o.indexOf(" on ");
            int at = o.lastIndexOf(" @ ");
            String cb = o.substring(5, on);
            String mid = o.substring(on, at);
            String site = o.substring(at + 3);
            for (String[] eq : LAZY_EQUIVALENT) {
                if (!eq[0].equals(cb) || !site.startsWith(eq[1])) {
                    continue;
                }
                for (JdkModels.Effect e : op.effects()) {
                    if (e instanceof JdkModels.Callback c && c.cb().equals(eq[2])) {
                        for (String s : c.sites()) {
                            if (allowed.contains("call " + eq[2] + mid + " @ " + s)) {
                                return true;
                            }
                        }
                    }
                }
            }
            return false;
        }

        /** The labels of {@code r}; a FRESH temp's slot ({@code $k.<elem>}, a named intermediate value) = the values the op stores there. */
        List<String> lazyLabels(JdkModels.Op o, JdkModels.Ref r) {
            return lazyLabels(o, r, new HashSet<>());
        }

        private List<String> lazyLabels(JdkModels.Op o, JdkModels.Ref r, Set<JdkModels.Ref> seen) {
            if (JdkModels.Ref.isTemp(r.slot()) && r.members().size() == 1 && JdkModels.slot(r.members().get(0)) != null &&
                            o.tempBinder(JdkModels.Ref.tempIndex(r.slot())) instanceof JdkModels.Fresh && seen.add(r)) {
                List<String> out = new ArrayList<>();
                for (JdkModels.Effect e : o.effects()) {
                    if (e instanceof JdkModels.Store st && st.a().slot() == r.slot() && st.a().members().isEmpty() && st.member().equals(r.members().get(0))) {
                        out.addAll(lazyLabels(o, st.v(), seen));
                    }
                }
                return out;
            }
            return Result.labels(o, r);
        }
    }

    /** The lazy premise of one F4 entry: its violations and undeclared effects. */
    private List<String> lazyPremise(JdkModels.Op op) {
        LazyChecker c = new LazyChecker(op);
        Result r = c.check(method(op.method()), op);
        List<String> out = new ArrayList<>(r.violations);
        out.addAll(c.lazyUncovered());
        System.out.println("[jdkmodel-lazy-premise] " + op.method() + " observed=" + r.observed + " violations=" + r.violations);
        return out;
    }

    /**
     * Modelling standard (a) for a lazy family: every F4 entry over-approximates the JDK code that runs for it, the
     * op method composed with the stage's sink or the terminal's evaluation ({@link LazyChecker}); the entries of {@link
     * #LAZY_REVIEWED} are reviewed instead (their reasons stated).
     */
    @Test
    public void everyLazyEntryOverApproximatesTheJdkCode() {
        List<String> failures = new ArrayList<>();
        int checked = 0;
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (!f.lazy) {
                continue;
            }
            for (JdkModels.Op op : f.table.values()) {
                if (LAZY_REVIEWED.containsKey(op.method())) {
                    continue;
                }
                checked++;
                failures.addAll(lazyPremise(op));
            }
        }
        Assert.assertTrue("checked lazy entries: " + checked, checked >= 40);
        Assert.assertTrue("lazy premise failures: " + failures, failures.isEmpty());
        for (String m : LAZY_REVIEWED.keySet()) {
            Assert.assertNotNull("a reviewed lazy entry exists: " + m, JdkModels.F4.table.values().stream().filter(x -> x.method().equals(m)).findFirst().orElse(null));
        }
    }

    /**
     * Every callback site of a lazy family is a real invoke of the callback's name and descriptor (the engine's
     * {@code sitesOf} check, statically).
     */
    @Test
    public void everyLazySiteIsARealInvoke() {
        List<String> failures = new ArrayList<>();
        int sites = 0;
        for (JdkModels.Family f : JdkModels.FAMILIES) {
            if (!f.lazy) {
                continue;
            }
            for (JdkModels.Op op : f.table.values()) {
                for (JdkModels.Effect e : op.effects()) {
                    if (e instanceof JdkModels.Callback c) {
                        for (String site : c.sites()) {
                            sites++;
                            String at = invokeAt(site);
                            if (!c.cb().substring(c.cb().indexOf('#') + 1).equals(at)) {
                                failures.add(op.method() + ": the site " + site + " of " + c.cb() + " invokes " + at);
                            } else if (!type(c.cb().substring(0, c.cb().indexOf('#'))).isAssignableFrom(invokeHolderAt(site))) {
                                // the engine's sitesOf class guard, statically
                                failures.add(op.method() + ": the site " + site + " of " + c.cb() + " invokes it on " + invokeHolderAt(site).toJavaName());
                            }
                        }
                    }
                }
            }
        }
        Assert.assertTrue("sites: " + sites, sites > 40);
        Assert.assertTrue("site failures: " + failures, failures.isEmpty());
    }

    /** The symbolic holder of the invoke at {@code site} (an invoke there: checked by {@link #invokeAt}). */
    private ResolvedJavaType invokeHolderAt(String site) {
        ResolvedJavaMethod m = method(JdkModels.Effect.siteMethod(site));
        BytecodeStream s = new BytecodeStream(m.getCode());
        s.setBCI(JdkModels.Effect.siteBci(site));
        return type(m.getConstantPool().lookupMethod(s.readCPI(), s.currentBC(), m).getDeclaringClass().toJavaName());
    }

    /** The name and descriptor of the method invoked at {@code site} ("holder#name(desc)@bci"), or a description of what is there. */
    private String invokeAt(String site) {
        ResolvedJavaMethod m = method(JdkModels.Effect.siteMethod(site));
        int bci = JdkModels.Effect.siteBci(site);
        BytecodeStream s = new BytecodeStream(m.getCode());
        for (s.setBCI(0); s.currentBCI() < m.getCodeSize(); s.next()) {
            if (s.currentBCI() == bci) {
                int bc = s.currentBC();
                if (bc != Bytecodes.INVOKEVIRTUAL && bc != Bytecodes.INVOKEINTERFACE && bc != Bytecodes.INVOKESPECIAL && bc != Bytecodes.INVOKESTATIC) {
                    return "no invoke (" + Bytecodes.nameOf(bc) + ")";
                }
                return nameDesc(m.getConstantPool().lookupMethod(s.readCPI(), bc, m));
            }
            if (s.currentBCI() > bci) {
                break;
            }
        }
        return "no instruction at " + bci;
    }

    /** The lazy premise catches real F4 entries with an effect dropped or wrong (table mutations), and passes the real ones. */
    @Test
    public void lazyCheckerCatchesTableMutations() {
        String rp = "java.util.stream.ReferencePipeline";
        String o = "Ljava/lang/Object;";
        String st = "Ljava/util/stream/Stream;";
        String filterSite = " @ " + rp + "$2$1#accept(" + o + ")V@5";
        assertLazyCaught(rp + "#filter(Ljava/util/function/Predicate;)" + st + " : fresh " + rp + "$2 ; store R <elem> 0.<elem>", "filter without its predicate callback");
        assertLazyCaught(rp + "#filter(Ljava/util/function/Predicate;)" + st + " : call 1 java.util.function.Predicate#test(" + o + ")Z 0.<elem>" + filterSite + " ; fresh " + rp + "$2",
                        "filter without its elements");
        assertLazyCaught(rp + "#map(Ljava/util/function/Function;)" + st + " : call 1 java.util.function.Function#apply(" + o + ")" + o + " 0.<elem> -> $1 @ " + rp + "$3$1#accept(" + o +
                        ")V@9 ; fresh " + rp + "$3 ; store R <elem> 0.<elem>", "map storing the upstream's elements instead of the mapper's results");
        assertLazyCaught(rp + "#peek(Ljava/util/function/Consumer;)" + st + " : call 1 java.util.function.Consumer#accept(" + o + ")V _ @ " + rp + "$15$1#accept(" + o + ")V@5 ; fresh " + rp +
                        "$15 ; store R <elem> 0.<elem>", "peek without the element argument");
        assertLazyCaught(rp + "#forEach(Ljava/util/function/Consumer;)V : observe 0 ; observe 1", "forEach without its consumer callback");
        assertLazyCaught(rp + "#anyMatch(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(" + o + ")Z 0.<elem> @ java.util.stream.MatchOps$1MatchSink#accept(" + o + ")V@13",
                        "anyMatch at a wrong site");
        assertLazyCaught(rp + "#findFirst()Ljava/util/Optional; : fresh java.util.Optional", "findFirst without the element in the Optional");
        assertLazyCaught("java.util.Arrays#stream([" + o + ")" + st + " : fresh " + rp + "$Head ; store R <elem> 0", "Arrays.stream storing the array instead of its elements");
        assertLazyCaught("java.util.Collection#stream()" + st + " : call 0 java.util.Collection#spliterator()Ljava/util/Spliterator; -> $1 @ java.util.Collection#stream()" + st +
                        "@1 ; call $1 java.util.Spliterator#getComparator()Ljava/util/Comparator; @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@14 ; fresh " + rp +
                        "$Head ; call $1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S @ " + AP +
                        "#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@32 ; store R <elem> S",
                        "Collection.stream without the short-circuit traversal (tryAdvance)");
        String red = rp + "#reduce(Ljava/util/function/BinaryOperator;)Ljava/util/Optional; : fresh java.lang.Object -> $1 ; store $1 <elem> 0.<elem>" +
                        " ; call 1 java.util.function.BinaryOperator#apply(" + o + o + ")" + o + " $1.<elem> $1.<elem> -> $2 @ java.util.stream.ReduceOps$2ReducingSink#accept(" + o + ")V@30" +
                        " ; fresh java.util.Optional ; store R java.util.Optional.value $1.<elem>";
        assertLazyCaught(red, "reduce(op) without the accumulated results in the box");
        assertLazyCaught(rp + "#collect(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BiConsumer;)" + o + " : call 1 java.util.function.Supplier#get()" + o +
                        " -> $1 @ java.util.stream.ReduceOps$4ReducingSink#begin(J)V@5 ; call 2 java.util.function.BiConsumer#accept(" + o + o +
                        ")V $1 0.<elem> @ java.util.stream.ReduceOps$4ReducingSink#accept(" + o +
                        ")V@9 ; alias $1", "collect(s, a, c) without its combiner callback");
        // a receiver-only primitive call on a user object (the source spliterator, a collector's
        // characteristics set) is not "no effect": the real entries without those callbacks are caught
        assertLazyCaught(familyLine(JdkModels.F4, "java.util.Collection#stream()" + st, x -> !x.contains("getExactSizeIfKnown"), x -> x),
                        "Collection.stream without the source spliterator's getExactSizeIfKnown");
        assertLazyCaught(familyLine(JdkModels.F4, rp + "#collect(Ljava/util/stream/Collector;)" + o, x -> !x.contains("java.util.Set#contains"), x -> x),
                        "collect(Collector) without the characteristics set's contains");
        // the real entries pass (the controls of the mutations above)
        for (String m : List.of(rp + "#filter(Ljava/util/function/Predicate;)" + st, rp + "#map(Ljava/util/function/Function;)" + st, rp + "#forEach(Ljava/util/function/Consumer;)V",
                        rp + "#findFirst()Ljava/util/Optional;", "java.util.Collection#stream()" + st, rp + "#reduce(Ljava/util/function/BinaryOperator;)Ljava/util/Optional;")) {
            JdkModels.Op real = JdkModels.F4.table.values().stream().filter(x -> x.method().equals(m)).findFirst().orElseThrow();
            List<String> f = lazyPremise(real);
            Assert.assertTrue("the real entry passes: " + m + " " + f, f.isEmpty());
        }
    }

    /**
     * A class check is explicit in every family (a callback on the value does not cover it):
     * F1's {@code ArrayList.equals(o)} ({@code o.getClass() == ArrayList.class} at @22) without its {@code classcheck} is caught,
     * the real entry passes.
     */
    @Test
    public void classChecksAreExplicitInEveryFamily() {
        String eq = "java.util.ArrayList#equals(Ljava/lang/Object;)Z";
        assertPasses(JdkModels.F1, familyLine(JdkModels.F1, eq, x -> true, x -> x));
        assertCaught(JdkModels.F1, familyLine(JdkModels.F1, eq, x -> !x.startsWith("classcheck"), x -> x), "ArrayList.equals without the argument's class check");
    }

    private void assertLazyCaught(String line, String what) {
        List<String> f = lazyPremise(JdkModels.parse(JdkModels.F4, line));
        Assert.assertFalse("the lazy checker catches: " + what, f.isEmpty());
    }
}
