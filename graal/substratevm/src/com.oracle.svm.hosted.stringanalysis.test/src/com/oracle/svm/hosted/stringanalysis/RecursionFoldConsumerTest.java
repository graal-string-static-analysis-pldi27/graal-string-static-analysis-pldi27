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

import java.io.File;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.bytecode.BytecodeStream;
import jdk.graal.compiler.bytecode.Bytecodes;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.JavaField;
import jdk.vm.ci.meta.JavaMethod;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Recursion folding, the premise of the fold-link invariant:
 * every reader of a call-path link's fields ({@code CallPath.callerFrame/call/callerMctx/next}) and every reader of a
 * fold's fields ({@code FoldInfo.root/rootMctx/owner}) outside {@code ContextPolicy$CallPath} itself is on the
 * {@link #AUDITED} list: each one handles a fold link explicitly or is fail-safe on it (refuses or widens, never ends
 * silently). A bytecode scan over every class of the package (lambdas included) finds them; a new or moved reader fails
 * until it is audited and listed, and a listed reader that disappeared fails too.

 * Also: the only caller of {@code CallPath.foldPush} is {@code RecursiveTracking.foldedPush}, and the only
 * creator of a {@code FoldInfo} is {@code foldPush} (no fold link exists with the knob at 0).
 */
@AddExports({"jdk.graal.compiler/jdk.graal.compiler.api.replacements",
                "jdk.graal.compiler/jdk.graal.compiler.bytecode",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.memory",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.graph.iterators",
                "jdk.graal.compiler/jdk.graal.compiler.graph.spi",
                "jdk.graal.compiler/jdk.graal.compiler.java",
                "jdk.graal.compiler/jdk.graal.compiler.lir.gen",
                "jdk.graal.compiler/jdk.graal.compiler.nodeinfo",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.cfg",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.debug",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.memory.address",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.type",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.virtual",
                "jdk.graal.compiler/jdk.graal.compiler.options",
                "jdk.graal.compiler/jdk.graal.compiler.phases",
                "jdk.graal.compiler/jdk.graal.compiler.phases.common.util",
                "jdk.graal.compiler/jdk.graal.compiler.phases.tiers",
                "jdk.graal.compiler/jdk.graal.compiler.replacements.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.word",
                "jdk.internal.vm.ci/jdk.vm.ci.code",
                "jdk.internal.vm.ci/jdk.vm.ci.common",
                "jdk.internal.vm.ci/jdk.vm.ci.hotspot",
                "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.internal.vm.ci/jdk.vm.ci.runtime",
                "org.graalvm.nativeimage/org.graalvm.nativeimage.impl"})
public class RecursionFoldConsumerTest {

    private static final String PKG = "com/oracle/svm/hosted/stringanalysis/";
    private static final String CALLPATH = "Lcom/oracle/svm/hosted/stringanalysis/ContextPolicy$CallPath;";
    private static final String FOLDINFO = "Lcom/oracle/svm/hosted/stringanalysis/ContextPolicy$FoldInfo;";

    /**
     * The audited readers: {@code SimpleClassName#method field}. Lambda method names are compiler-chosen
     * ({@code lambda$name$N}); a reader inside a lambda is listed with the {@code lambda$<enclosing>} prefix only.
     */
    static final Set<String> AUDITED = new TreeSet<>(List.of(
                    // --- real fold handling ---
                    "RecursiveTracking#returnCase call", // fold check before the matched return (returnAlongFold)
                    "RecursiveTracking#returnCase callerFrame",
                    "RecursiveTracking#returnCase callerMctx",
                    "RecursiveTracking#returnCase next",
                    "ObjectIdentityRule#returnAtEntry call", // ownerCont (shared with the identity rule): fold check first
                    "ObjectIdentityRule#returnAtEntry callerFrame",
                    "ObjectIdentityRule#returnAtEntry callerMctx",
                    "ObjectIdentityRule#returnAtEntry next",
                    "ObjectIdentityRule#lambda$idParameter callerFrame", // parameter entries: a fold entry takes the fan first
                    "ObjectIdentityRule#lambda$idParameter callerMctx",
                    "ObjectIdentityRule#lambda$idParameter next",
                    "ObjectReturnRule#lambda$objretParameter callerFrame", // the named parameter delivery, as idParameter (a fold entry takes the fan first)
                    "ObjectReturnRule#lambda$objretParameter callerMctx",
                    "ObjectReturnRule#lambda$objretParameter next",
                    "RecursiveTracking#returnAlongFold next", // the root exit through F.next
                    "RecursiveTracking#returnAlongFold root",
                    "RecursiveTracking#returnAlongFold rootMctx",
                    "RecursiveTracking#returnAlongFold owner",
                    "RecursiveTracking#foldedPush root",
                    "RecursiveTracking#foldedPush owner",
                    "RecursiveTracking#parameterIndexCase callerFrame", // backward under F: path-less (the fan)
                    "RecursiveTracking#parameterIndexCase callerMctx",
                    "RecursiveTracking#parameterIndexCase next",
                    // --- fail-safe on a fold link (callerFrame null, call a FoldInfo) ---
                    "RecursiveTracking#invokesOf call", // -> invokesOfCall: [] -> MISSING_IR / UNRESOLVED_VALUE
                    "RecursiveTracking#invokesOf callerFrame",
                    "RecursiveTracking#beltOk call", // a non-vertex call: true; unreachable for F (parameterIndexCase)
                    "RecursiveTracking#beltOk callerFrame",
                    "RecursiveTracking#argumentsAt call", // not a DesugaredCall -> invokesOf -> [] -> UNRESOLVED_VALUE
                    "RecursiveTracking#contextsAndMint call", // F: callElementOf null -> mergeMint (widens)
                    "ObjectIdentityRule#idContraCheck call", // census only: a non-vertex (fold) entry is counted unchecked
                    "ObjectIdentityRule#idContraCheck callerFrame",
                    "ObjectIdentityRule#entryLabel call", // census only: a fold entry is labelled "fold", never followed
                    "ObjectIdentityRule#entryLabel callerFrame",
                    "RecursiveTracking#extendChainFromPath call", // DUMP text only
                    "RecursiveTracking#extendChainFromPath callerFrame",
                    "RecursiveTracking#extendChainFromPath callerMctx",
                    "RecursiveTracking#extendChainFromPath next",
                    "RecursiveTracking#extendChain next", // callElementOf(F) null -> returns own (no completion)
                    "RecursiveTracking#unknownOwnerTail callerFrame", // callElementOf(F) null -> null (= path-less)
                    "RecursiveTracking#unknownOwnerTail next",
                    "RecursiveTracking#invocationCtx callerFrame", // null frame -> UNKNOWN (widens)
                    "RecursiveTracking#invocationCtx callerMctx",
                    "RecursiveTracking#invocationCtx next",
                    "RecursiveTracking#invocationCtx call",
                    "RecursiveTracking#callElementOf call", // FoldInfo -> null
                    "RecursiveTracking#callElementOf callerFrame",
                    "JdkModelEngine#returnArrival call", // not a ModelCall -> false (falls through to returnCase's fold rule)
                    "JdkModelEngine#returnArrival callerMctx",
                    "JdkModelEngine#returnArrival next",
                    "JdkModelEngine#parameterCase call", // not a ModelCall -> false (unreachable for F: path-less first)
                    "JdkModelEngine#parameterCase callerFrame",
                    "JdkModelEngine#parameterCase callerMctx",
                    "JdkModelEngine#parameterCase next"));

    private static MetaAccessProvider metaAccess;

    private static MetaAccessProvider meta() {
        if (metaAccess == null) {
            metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();
        }
        return metaAccess;
    }

    /** Every class name of the package, from RecursiveTracking's code source (a jar or a class directory). */
    static List<String> packageClasses() throws Exception {
        URI src = RecursiveTracking.class.getProtectionDomain().getCodeSource().getLocation().toURI();
        File loc = new File(src);
        List<String> out = new ArrayList<>();
        if (loc.isDirectory()) {
            Path dir = Paths.get(loc.getPath(), PKG);
            try (Stream<Path> s = Files.list(dir)) {
                s.map(p -> p.getFileName().toString()).filter(n -> n.endsWith(".class")).forEach(n -> out.add(n.substring(0, n.length() - 6)));
            }
        } else {
            try (JarFile jf = new JarFile(loc)) {
                Enumeration<JarEntry> en = jf.entries();
                while (en.hasMoreElements()) {
                    String n = en.nextElement().getName();
                    if (n.startsWith(PKG) && n.endsWith(".class") && n.indexOf('/', PKG.length()) < 0) {
                        out.add(n.substring(PKG.length(), n.length() - 6));
                    }
                }
            }
        }
        return out;
    }

    private record Scan(Set<String> readers, Set<String> foldPushCallers, Set<String> foldInfoCreators) {
    }

    private static Scan scan() throws Exception {
        Set<String> readers = new TreeSet<>();
        Set<String> callers = new TreeSet<>();
        Set<String> creators = new TreeSet<>();
        List<String> classes = packageClasses();
        Assert.assertTrue("the package enumeration found the engine classes: " + classes.size(), classes.contains("RecursiveTracking") && classes.size() > 50);
        int scanned = 0;
        for (String cn : classes) {
            // a class reading a CallPath/FoldInfo field (or calling foldPush / FoldInfo.of) names the class in its
            // constant pool; the others are skipped unloaded (some plugin classes cannot be linked in the test VM)
            byte[] bytes;
            try (java.io.InputStream in = RecursiveTracking.class.getClassLoader().getResourceAsStream(PKG + cn + ".class")) {
                Assert.assertNotNull("class file of " + cn, in);
                bytes = in.readAllBytes();
            }
            String text = new String(bytes, java.nio.charset.StandardCharsets.ISO_8859_1);
            if (!text.contains("ContextPolicy$CallPath") && !text.contains("ContextPolicy$FoldInfo")) {
                continue;
            }
            scanned++;
            Class<?> c = Class.forName("com.oracle.svm.hosted.stringanalysis." + cn.replace('/', '.'), false, RecursiveTracking.class.getClassLoader());
            ResolvedJavaType t = meta().lookupJavaType(c);
            List<ResolvedJavaMethod> ms = new ArrayList<>(List.of(t.getDeclaredMethods()));
            ms.addAll(List.of(t.getDeclaredConstructors()));
            if (t.getClassInitializer() != null) {
                ms.add(t.getClassInitializer());
            }
            String simple = cn.substring(cn.lastIndexOf('$') + 1);
            String owner = cn.contains("$") ? cn : simple;
            for (ResolvedJavaMethod m : ms) {
                byte[] code = m.getCode();
                if (code == null) {
                    continue;
                }
                String mname = m.getName();
                if (mname.startsWith("lambda$")) {
                    int e = mname.indexOf('$', 7);
                    mname = "lambda$" + (e > 0 ? mname.substring(7, e) : mname.substring(7));
                }
                BytecodeStream s = new BytecodeStream(code);
                while (s.currentBC() != Bytecodes.END) {
                    int bc = s.currentBC();
                    if (bc == Bytecodes.GETFIELD) {
                        JavaField f = m.getConstantPool().lookupField(s.readCPI(), m, Bytecodes.GETFIELD);
                        String holder = f.getDeclaringClass().getName();
                        if ((holder.equals(CALLPATH) || holder.equals(FOLDINFO)) && !cn.equals("ContextPolicy$CallPath") && !cn.equals("ContextPolicy$FoldInfo")) {
                            readers.add(owner + "#" + mname + " " + f.getName());
                        }
                    } else if (bc == Bytecodes.INVOKESTATIC || bc == Bytecodes.INVOKESPECIAL) {
                        JavaMethod tm = m.getConstantPool().lookupMethod(s.readCPI(), bc, m);
                        String holder = tm.getDeclaringClass().getName();
                        if (holder.equals(CALLPATH) && tm.getName().equals("foldPush")) {
                            callers.add(owner + "#" + mname);
                        }
                        if (holder.equals(FOLDINFO) && (tm.getName().equals("of") || tm.getName().equals("<init>"))) {
                            creators.add(owner + "#" + mname);
                        }
                    }
                    s.next();
                }
            }
        }
        Assert.assertTrue("the engine classes were scanned: " + scanned, scanned >= 4);
        return new Scan(readers, callers, creators);
    }

    @Test
    public void everyPathReaderIsAudited() throws Exception {
        Scan sc = scan();
        Set<String> unaudited = new TreeSet<>(sc.readers());
        unaudited.removeAll(AUDITED);
        Set<String> gone = new TreeSet<>(AUDITED);
        gone.removeAll(sc.readers());
        if (Boolean.getBoolean("c95.recfold.print")) {
            sc.readers().forEach(r -> System.out.println("[recfold-reader] " + r));
        }
        Assert.assertTrue("unaudited CallPath/FoldInfo readers (audit each for a fold link, then list it): " + unaudited, unaudited.isEmpty());
        Assert.assertTrue("audited readers no longer present (keep the list exact): " + gone, gone.isEmpty());
    }

    @Test
    public void foldsAreCreatedOnlyBehindTheKnob() throws Exception {
        Scan sc = scan();
        Assert.assertEquals("the only caller of CallPath.foldPush is the crossing helper", Set.of("RecursiveTracking#foldedPush"), sc.foldPushCallers());
        Assert.assertEquals("a FoldInfo is created only by foldPush (and its intern)", Set.of("ContextPolicy$CallPath#foldPush", "ContextPolicy$FoldInfo#lambda$of"),
                        sc.foldInfoCreators());
    }
}
