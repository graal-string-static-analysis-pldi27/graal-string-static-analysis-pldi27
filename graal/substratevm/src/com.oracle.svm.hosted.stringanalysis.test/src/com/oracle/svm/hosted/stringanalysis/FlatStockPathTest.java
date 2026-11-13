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
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.reflect.Constructor;
import java.lang.reflect.Proxy;
import java.net.JarURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
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
import org.junit.BeforeClass;
import org.junit.Test;

import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.graphbuilderconf.GraphBuilderContext;
import jdk.graal.compiler.nodes.graphbuilderconf.NodePlugin;
import jdk.vm.ci.meta.ResolvedJavaMethod;

import com.oracle.svm.util.ModuleSupport;

/**
 * Flat stock path: the inline cache's flat {@code String.<m>} call is
 * re-parsed through the parser's own invoke path, so every string-analysis node plugin must decline that re-entry
 * (otherwise a plugin would lower the same invoke twice, or recurse). Pins: (1) every string-analysis NodePlugin that
 * any class of the image builder registers ({@code Plugins.appendNodePlugin/prependNodePlugin}; the whole builder code
 * source is scanned) starts its {@code handleInvoke} with the {@code isFlatReentry} check; (2) behaviour:
 * inside a flat re-entry of {@code (b, m)} each such plugin returns false for {@code (b, m)} without touching the
 * parser context or the method (it steps aside); (3) the knob default is the fix (1, not the CHECK mode 2).
 */
public class FlatStockPathTest {

    /**
     * Some plugin constructors make {@code String.value} accessible; open {@code java.lang} to their module here, so
     * the test does not depend on an earlier test of the run having done so (e.g. through {@code ReflectionUtil}).
     */
    @BeforeClass
    public static void openJavaLang() {
        ModuleSupport.accessModuleByClass(ModuleSupport.Access.OPEN, StringLengthNodePlugin.class, String.class);
    }

    private static final String PKG = "com/oracle/svm/hosted/stringanalysis/";
    private static final String GUARD_OWNER = PKG + "InlineCacheTrivialMethodNodePlugin";
    private static final String PLUGINS = "jdk/graal/compiler/nodes/graphbuilderconf/GraphBuilderConfiguration$Plugins";

    private static ClassModel model(String internalName) throws IOException {
        try (InputStream in = FlatStockPathTest.class.getResourceAsStream("/" + internalName + ".class")) {
            Assert.assertNotNull("class file of " + internalName, in);
            return ClassFile.of().parse(in.readAllBytes());
        }
    }

    /** Every class file (bytes) of the code source that holds the string-analysis package (the image builder). */
    private static List<byte[]> builderClassFiles() throws Exception {
        URL u = FlatStockPathTest.class.getResource("/" + GUARD_OWNER + ".class");
        Assert.assertNotNull(u);
        List<byte[]> out = new ArrayList<>();
        if (u.getProtocol().equals("jar")) {
            JarURLConnection c = (JarURLConnection) u.openConnection();
            c.setUseCaches(false);
            try (JarFile jar = new JarFile(Paths.get(c.getJarFileURL().toURI()).toFile())) {
                for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements();) {
                    JarEntry je = e.nextElement();
                    if (je.getName().endsWith(".class")) {
                        try (InputStream in = jar.getInputStream(je)) {
                            out.add(in.readAllBytes());
                        }
                    }
                }
            }
        } else if (u.getProtocol().equals("file")) {
            Path self = Paths.get(u.toURI());
            Path root = self;
            for (int i = 0; i < GUARD_OWNER.split("/").length; i++) {
                root = root.getParent();
            }
            try (Stream<Path> files = Files.walk(root)) {
                for (Path f : (Iterable<Path>) files.filter(f -> f.toString().endsWith(".class"))::iterator) {
                    out.add(Files.readAllBytes(f));
                }
            }
        } else {
            Assert.fail("unsupported code source of the builder classes: " + u);
        }
        Assert.assertTrue("the builder code source has many classes: " + u, out.size() > 1000);
        return out;
    }

    private static boolean contains(byte[] haystack, byte[] needle) {
        outer: for (int i = 0; i + needle.length <= haystack.length; i++) {
            for (int j = 0; j < needle.length; j++) {
                if (haystack[i + j] != needle[j]) {
                    continue outer;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * The string-analysis NodePlugin classes instantiated in any builder method that registers node plugins: a method
     * calling {@code Plugins.appendNodePlugin} or {@code prependNodePlugin}, anywhere in the builder (not only the
     * feature and the length registration). A string-analysis plugin is one in the string-analysis package or one
     * whose name contains {@code StringAnalysis}.
     */
    private static Set<String> registeredNodePlugins(Set<String> registrars) throws Exception {
        Set<String> out = new TreeSet<>();
        byte[] append = "appendNodePlugin".getBytes(StandardCharsets.UTF_8);
        byte[] prepend = "prependNodePlugin".getBytes(StandardCharsets.UTF_8);
        for (byte[] cf : builderClassFiles()) {
            if (!contains(cf, append) && !contains(cf, prepend)) {
                continue;
            }
            ClassModel cm = ClassFile.of().parse(cf);
            for (MethodModel m : cm.methods()) {
                if (m.code().isEmpty()) {
                    continue;
                }
                boolean registers = false;
                List<String> created = new ArrayList<>();
                for (CodeElement e : m.code().get()) {
                    if (e instanceof InvokeInstruction i && i.owner().asInternalName().equals(PLUGINS) &&
                                    (i.name().equalsString("appendNodePlugin") || i.name().equalsString("prependNodePlugin"))) {
                        registers = true;
                    } else if (e instanceof NewObjectInstruction n) {
                        created.add(n.className().asInternalName());
                    }
                }
                if (!registers) {
                    continue;
                }
                for (String internal : created) {
                    if (!internal.startsWith(PKG) && !internal.contains("StringAnalysis")) {
                        continue;
                    }
                    Class<?> c = Class.forName(internal.replace('/', '.'), false, FlatStockPathTest.class.getClassLoader());
                    if (NodePlugin.class.isAssignableFrom(c)) {
                        out.add(internal);
                        registrars.add(cm.thisClass().asInternalName());
                    }
                }
            }
        }
        return out;
    }

    private static final Set<String> EXPECTED_PLUGINS = Set.of(PKG + "EqualsMatrixNodePlugin", PKG + "InlineCacheTrivialMethodNodePlugin", PKG + "OffStringFinalBindingPlugin", PKG +
                    "StringAnalysisCapturePlugin",
                    PKG + "StringLengthNodePlugin", PKG + "StringRepresentationReplacementPlugin",
                    PKG + "RangeCopyRedirectPlugin",
                    PKG + "AppendMirrorNodePlugin",
                    PKG + "TypeCheckIcNodePlugin");

    @Test
    public void everyRegisteredNodePluginDeclinesTheFlatReentry() throws Exception {
        Set<String> registrars = new TreeSet<>();
        Set<String> plugins = registeredNodePlugins(registrars);
        /* the expected plugin set; a new plugin must be added here and carry the guard */
        Assert.assertEquals("registered by " + registrars, EXPECTED_PLUGINS, plugins);
        for (String p : plugins) {
            MethodModel handleInvoke = null;
            for (MethodModel m : model(p).methods()) {
                if (m.methodName().equalsString("handleInvoke") && m.methodType().equalsString(
                                "(Ljdk/graal/compiler/nodes/graphbuilderconf/GraphBuilderContext;Ljdk/vm/ci/meta/ResolvedJavaMethod;[Ljdk/graal/compiler/nodes/ValueNode;)Z")) {
                    handleInvoke = m;
                }
            }
            Assert.assertNotNull(p + " declares handleInvoke", handleInvoke);
            InvokeInstruction first = null;
            for (CodeElement e : handleInvoke.code().get()) {
                if (e instanceof InvokeInstruction i) {
                    first = i;
                    break;
                }
            }
            Assert.assertNotNull(p + ".handleInvoke invokes something", first);
            Assert.assertEquals(p + ": the first call of handleInvoke is the flat re-entry check", GUARD_OWNER + ".isFlatReentry",
                            first.owner().asInternalName() + "." + first.name().stringValue());
        }
    }

    /** A proxy of {@code type} that only answers identity {@code equals}/{@code hashCode}; any other call is recorded. */
    private static <T> T untouchable(Class<T> type, List<String> touched) {
        Object p = Proxy.newProxyInstance(FlatStockPathTest.class.getClassLoader(), new Class<?>[]{type}, (proxy, method, args) -> {
            switch (method.getName()) {
                case "equals":
                    return proxy == args[0];
                case "hashCode":
                    return System.identityHashCode(proxy);
                case "toString":
                    return type.getSimpleName() + "-proxy";
                default:
                    touched.add(type.getSimpleName() + "." + method.getName());
                    throw new AssertionError("the plugin touched " + type.getSimpleName() + "." + method.getName() + " during the flat re-entry");
            }
        });
        return type.cast(p);
    }

    private static NodePlugin instantiate(String internal) throws Exception {
        Class<?> c = Class.forName(internal.replace('/', '.'), true, FlatStockPathTest.class.getClassLoader());
        Constructor<?> best = null;
        for (Constructor<?> k : c.getDeclaredConstructors()) {
            if (best == null || k.getParameterCount() < best.getParameterCount()) {
                best = k;
            }
        }
        Assert.assertNotNull(internal + " has a constructor", best);
        best.setAccessible(true);
        Object[] a = new Object[best.getParameterCount()];
        Class<?>[] pt = best.getParameterTypes();
        for (int i = 0; i < a.length; i++) {
            a[i] = pt[i] == boolean.class ? Boolean.TRUE : pt[i] == int.class ? 0 : null;
        }
        return (NodePlugin) best.newInstance(a);
    }

    @Test
    public void everyPluginStepsAsideInsideTheFlatReentry() throws Exception {
        for (String p : EXPECTED_PLUGINS) {
            NodePlugin plugin = instantiate(p);
            List<String> touched = new ArrayList<>();
            GraphBuilderContext b = untouchable(GraphBuilderContext.class, touched);
            ResolvedJavaMethod m = untouchable(ResolvedJavaMethod.class, touched);
            boolean[] result = {true};
            InlineCacheTrivialMethodNodePlugin.withFlatReentry(b, m, () -> result[0] = plugin.handleInvoke(b, m, new ValueNode[0]));
            Assert.assertFalse(p + " declines the flat re-entry (returns false)", result[0]);
            Assert.assertTrue(p + " touched nothing during the flat re-entry: " + touched, touched.isEmpty());
            Assert.assertFalse("the re-entry mark is cleared after the emission", InlineCacheTrivialMethodNodePlugin.isFlatReentry(b, m));
        }
    }

    @Test
    public void flatStockPathIsTheDefault() {
        Assert.assertNull("the test JVM must not set the knob", System.getProperty("svm.stringanalysis.ic.flatstock"));
        Assert.assertEquals("the flat call is the default (ic.flatstock=1); 0 is the revert switch, 2 the CHECK mode", 1, InlineCacheTrivialMethodNodePlugin.FLAT_STOCK_MODE);
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.FLAT_STOCK);
        Assert.assertFalse("no re-entry outside an emission", InlineCacheTrivialMethodNodePlugin.isFlatReentry(null, null));
    }
}
