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
import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import org.junit.Assert;

import com.oracle.svm.core.stringrep.TrivialString;

/**
 * Shared helpers of the rep pins
 * {@code RepReturnPinTest}, {@code RepInheritedBodyTest} and {@code RepEscapeTest}.
 */
final class RepPinSupport {

    private RepPinSupport() {
    }

    /** The package of every custom representation class. */
    static final String REP_PACKAGE = "com.oracle.svm.core.stringrep";

    /**
     * Every rep class: the inline-cache registry's seven production reps plus the test-only {@link TrivialString}. The
     * set is checked against {@link SugNameTables#STRINGY_REP_TYPES} (the analysis' own list) and against a
     * scan of the class files: every {@code String} subclass of the svm class files on the test path (the rep package
     * included) must be in it. So a new rep class must be classified here before the pins pass.
     */
    static List<Class<?>> repClasses() {
        List<Class<?>> out = new ArrayList<>(InlineCacheRegistry.REP_CLASSES.values());
        out.add(TrivialString.class);
        Set<String> names = new TreeSet<>();
        for (Class<?> c : out) {
            names.add(c.getName());
        }
        Assert.assertEquals("the pinned rep classes are exactly the analysis' STRINGY_REP_TYPES", new TreeSet<>(SugNameTables.STRINGY_REP_TYPES), names);
        Assert.assertEquals("the pinned rep classes are exactly the String subclasses of the svm class files " + scannedRoots(), names, scannedStringSubclasses());
        return out;
    }

    /** The class-file roots of the scan: every class path and module path entry of the substratevm tree. */
    static List<String> scannedRoots() {
        List<String> out = new ArrayList<>();
        for (String prop : new String[]{"java.class.path", "jdk.module.path", "jdk.module.upgrade.path"}) {
            String v = System.getProperty(prop);
            if (v == null) {
                continue;
            }
            for (String e : v.split(File.pathSeparator)) {
                if (e.contains("/substratevm/") && !out.contains(e)) {
                    out.add(e);
                }
            }
        }
        return out;
    }

    private static volatile Set<String> stringSubclasses;

    /**
     * The binary names of every class in {@link #scannedRoots()} whose superclass chain reaches
     * {@code java.lang.String} (read from the class files, not from any hand list). Asserts that the scan saw the rep
     * package (every production rep's class file).
     */
    static Set<String> scannedStringSubclasses() {
        Set<String> cached = stringSubclasses;
        if (cached != null) {
            return cached;
        }
        Map<String, String> superOf = new HashMap<>();
        forEachClassFile(bytes -> record(superOf, bytes));
        Set<String> out = new TreeSet<>();
        for (String c : superOf.keySet()) {
            String s = superOf.get(c);
            for (int depth = 0; s != null && depth < 64; depth++) {
                if (s.equals("java/lang/String")) {
                    out.add(c.replace('/', '.'));
                    break;
                }
                s = superOf.get(s);
            }
        }
        for (Class<?> rep : InlineCacheRegistry.REP_CLASSES.values()) {
            Assert.assertTrue("the class-file scan saw " + rep.getName() + " (roots " + scannedRoots() + ")", superOf.containsKey(rep.getName().replace('.', '/')));
        }
        stringSubclasses = out;
        return out;
    }

    /** Every class file (bytes) under {@link #scannedRoots()}: class directories and jars ({@code META-INF/} excluded). */
    static void forEachClassFile(Consumer<byte[]> action) {
        for (String root : scannedRoots()) {
            Path p = Path.of(root);
            try {
                if (Files.isDirectory(p)) {
                    try (Stream<Path> walk = Files.walk(p)) {
                        for (Path f : (Iterable<Path>) walk.filter(x -> x.toString().endsWith(".class"))::iterator) {
                            action.accept(Files.readAllBytes(f));
                        }
                    }
                } else if (root.endsWith(".jar") && Files.isRegularFile(p)) {
                    try (JarFile jar = new JarFile(p.toFile())) {
                        Enumeration<JarEntry> en = jar.entries();
                        while (en.hasMoreElements()) {
                            JarEntry je = en.nextElement();
                            if (je.getName().endsWith(".class") && !je.getName().startsWith("META-INF/")) {
                                try (InputStream in = jar.getInputStream(je)) {
                                    action.accept(in.readAllBytes());
                                }
                            }
                        }
                    }
                }
            } catch (IOException e) {
                throw new UncheckedIOException(root, e);
            }
        }
    }

    private static void record(Map<String, String> superOf, byte[] bytes) {
        ClassModel cm;
        try {
            cm = ClassFile.of().parse(bytes);
        } catch (IllegalArgumentException e) {
            return; // not a class file this JDK parses (e.g. a newer version); cannot extend the builder's String
        }
        superOf.putIfAbsent(cm.thisClass().asInternalName(), cm.superclass().map(sc -> sc.asInternalName()).orElse(null));
    }

    /** A rep class: a strict subclass of {@code java.lang.String} (the only ones in the svm tree are the reps, see {@link #repClasses()}). */
    static boolean isRep(Class<?> c) {
        return c != String.class && String.class.isAssignableFrom(c);
    }

    /** The usage-site signature format: the parameter descriptors joined by {@code ","}, empty for none. */
    static String signature(Method m) {
        StringBuilder sb = new StringBuilder();
        for (Class<?> p : m.getParameterTypes()) {
            if (sb.length() > 0) {
                sb.append(',');
            }
            sb.append(descriptor(p));
        }
        return sb.toString();
    }

    static String descriptor(Class<?> type) {
        return type.descriptorString();
    }

    /** {@code Simple.name(sig)}. */
    static String label(Class<?> c, String name, String sig) {
        return c.getSimpleName() + "." + name + "(" + sig + ")";
    }

    /** The hand-list entry of {@code java.lang.String.name(sig)}, or null. */
    static StringTerminalHandList.Entry handEntry(String name, String sig) {
        for (StringTerminalHandList.Entry e : StringTerminalHandList.STRING_ENTRIES) {
            if (e.name().equals(name) && e.signature().equals(sig)) {
                return e;
            }
        }
        return null;
    }
}
