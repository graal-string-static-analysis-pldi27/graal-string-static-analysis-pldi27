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
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Enumeration;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * The class-initializer simulation parity rule ({@link RepTypeChecks#clinitSimulationParityActive},
 * the hook {@code SimulateClassInitializerGraphDecoder#abortIfRepAllocation}): the rule aborts a simulation at an
 * allocation whose type satisfies {@link RepTypeChecks#isRepOrRepArrayClass}. This pins that the predicate covers every
 * rep family of {@code com.oracle.svm.core.stringrep} (scanned, not listed: every class of the package that extends
 * String), their arrays, and nothing a non-rep allocation in a class initializer would produce.
 */
public class ClinitSimulationParityTest {

    static TreeSet<String> stringrepClassNames() throws IOException, URISyntaxException {
        String pkg = StringView.class.getPackageName().replace('.', '/') + "/";
        Path src = Paths.get(StringView.class.getProtectionDomain().getCodeSource().getLocation().toURI());
        TreeSet<String> out = new TreeSet<>();
        if (Files.isDirectory(src)) {
            try (Stream<Path> s = Files.list(src.resolve(pkg))) {
                s.map(p -> p.getFileName().toString()).filter(n -> n.endsWith(".class")).forEach(n -> out.add(n.substring(0, n.length() - 6)));
            }
        } else {
            try (JarFile jar = new JarFile(src.toFile())) {
                for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements();) {
                    String n = e.nextElement().getName();
                    if (n.startsWith(pkg) && n.endsWith(".class") && n.indexOf('/', pkg.length()) < 0) {
                        out.add(n.substring(pkg.length(), n.length() - 6));
                    }
                }
            }
        }
        return out;
    }

    @Test
    public void everyRepFamilyAndItsArraysAbortTheSimulation() throws Exception {
        TreeSet<String> reps = new TreeSet<>();
        for (String simple : stringrepClassNames()) {
            Class<?> c = Class.forName(StringView.class.getPackageName() + "." + simple, false, StringView.class.getClassLoader());
            if (String.class.isAssignableFrom(c)) {
                reps.add(simple);
                Assert.assertTrue(simple, RepTypeChecks.isRepOrRepArrayClass(c));
                Assert.assertTrue(simple + "[]", RepTypeChecks.isRepOrRepArrayClass(c.arrayType()));
                Assert.assertTrue(simple + "[][]", RepTypeChecks.isRepOrRepArrayClass(c.arrayType().arrayType()));
            } else {
                Assert.assertFalse(simple, RepTypeChecks.isRepOrRepArrayClass(c));
            }
        }
        Assert.assertEquals("the rep families the rule covers (SB, SV, the lazy reps, Trivial)",
                        "[ArrayLazyString, FixedConcat4, InterleavedStringArray, RopeString, SingleByteString, StringView, ThreeWayString, TrivialString]", reps.toString());
    }

    @Test
    public void nonRepAllocationsDoNotAbort() {
        for (Class<?> c : new Class<?>[]{String.class, String[].class, String[][].class, Object.class, Object[].class, CharSequence[].class, StringBuilder.class, byte[].class,
                        int[].class, ClinitSimulationParityTest.class}) {
            Assert.assertFalse(c.getTypeName(), RepTypeChecks.isRepOrRepArrayClass(c));
        }
    }
}
