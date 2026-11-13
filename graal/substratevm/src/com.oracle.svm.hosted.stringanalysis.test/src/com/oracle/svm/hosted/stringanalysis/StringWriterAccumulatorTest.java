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

import java.io.StringWriter;
import java.io.Writer;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * {@code java.io.StringWriter} as an accumulator kind. Pins the writer's pass-1 table (every public method StringWriter
 * declares is classified exactly once; the inherited, non-overridden Writer methods are the known set), the receiver
 * proof's {@code return this} rule, and the runtime premise on the real JDK class: a view over the writer's buffer (the
 * parent's {@code StringView.create(writer.buf)}, in its sharing regime) keeps its content under every public overload
 * of every growing writer method (incl. the
 * inherited {@code Writer.write(char[])}, reallocation and Latin-1 to UTF-16 inflation), while the escape
 * {@code getBuffer()} lets a mutator change it (the rejection is necessary).
 */
public class StringWriterAccumulatorTest {

    private static final String SW = "java.io.StringWriter";

    @Test
    public void everyPublicWriterMethodIsClassified() {
        Set<String> seen = new TreeSet<>();
        for (Method m : StringWriter.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(m.getModifiers()) || m.isSynthetic() || m.isBridge()) {
                continue;
            }
            String n = m.getName();
            seen.add(n);
            int classes = (AccumulatorWhitelist.WRITER_GROWING_METHODS.contains(n) ? 1 : 0) + (AccumulatorWhitelist.WRITER_READ_ONLY_METHODS.contains(n) ? 1 : 0) +
                            (AccumulatorWhitelist.WRITER_ESCAPING_METHODS.contains(n) ? 1 : 0);
            Assert.assertEquals("unclassified (or doubly classified) StringWriter method " + n, 1, classes);
        }
        for (Set<String> set : List.of(AccumulatorWhitelist.WRITER_GROWING_METHODS, AccumulatorWhitelist.WRITER_READ_ONLY_METHODS, AccumulatorWhitelist.WRITER_ESCAPING_METHODS)) {
            for (String n : set) {
                Assert.assertTrue("stale entry " + n, n.equals("<init>") || seen.contains(n));
            }
        }
        for (String n : AccumulatorWhitelist.W_GROW_WRITER) {
            Assert.assertEquals(n, AccumulatorWhitelist.AccRow.GROWING, AccumulatorWhitelist.accumulatorUsageRow(SW, n, UsageRole.RECEIVER));
            Assert.assertEquals("a writer-declared site in another role is not a read", AccumulatorWhitelist.AccRow.REJECT,
                            AccumulatorWhitelist.accumulatorUsageRow(SW, n, UsageRole.PARAMETER));
        }
        for (String n : List.of("getBuffer", "field:buf", "field:lock")) {
            Assert.assertEquals(n, AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow(SW, n, UsageRole.RECEIVER));
        }
        // the builder table is not widened: a writer method name on a builder still follows the builder table
        Assert.assertEquals(AccumulatorWhitelist.AccRow.REJECT, AccumulatorWhitelist.accumulatorUsageRow("java.lang.StringBuilder", "write", UsageRole.RECEIVER));
    }

    /**
     * The public instance methods StringWriter inherits from Writer without overriding: entered by the walk (Writer is not
     * a stringy declaring type), so their bodies' calls are the usages. A new one fails here until audited.
     */
    @Test
    public void inheritedWriterMethodsAreTheAuditedSet() {
        Set<String> inherited = new TreeSet<>();
        for (Method m : Writer.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(m.getModifiers()) || Modifier.isStatic(m.getModifiers())) {
                continue;
            }
            try {
                StringWriter.class.getDeclaredMethod(m.getName(), m.getParameterTypes());
            } catch (NoSuchMethodException e) {
                inherited.add(m.getName() + java.util.Arrays.toString(m.getParameterTypes()));
            }
        }
        // Writer.write(char[]) = write(cbuf, 0, cbuf.length): a virtual call to StringWriter.write(char[],int,int)
        Assert.assertEquals(Set.of("write[class [C]"), inherited);
    }

    @Test
    public void returnThisRule() {
        Assert.assertTrue(AccumulatorWhitelist.returnsThis(SW, "append"));
        Assert.assertFalse(AccumulatorWhitelist.returnsThis(SW, "write"));
        Assert.assertFalse(AccumulatorWhitelist.returnsThis(SW, "getBuffer"));
        Assert.assertTrue(AccumulatorWhitelist.returnsThis("java.lang.StringBuilder", "append"));
        Assert.assertFalse(AccumulatorWhitelist.returnsThis("java.io.Writer", "append"));
    }

    @Test
    public void writerToStringIsSeedableWithTheKnob() {
        Assert.assertTrue(StringAtoms.ACC_SEED_TYPES.contains(SW));
        Assert.assertTrue(AccumulatorWhitelist.isSeedableExtraction(SW, "toString", ""));
        Assert.assertFalse(AccumulatorWhitelist.isSeedableExtraction(SW, "getBuffer", ""));
    }

    // ------------------------------------------------------------------
    // The runtime premise on the real class.
    // ------------------------------------------------------------------
    private static final String BASE = "abcdef";

    /** A writer whose buffer the factory shares (6 of 8 Latin-1 bytes used). */
    private static StringWriter sharingWriter() {
        StringWriter w = new StringWriter(8);
        w.write(BASE);
        return w;
    }

    private static List<Consumer<StringWriter>> growingOps() {
        return List.of(
                        w -> w.write('x'),
                        w -> w.write('ā'),
                        w -> w.write(new char[]{'p', 'q'}, 0, 2),
                        w -> {
                            try {
                                w.write(new char[]{'p', 'q', 'Ă'}); // inherited Writer.write(char[])
                            } catch (java.io.IOException e) {
                                throw new AssertionError(e);
                            }
                        },
                        w -> w.write("ghij"),
                        w -> w.write("klmnop", 1, 3),
                        w -> w.append("st"),
                        w -> w.append("uvwxyz", 1, 4),
                        w -> w.append('z'),
                        w -> w.append(null),
                        StringWriter::flush,
                        w -> {
                            try {
                                w.close();
                            } catch (java.io.IOException e) {
                                throw new AssertionError(e);
                            }
                        },
                        w -> w.toString());
    }

    private static void followUp(StringWriter w) {
        w.write("12"); // in place
        w.write("0123456789012345678901234567890123456789"); // reallocation
        w.write("€"); // inflation
    }

    @Test
    public void growingWriterMethodsKeepTheView() {
        int i = 0;
        for (Consumer<StringWriter> op : growingOps()) {
            StringWriter w = sharingWriter();
            StringView v = (StringView) StringView.create(w.getBuffer()); // the parent's lowering: create(writer.buf)
            RepEq.assertRepEquals(BASE, v.toString());
            op.accept(w);
            followUp(w);
            RepEq.assertRepEquals("op " + i, BASE, v.toString());
            Assert.assertEquals("op " + i, BASE.length(), v.length());
            Assert.assertEquals("op " + i, 'f', v.charAt(5));
            i++;
        }
        // the view is shared in this regime (the premise is about the sharing case): an in-place write is invisible
        StringWriter w = new StringWriter(8);
        w.write("abc");
        w.write("def");
        StringView v = (StringView) StringView.create(w.getBuffer());
        w.write("g");
        RepEq.assertRepEquals("abcdef", v.toString());
    }

    @Test
    public void getBufferMutationChangesASharedView() {
        StringWriter w = sharingWriter();
        StringView v = (StringView) StringView.create(w.getBuffer());
        StringBuffer b = w.getBuffer();
        b.setLength(0);
        b.append("zzzzzz");
        Assert.assertFalse("the getBuffer escape is a real hazard", RepEq.eq(BASE, v.toString()));
    }
}
