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

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.StringView;

/**
 * The builder-view factories follow the JDK's {@code String(AbstractStringBuilder, Void)} rule: a UTF-16
 * builder is scanned for compression only when {@code AbstractStringBuilder.maybeLatin1} is set (read through an alias
 * of the existing field in an image, reflectively here).
 */
public class BuilderViewMaybeLatin1Test {

    /**
     * The JDK builder's own fields, read like the image's alias reads them ({@code java.lang} is closed to reflection in
     * the hosted JUnit; {@code sun.misc.Unsafe} reads them by offset).
     */
    private static final class Asb {
        // sun.misc.Unsafe by reflection: jdk.unsupported is not in this project's compile-time module graph
        static final Object U;
        static final Method GET_BOOLEAN;
        static final Method GET_BYTE;
        static final Method GET_INT;
        static final Method GET_OBJECT;
        static final long VALUE;
        static final long CODER;
        static final long COUNT;
        static final long MAYBE_LATIN1;
        static {
            try {
                Class<?> unsafe = Class.forName("sun.misc.Unsafe");
                Field f = unsafe.getDeclaredField("theUnsafe");
                f.setAccessible(true);
                U = f.get(null);
                Method offset = unsafe.getMethod("objectFieldOffset", Field.class);
                GET_BOOLEAN = unsafe.getMethod("getBoolean", Object.class, long.class);
                GET_BYTE = unsafe.getMethod("getByte", Object.class, long.class);
                GET_INT = unsafe.getMethod("getInt", Object.class, long.class);
                GET_OBJECT = unsafe.getMethod("getObject", Object.class, long.class);
                Class<?> asb = Class.forName("java.lang.AbstractStringBuilder");
                VALUE = (long) offset.invoke(U, asb.getDeclaredField("value"));
                CODER = (long) offset.invoke(U, asb.getDeclaredField("coder"));
                COUNT = (long) offset.invoke(U, asb.getDeclaredField("count"));
                MAYBE_LATIN1 = (long) offset.invoke(U, asb.getDeclaredField("maybeLatin1"));
            } catch (ReflectiveOperationException e) {
                throw new ExceptionInInitializerError(e);
            }
        }

        static Object read(Method m, Object asb, long off) {
            try {
                return m.invoke(U, asb, off);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }
    }

    private static boolean jdkMaybeLatin1(Object asb) {
        return (boolean) Asb.read(Asb.GET_BOOLEAN, asb, Asb.MAYBE_LATIN1);
    }

    private static byte jdkCoder(Object asb) {
        return (byte) Asb.read(Asb.GET_BYTE, asb, Asb.CODER);
    }

    /** The image's {@code StringView.create(StringBuilder/StringBuffer)} body: one snapshot, maybeLatin1 read last. */
    private static String snapshotView(Object asb) {
        byte[] value = (byte[]) Asb.read(Asb.GET_OBJECT, asb, Asb.VALUE);
        byte coder = jdkCoder(asb);
        int count = (int) Asb.read(Asb.GET_INT, asb, Asb.COUNT);
        return StringView.ofBuilderSnapshot(value, coder, count, jdkMaybeLatin1(asb));
    }

    private static void sameAsJdk(String what, String jdk, String made) {
        Assert.assertEquals(what + " length", jdk.length(), made.length());
        Assert.assertEquals(what + " content", jdk, RepEqualsMatrixTest.contentOf(made));
        Assert.assertEquals(what + " coder", jdk.coder(), made.coder());
        Assert.assertTrue(what + " jdk.equals(made) (the REDIRECT mirror)", RepEq.eq(jdk, made));
        Assert.assertTrue(what + " made.equals(jdk)", made.equals(jdk));
        Assert.assertEquals(what + " hashCode", jdk.hashCode(), made.hashCode());
        Assert.assertEquals(what + " appended", jdk, new StringBuilder().append(made).toString());
    }

    /** The JDK rule the snapshot relies on: which ops set maybeLatin1 (and the flag is inherited). */
    @Test
    public void theJdkFlagRule() {
        StringBuilder sb = new StringBuilder("ab\u20ac");
        Assert.assertFalse("a live non-Latin-1 char: the field is clear and the factory sees it", jdkMaybeLatin1(sb));
        StringBuffer sbuf = new StringBuffer("ab\u20ac");
        Assert.assertFalse(jdkMaybeLatin1(sbuf));
        sb.setLength(2);
        sbuf.deleteCharAt(2);
        Assert.assertTrue("setLength shrinking sets it", jdkMaybeLatin1(sb));
        Assert.assertTrue("deleteCharAt sets it", jdkMaybeLatin1(sbuf));
        Assert.assertTrue("the copy constructor inherits it", jdkMaybeLatin1(new StringBuilder(sb)));
        Assert.assertTrue("append(AbstractStringBuilder) inherits it", jdkMaybeLatin1(new StringBuilder("\u20ac").append(sb)));
        Assert.assertFalse(jdkMaybeLatin1(new StringBuilder("\u20ac").append("x")));
    }

    /** Inflated by a non-Latin-1 append, the char removed: maybeLatin1 set, the snapshot is the compact copy. */
    @Test
    public void removedNonLatin1GivesCompactLatin1() {
        String[] kinds = {"setLength", "delete", "deleteCharAt", "setCharAt", "replace"};
        for (String k : kinds) {
            for (int buffer = 0; buffer < 2; buffer++) {
                AbstractStringBuilderOps b = buffer == 0 ? AbstractStringBuilderOps.of(new StringBuilder()) : AbstractStringBuilderOps.of(new StringBuffer());
                b.append("hello world, a longer latin-1 text").append("\u20ac");
                switch (k) {
                    case "setLength" -> b.setLength(b.length() - 1);
                    case "delete" -> b.delete(b.length() - 1, b.length());
                    case "deleteCharAt" -> b.deleteCharAt(b.length() - 1);
                    case "setCharAt" -> b.setCharAt(b.length() - 1, 'x');
                    default -> b.replace(b.length() - 1, b.length(), "yz");
                }
                String what = k + (buffer == 0 ? " StringBuilder" : " StringBuffer");
                Assert.assertTrue(what + ": maybeLatin1", jdkMaybeLatin1(b.target()));
                String jdk = b.toString();
                Assert.assertEquals(what + ": JDK compresses", 0, jdk.coder());
                String made = b.view();
                Assert.assertFalse(what + ": compact copy, not a UTF-16 view", made instanceof StringView);
                sameAsJdk(what, jdk, made);
            }
        }
    }

    /** A live non-Latin-1 char: maybeLatin1 clear, the view is made without a scan (UTF-16, shared). */
    @Test
    public void liveNonLatin1IsAViewWithoutScan() {
        StringBuilder sb = new StringBuilder();
        sb.append("\u20ac");
        for (int i = 0; i < 200; i++) {
            sb.append((char) ('a' + i % 26));
        }
        Assert.assertFalse(jdkMaybeLatin1(sb));
        String made = snapshotView(sb);
        Assert.assertTrue(made instanceof StringView);
        Assert.assertEquals(1, made.coder());
        sameAsJdk("live", sb.toString(), made);
        // no scan: a UTF-16 snapshot of Latin-1-only chars (a state the JDK never pairs with a clear flag) stays a view
        String utf16 = new String("abc\u20ac".toCharArray());
        Assert.assertEquals(1, utf16.coder());
        byte[] inflated = utf16.value().clone(); // UTF-16, platform byte order
        String noScan = StringView.ofBuilderSnapshot(inflated, (byte) 1, 3, false);
        Assert.assertTrue("maybeLatin1 clear: no scan, the view as made", noScan instanceof StringView);
        Assert.assertEquals(1, noScan.coder());
        String scanned = StringView.ofBuilderSnapshot(inflated, (byte) 1, 3, true);
        Assert.assertFalse("maybeLatin1 set: the scan compresses", scanned instanceof StringView);
        Assert.assertEquals(0, scanned.coder());
    }

    /** Parity against {@code toString()} over generated op sequences (StringBuilder and StringBuffer). */
    @Test
    public void parityOverGeneratedSequences() {
        Random r = new Random(9501);
        char[] alphabet = {'a', 'Z', ' ', '\u00e9', '\u00ff', '\u0100', '\u20ac', '\u4e2d'};
        int steps = 0;
        int views = 0;
        int copies = 0;
        int noScan = 0;
        for (int seq = 0; seq < 400; seq++) {
            AbstractStringBuilderOps b = (seq & 1) == 0 ? AbstractStringBuilderOps.of(new StringBuilder()) : AbstractStringBuilderOps.of(new StringBuffer());
            for (int step = 0; step < 40; step++) {
                int len = b.length();
                char c = alphabet[r.nextInt(alphabet.length)];
                switch (r.nextInt(len == 0 ? 3 : 12)) {
                    case 0 -> b.append(String.valueOf(c));
                    case 1 -> b.append("x" + c + "yz");
                    case 2 -> b.appendBuilder(r.nextBoolean(), c);
                    case 3 -> b.setLength(r.nextInt(len + 1));
                    case 4 -> {
                        int s = r.nextInt(len + 1);
                        b.delete(s, s + r.nextInt(len - s + 1));
                    }
                    case 5 -> b.deleteCharAt(r.nextInt(len));
                    case 6 -> b.setCharAt(r.nextInt(len), c);
                    case 7 -> {
                        int s = r.nextInt(len + 1);
                        b.replace(s, s + r.nextInt(len - s + 1), r.nextBoolean() ? "q" : String.valueOf(c));
                    }
                    case 8 -> b.insert(r.nextInt(len + 1), String.valueOf(c));
                    case 9 -> b.reverse();
                    case 10 -> b.copyConstruct();
                    default -> b.append(String.valueOf(c).repeat(1 + r.nextInt(20)));
                }
                String jdk = b.toString();
                boolean flag = jdkMaybeLatin1(b.target());
                if (!flag && jdkCoder(b.target()) == 1) {
                    Assert.assertEquals("the JDK invariant: UTF-16 with the flag clear holds a char above 0xFF", 1, jdk.coder());
                }
                String made = b.view();
                sameAsJdk("hosted factory seq " + seq + " step " + step, jdk, b.hostedFactoryView());
                if (!flag) {
                    // the view as made, or the copy branch's exact String with the builder's coder (no compression)
                    Assert.assertTrue("flag clear: no scan, the view as made or the exact copy", made instanceof StringView || made.getClass() == String.class && made.coder() == jdkCoder(b.target()));
                    if (made.coder() == 1) {
                        noScan++; // a UTF-16 builder with the flag clear: JDK parity below without a scan
                    }
                }
                sameAsJdk("seq " + seq + " step " + step + " [" + jdk + "]", jdk, made);
                steps++;
                if (made instanceof StringView) {
                    views++;
                } else {
                    copies++;
                }
            }
        }
        Assert.assertEquals(16000, steps);
        Assert.assertTrue("both outcomes exercised: views " + views + ", copies " + copies, views > 1000 && copies > 1000);
        Assert.assertTrue("the no-scan path exercised: " + noScan, noScan > 300); // 520 with this seed
    }

    /** One API over StringBuilder and StringBuffer (they share no public mutator interface). */
    private static final class AbstractStringBuilderOps {
        private StringBuilder sb;
        private StringBuffer sbuf;

        static AbstractStringBuilderOps of(StringBuilder b) {
            AbstractStringBuilderOps o = new AbstractStringBuilderOps();
            o.sb = b;
            return o;
        }

        static AbstractStringBuilderOps of(StringBuffer b) {
            AbstractStringBuilderOps o = new AbstractStringBuilderOps();
            o.sbuf = b;
            return o;
        }

        Object target() {
            return sb != null ? sb : sbuf;
        }

        int length() {
            return sb != null ? sb.length() : sbuf.length();
        }

        AbstractStringBuilderOps append(String s) {
            if (sb != null) {
                sb.append(s);
            } else {
                sbuf.append(s);
            }
            return this;
        }

        /** append(AbstractStringBuilder): inherits the argument's maybeLatin1. */
        void appendBuilder(boolean deleted, char c) {
            StringBuilder other = new StringBuilder("\u20ac").append(c).append("ok");
            if (deleted) {
                other.deleteCharAt(0); // maybeLatin1 set on the argument
            }
            if (sb != null) {
                sb.append(other);
            } else {
                sbuf.append(other);
            }
        }

        /** The copy constructor: inherits the source's maybeLatin1. */
        void copyConstruct() {
            if (sb != null) {
                sb = new StringBuilder(sb);
            } else {
                sbuf = new StringBuffer(sbuf);
            }
        }

        void setLength(int n) {
            if (sb != null) {
                sb.setLength(n);
            } else {
                sbuf.setLength(n);
            }
        }

        void delete(int s, int e) {
            if (sb != null) {
                sb.delete(s, e);
            } else {
                sbuf.delete(s, e);
            }
        }

        void deleteCharAt(int i) {
            if (sb != null) {
                sb.deleteCharAt(i);
            } else {
                sbuf.deleteCharAt(i);
            }
        }

        void setCharAt(int i, char c) {
            if (sb != null) {
                sb.setCharAt(i, c);
            } else {
                sbuf.setCharAt(i, c);
            }
        }

        void replace(int s, int e, String str) {
            if (sb != null) {
                sb.replace(s, e, str);
            } else {
                sbuf.replace(s, e, str);
            }
        }

        void insert(int i, String s) {
            if (sb != null) {
                sb.insert(i, s);
            } else {
                sbuf.insert(i, s);
            }
        }

        void reverse() {
            if (sb != null) {
                sb.reverse();
            } else {
                sbuf.reverse();
            }
        }

        /** The image path (the snapshot with the JDK flag). */
        String view() {
            return snapshotView(target());
        }

        /** The hosted factory (no alias outside an image: always the scan). */
        String hostedFactoryView() {
            return sb != null ? StringView.create(sb) : StringView.create(sbuf);
        }

        @Override
        public String toString() {
            return sb != null ? sb.toString() : sbuf.toString();
        }
    }
}
