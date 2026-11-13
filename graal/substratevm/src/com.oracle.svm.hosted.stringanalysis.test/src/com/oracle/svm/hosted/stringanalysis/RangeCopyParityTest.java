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

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URI;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.stringrep.SingleByteString;
import com.oracle.svm.core.stringrep.TrivialString;

/**
 * The builder JDK's {@code AbstractStringBuilder.appendChars(..., String, ...)} ({@code append(CharSequence,int,int)})
 * and {@code putStringAt} ({@code insert(int,CharSequence,int,int)} of a whole String) copy through the protected
 * ranged copy {@code String.getBytes(byte[],int,int,byte,int)}, which every value-null rep overrides.
 *
 * <p>Premise: the JDK method is {@code protected} (overridable from the rep package), every value-null rep declares
 * it, the flat reps run String's body. Parity: for every rep instance of {@link RepJdkParityTest#instances()} and
 * every range {@code [b, e)}, the ranged append / insert into Latin-1 and UTF-16 {@code StringBuilder}s and
 * {@code StringBuffer}s gives exactly the JDK's result on the plain string with the same chars (content, coder-exact
 * {@code equals}, hash).
 */
public class RangeCopyParityTest {

    static Method rangedCopy() throws NoSuchMethodException {
        return String.class.getDeclaredMethod("getBytes", byte[].class, int.class, int.class, byte.class, int.class);
    }

    @Test
    public void rangedCopyIsProtectedAndOverriddenByEveryValueNullRep() throws NoSuchMethodException {
        Method m = rangedCopy();
        Assert.assertTrue("the builder JDK's ranged copy must be protected", Modifier.isProtected(m.getModifiers()));
        Assert.assertFalse(Modifier.isFinal(m.getModifiers()) || Modifier.isStatic(m.getModifiers()));
        Assert.assertFalse("non-vacuous", RepInheritedBodyTest.VALUE_NULL_REPS.isEmpty());
        for (Class<?> rep : RepInheritedBodyTest.VALUE_NULL_REPS) {
            Assert.assertSame(rep + " must override the ranged copy getBytes(byte[],int,int,byte,int)", rep, RepInheritedBodyTest.implementingClass(rep, m));
        }
        for (Class<?> flat : new Class<?>[]{SingleByteString.class, TrivialString.class}) {
            Assert.assertSame(flat + " keeps a real value[]: String's body", String.class, RepInheritedBodyTest.implementingClass(flat, m));
        }
    }

    @Test
    public void whitelistRowsForTheRangedCopy() {
        Assert.assertTrue(StringViewWhitelist.isWhitelisted("getBytes", "java.lang.String", "[B,I,I,B,I"));
        for (String v : new String[]{"ROPE", "THREE_WAY", "FIXED4", "ARRAY_LAZY", "INTERLEAVED"}) {
            Assert.assertTrue(v, LazyConcatWhitelist.isWhitelisted("getBytes", "java.lang.String", "[B,I,I,B,I", v));
        }
        Assert.assertTrue("variant-free", LazyConcatWhitelist.isWhitelisted("getBytes", "java.lang.String", "[B,I,I,B,I"));
    }

    @Test
    public void rangedAppendAndInsertAreTheJdks() {
        int ranges = 0;
        for (RepJdkParityTest.Inst in : RepJdkParityTest.instances()) {
            String p = RepJdkParityTest.plain(in.content());
            String r = in.s();
            int n = p.length();
            for (String prefix : new String[]{"", "x", "€"}) {
                String what = in.label() + " after " + RepJdkParityTest.esc(prefix);
                for (int b = 0; b <= n; b++) {
                    for (int e = b; e <= n; e++) {
                        int fb = b;
                        int fe = e;
                        ranges++;
                        // the ranged append is the invented twin's (twinRangedAppendIsTheJdks); the stock
                        // appendChars on HotSpot reads s.value() (the analysis redirects it where reps exist)
                        RepJdkParityTest.same(what + " insert(1,cs," + b + "," + e + ")",
                                        () -> new StringBuilder(prefix).append("yz").insert(1, p, fb, fe).toString(),
                                        () -> new StringBuilder(prefix).append("yz").insert(1, r, fb, fe).toString(), true);
                    }
                }
                // the whole string: putStringAt (insert) and the full-range append
                RepJdkParityTest.same(what + " insert(0,cs,0,n)", () -> new StringBuilder(prefix).insert(0, p, 0, n).toString(),
                                () -> new StringBuilder(prefix).insert(0, r, 0, n).toString(), true);
                RepJdkParityTest.same(what + " insert(len,cs,0,n)", () -> new StringBuilder(prefix).insert(prefix.length(), p, 0, n).toString(),
                                () -> new StringBuilder(prefix).insert(prefix.length(), r, 0, n).toString(), true);
                RepJdkParityTest.same(what + " StringBuffer insert(0,cs,0,n)", () -> new StringBuffer(prefix).insert(0, p, 0, n).toString(),
                                () -> new StringBuffer(prefix).insert(0, r, 0, n).toString(), true);
                // out-of-range: the JDK's own exception before any copy
                RepJdkParityTest.same(what + " append(cs,-1,n)", () -> new StringBuilder(prefix).append(p, -1, n).toString(),
                                () -> new StringBuilder(prefix).append(r, -1, n).toString(), true);
                RepJdkParityTest.same(what + " append(cs,0,n+1)", () -> new StringBuilder(prefix).append(p, 0, n + 1).toString(),
                                () -> new StringBuilder(prefix).append(r, 0, n + 1).toString(), true);
            }
        }
        Assert.assertTrue("non-vacuous: " + ranges, ranges > 1000);
    }

    /** The twin is private in java.lang; its runtime parity needs {@code --open-packages java.base/java.lang=ALL-UNNAMED}. */
    static boolean javaLangOpen() {
        return Object.class.getModule().isOpen("java.lang", RangeCopyParityTest.class.getModule());
    }

    /**
     * The ranged append through the invented twin {@code appendCharsRangeCopy} (the body the analysis redirects
     * {@code append(CharSequence,int,int)} to where reps exist) equals the JDK's append on the plain string, for every
     * rep instance and range, Latin-1 and UTF-16 builders; and its three ranged-copy call sites keep the invoker
     * guarantee (a flat recording String). Skipped (visibly) unless java.lang is open to the test.
     */
    @Test
    public void twinRangedAppendIsTheJdks() throws ReflectiveOperationException {
        org.junit.Assume.assumeTrue("needs --open-packages java.base/java.lang=ALL-UNNAMED", javaLangOpen());
        int ranges = 0;
        for (RepJdkParityTest.Inst in : RepJdkParityTest.instances()) {
            String p = RepJdkParityTest.plain(in.content());
            String r = in.s();
            int n = p.length();
            for (String prefix : new String[]{"", "x", "\u20ac"}) {
                String what = in.label() + " after " + RepJdkParityTest.esc(prefix);
                for (int b = 0; b <= n; b++) {
                    for (int e = b; e <= n; e++) {
                        int fb = b;
                        int fe = e;
                        ranges++;
                        RepJdkParityTest.same(what + " twin append(cs," + b + "," + e + ")",
                                        () -> new StringBuilder(prefix).append(p, fb, fe).append('!').toString(),
                                        () -> twinAppend(prefix, r, fb, fe) + "!", true);
                        RepJdkParityTest.same(what + " twin append twice(cs," + b + "," + e + ")",
                                        () -> new StringBuffer(prefix).append(p, fb, fe).append(p, fb, fe).toString(),
                                        () -> twinAppend(twinAppend(prefix, r, fb, fe), r, fb, fe), true);
                    }
                }
            }
        }
        Assert.assertTrue("non-vacuous: " + ranges, ranges > 1000);
        Constructor<?> recording = recordingStringConstructor();
        CALLS.clear();
        for (String src : new String[]{"abcdefgh", "ab\u20accdefg", "abcdef\u20ac", "\u20ac\u20acx"}) {
            String r = (String) recording.newInstance(src.value(), src.coder());
            for (String prefix : new String[]{"", "x", "\u20ac"}) {
                for (int b = 0; b <= src.length(); b++) {
                    for (int e = b; e <= src.length(); e++) {
                        Assert.assertEquals(new StringBuilder(prefix).append(src, b, e).toString(), twinAppend(prefix, r, b, e));
                    }
                }
            }
        }
        Set<String> sites = new TreeSet<>();
        for (String c : CALLS) {
            int sp = c.indexOf(' ');
            sites.add(c.substring(0, sp));
            String pair = c.substring(sp + 1);
            Assert.assertTrue("invoker guarantee violated: " + c, pair.equals("this=0 dst=0") || pair.equals("this=1 dst=1") || pair.equals("this=0 dst=1"));
        }
        Assert.assertEquals("the twin's ranged-copy call sites", Set.of("java.lang.AbstractStringBuilder#appendCharsRangeCopy@25", "java.lang.AbstractStringBuilder#appendCharsRangeCopy@93",
                        "java.lang.AbstractStringBuilder#appendCharsRangeCopy@138"), sites);
    }

    /**
     * {@code prefix + s.subSequence(b, e)} as {@code AbstractStringBuilder.append(CharSequence,int,int)} computes
     * it with the invented twin {@code appendCharsRangeCopy(byte[],byte,int,String,int,int)}: a builder buffer holding
     * {@code prefix} (Latin-1 if it is, else UTF-16) with room for the range, the twin, then the content of the (possibly
     * inflated) buffer. The result is a plain compact String (as {@code toString} makes it).
     */
    static String twinAppend(String prefix, String s, int b, int e) {
        try {
            Method twin = Class.forName("java.lang.AbstractStringBuilder").getDeclaredMethod("appendCharsRangeCopy", byte[].class, byte.class, int.class, String.class, int.class,
                            int.class);
            twin.setAccessible(true);
            boolean latin1 = prefix.chars().allMatch(c -> c <= 0xFF);
            int count = prefix.length();
            int len = e - b;
            byte[] value = new byte[(count + len) << (latin1 ? 0 : 1)];
            for (int i = 0; i < count; i++) {
                putChar(value, latin1, i, prefix.charAt(i));
            }
            byte[] out = (byte[]) twin.invoke(null, value, (byte) (latin1 ? 0 : 1), count, s, b, e);
            boolean outLatin1 = latin1 && out == value;
            char[] chars = new char[count + len];
            for (int i = 0; i < chars.length; i++) {
                chars[i] = outLatin1 ? (char) (out[i] & 0xFF) : getChar(out, i);
            }
            return new String(chars);
        } catch (java.lang.reflect.InvocationTargetException ex) {
            throw ex.getCause() instanceof RuntimeException re ? re : new RuntimeException(ex.getCause());
        } catch (ReflectiveOperationException ex) {
            throw new AssertionError("the builder JDK must declare AbstractStringBuilder.appendCharsRangeCopy", ex);
        }
    }

    /** StringUTF16's layout: native byte order (x86: little-endian). */
    private static void putChar(byte[] v, boolean latin1, int i, char c) {
        if (latin1) {
            v[i] = (byte) c;
        } else if (java.nio.ByteOrder.nativeOrder() == java.nio.ByteOrder.LITTLE_ENDIAN) {
            v[2 * i] = (byte) c;
            v[2 * i + 1] = (byte) (c >> 8);
        } else {
            v[2 * i] = (byte) (c >> 8);
            v[2 * i + 1] = (byte) c;
        }
    }

    private static char getChar(byte[] v, int i) {
        if (java.nio.ByteOrder.nativeOrder() == java.nio.ByteOrder.LITTLE_ENDIAN) {
            return (char) ((v[2 * i] & 0xFF) | ((v[2 * i + 1] & 0xFF) << 8));
        }
        return (char) (((v[2 * i] & 0xFF) << 8) | (v[2 * i + 1] & 0xFF));
    }

    /**
     * Inlining parity: the builder JDK spells the ranged copy's coder test as
     * {@code coder == LATIN1 || coder() != LATIN1} (so an inlined caller's constant/known coder folds it), which equals
     * the original {@code coder() == coder} only under the method's invoker guarantee: the destination coder equals
     * the receiver's, or the receiver is Latin-1 and the destination UTF-16. A flat recording String subclass (real
     * value, String's body via {@code super}; generated, see {@link #recordingStringConstructor()}) pins that every JDK
     * call site of the method keeps the guarantee for every builder coder x source coder x range of
     * {@code append(cs,b,e)}, {@code StringBuffer.append(cs,b,e)}, {@code insert(i,cs,b,e)} and whole-String
     * {@code insert}, that exactly the known call sites are reached (with the stock builder only {@code putStringAt@37},
     * since the stock {@code appendChars} copies directly; with the twin {@code appendCharsRangeCopy@25/93/138}), and that
     * every allowed coder pair occurs.
     */
    static final List<String> CALLS = new ArrayList<>();

    /** Called by the generated recording subclass' {@code getBytes} override before it runs String's body. */
    static void recordRangedCopy(String self, byte dstCoder) {
        StackWalker.StackFrame caller = StackWalker.getInstance().walk(st -> st.skip(2).findFirst().orElseThrow());
        CALLS.add(caller.getClassName() + "#" + caller.getMethodName() + "@" + caller.getByteCodeIndex() + " this=" + self.coder() + " dst=" + dstCoder);
    }

    /**
     * A flat recording String subclass: {@code (byte[] value, byte coder)} constructor, and a {@code getBytes} override
     * that records the call then runs String's body via {@code super}. Generated at run time (ClassFile API) and defined
     * in this package, not compiled into the test jar: {@link RepPinSupport#repClasses()} pins every String subclass of
     * the svm class files to the rep classes.
     */
    private static Constructor<?> recordingCtor;

    /** Memoized (two tests use the generated class; a second definition would be a duplicate). */
    static synchronized Constructor<?> recordingStringConstructor() throws ReflectiveOperationException {
        if (recordingCtor == null) {
            recordingCtor = defineRecordingString();
        }
        return recordingCtor;
    }

    private static Constructor<?> defineRecordingString() throws ReflectiveOperationException {
        ClassDesc str = ConstantDescs.CD_String;
        ClassDesc bytes = ConstantDescs.CD_byte.arrayType();
        MethodTypeDesc ctor = MethodTypeDesc.of(ConstantDescs.CD_void, bytes, ConstantDescs.CD_byte);
        MethodTypeDesc gb = MethodTypeDesc.of(ConstantDescs.CD_void, bytes, ConstantDescs.CD_int, ConstantDescs.CD_int, ConstantDescs.CD_byte, ConstantDescs.CD_int);
        MethodTypeDesc rec = MethodTypeDesc.of(ConstantDescs.CD_void, str, ConstantDescs.CD_byte);
        ClassDesc self = ClassDesc.of(RangeCopyParityTest.class.getPackageName() + ".C96RecordingStringGen");
        ClassDesc owner = ClassDesc.of(RangeCopyParityTest.class.getName());
        byte[] cf = ClassFile.of().build(self, cb -> cb.withSuperclass(str).withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL)
                        .withMethodBody("<init>", ctor, ClassFile.ACC_PUBLIC, code -> code.aload(0).aload(1).iload(2).invokespecial(str, "<init>", ctor).return_())
                        .withMethodBody("getBytes", gb, ClassFile.ACC_PROTECTED, code -> code.aload(0).iload(4).invokestatic(owner, "recordRangedCopy", rec)
                                        .aload(0).aload(1).iload(2).iload(3).iload(4).iload(5).invokespecial(str, "getBytes", gb).return_()));
        return MethodHandles.lookup().defineClass(cf).getConstructor(byte[].class, byte.class);
    }

    @Test
    public void rangedCopyCallersKeepTheInvokerGuarantee() throws ReflectiveOperationException {
        Constructor<?> recording = recordingStringConstructor();
        CALLS.clear();
        Set<String> sites = new TreeSet<>();
        Set<String> pairs = new TreeSet<>();
        int calls = 0;
        for (String src : new String[]{"abcdefgh", "ab\u20accdefg", "abcdef\u20ac", "\u20ac\u20acx"}) {
            String r = (String) recording.newInstance(src.value(), src.coder());
            int n = src.length();
            Assert.assertTrue(src, r.length() == n && src.contentEquals(r) && r.coder() == src.coder());
            for (String prefix : new String[]{"", "x", "\u20ac"}) {
                for (int b = 0; b <= n; b++) {
                    for (int e = b; e <= n; e++) {
                        Assert.assertEquals(new StringBuilder(prefix).append(src, b, e).toString(), new StringBuilder(prefix).append(r, b, e).toString());
                        Assert.assertEquals(new StringBuffer(prefix).append(src, b, e).toString(), new StringBuffer(prefix).append(r, b, e).toString());
                        Assert.assertEquals(new StringBuilder(prefix).append("yz").insert(1, src, b, e).toString(),
                                        new StringBuilder(prefix).append("yz").insert(1, r, b, e).toString());
                    }
                }
                Assert.assertEquals(new StringBuilder(prefix).insert(0, src, 0, n).toString(), new StringBuilder(prefix).insert(0, r, 0, n).toString());
                Assert.assertEquals(new StringBuffer(prefix).insert(0, src, 0, n).toString(), new StringBuffer(prefix).insert(0, r, 0, n).toString());
            }
        }
        for (String c : CALLS) {
            calls++;
            int sp = c.indexOf(' ');
            sites.add(c.substring(0, sp));
            String pair = c.substring(sp + 1);
            pairs.add(pair);
            Assert.assertTrue("invoker guarantee violated (dst coder must equal this coder, or this=LATIN1 and dst=UTF16): " + c,
                            pair.equals("this=0 dst=0") || pair.equals("this=1 dst=1") || pair.equals("this=0 dst=1"));
        }
        Assert.assertEquals("the JDK call sites of the ranged copy", Set.of("java.lang.AbstractStringBuilder#putStringAt@37"), sites); // the stock appendChars copies directly
        Assert.assertEquals("every allowed coder pair occurs", Set.of("this=0 dst=0", "this=1 dst=1", "this=0 dst=1"), pairs);
        Assert.assertTrue("non-vacuous: " + calls, calls > 30); // putStringAt only (the append sites are the twin's)
    }

    /**
     * The static counterpart of {@link #rangedCopyCallersKeepTheInvokerGuarantee()}, which only sees call sites its
     * entry points reach. Every {@code invoke*} of {@code getBytes([BIIBI)V} (any owner) in every class file of the
     * builder JDK's {@code java.base} and of the svm class files on the test path ({@link RepPinSupport#scannedRoots()})
     * is collected: the sites must be exactly {@code AbstractStringBuilder#appendCharsRangeCopy@25/93/138} (the twin)
     * and {@code #putStringAt@37} (where the invoker guarantee is argued and dynamically pinned), and no svm class may
     * invoke it (the reps only declare overrides). A new caller must first show the guarantee. An inline-cache entry for
     * this method may only redirect these four sites.
     */
    @Test
    public void rangedCopyCallSitesAreExactlyTheFourGuaranteedOnes() throws Exception {
        Set<String> jdkSites = new TreeSet<>();
        int[] jdkClasses = {0};
        FileSystem jrt = FileSystems.getFileSystem(URI.create("jrt:/"));
        Path base = jrt.getPath("/modules/java.base");
        try (Stream<Path> files = Files.walk(base)) {
            for (Path f : (Iterable<Path>) files.filter(x -> x.toString().endsWith(".class"))::iterator) {
                jdkClasses[0]++;
                rangedCopyInvokes(Files.readAllBytes(f), jdkSites);
            }
        }
        Assert.assertTrue("non-vacuous java.base scan: " + jdkClasses[0], jdkClasses[0] > 5000);
        /*
         * The builder-append mirrors copy only through the ranged copy (appendRep(String,int,int) x3,
         * insertRep(int,String,int,int) x3, and the whole-string copies of appendRep(String)/insertRep(int,String)/replaceRep
         * as getBytes(dst, 0, i, c, len) with c = the buffer coder after coder | str.coder()). Invoker guarantee, argued per
         * site: a Latin-1 string into a Latin-1 buffer passes LATIN1 (0/0); after an inflation the string is UTF-16 and
         * UTF16 is passed (1/1); a UTF-16 buffer passes UTF16 for any string (0/1 or 1/1); the full-length insert passes
         * the buffer coder after inflateIfNeededFor (stock putStringAt). The mirror sites are listed by member (their
         * bcis are not pinned here; AppendMirrorTest scans the mirrors).
         */
        Set<String> mirrorSites = new TreeSet<>();
        jdkSites.removeIf(x -> (x.startsWith("java/lang/AbstractStringBuilder#appendRep@") || x.startsWith("java/lang/AbstractStringBuilder#insertRep@") ||
                        x.startsWith("java/lang/AbstractStringBuilder#replaceRep@")) && mirrorSites.add(x));
        Assert.assertEquals("3 ranged copies in each ranged mirror + 1 whole-string copy in appendRep/insertRep/replaceRep " + mirrorSites, 9, mirrorSites.size());
        Assert.assertEquals("the java.base call sites of String.getBytes([BIIBI)V", Set.of("java/lang/AbstractStringBuilder#appendCharsRangeCopy@25",
                        "java/lang/AbstractStringBuilder#appendCharsRangeCopy@93",
                        "java/lang/AbstractStringBuilder#appendCharsRangeCopy@138", "java/lang/AbstractStringBuilder#putStringAt@37"), jdkSites);
        Set<String> svmSites = new TreeSet<>();
        int[] svmClasses = {0};
        RepPinSupport.forEachClassFile(bytes -> {
            svmClasses[0]++;
            rangedCopyInvokes(bytes, svmSites);
        });
        Assert.assertTrue("non-vacuous svm scan: " + svmClasses[0] + " " + RepPinSupport.scannedRoots(), svmClasses[0] > 1000);
        Assert.assertEquals("no svm class invokes the ranged copy (roots " + RepPinSupport.scannedRoots() + ")", Set.of(), svmSites);
    }

    /** Adds {@code owner#method@bci} of every invoke of {@code getBytes([BIIBI)V} (any owner) in the class file. */
    static void rangedCopyInvokes(byte[] bytes, Set<String> out) {
        ClassModel cm;
        try {
            cm = ClassFile.of().parse(bytes);
        } catch (IllegalArgumentException e) {
            return; // not a class file this JDK parses
        }
        String owner = cm.thisClass().asInternalName();
        for (MethodModel mm : cm.methods()) {
            CodeModel code = mm.code().orElse(null);
            if (code == null) {
                continue;
            }
            int bci = 0;
            for (CodeElement ce : code) {
                if (ce instanceof Instruction ins) {
                    if (ins instanceof InvokeInstruction inv && inv.name().equalsString("getBytes") && inv.type().equalsString("([BIIBI)V")) {
                        out.add(owner + "#" + mm.methodName().stringValue() + "@" + bci);
                    }
                    bci += ins.sizeInBytes();
                }
            }
        }
    }
}
