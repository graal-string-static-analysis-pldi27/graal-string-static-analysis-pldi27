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

import java.io.ByteArrayInputStream;
import java.io.DataInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * JDK-model scan harness: the Fieldref entries of a class file's constant pool, as "pkg.Class.field" (Java names); and
 * the {@code @TargetClass} target and declared methods of an SVM substitution class.
 */
final class JdkModelClassScan {

    private JdkModelClassScan() {
    }

    static List<String> fieldrefs(byte[] bytes) throws IOException {
        DataInputStream in = new DataInputStream(new ByteArrayInputStream(bytes));
        if (in.readInt() != 0xCAFEBABE) {
            return List.of();
        }
        in.readUnsignedShort();
        in.readUnsignedShort();
        int n = in.readUnsignedShort();
        String[] utf8 = new String[n];
        int[] classNameIdx = new int[n];
        int[] natNameIdx = new int[n];
        List<int[]> fieldrefs = new ArrayList<>();
        for (int i = 1; i < n; i++) {
            int tag = in.readUnsignedByte();
            switch (tag) {
                case 1 -> utf8[i] = in.readUTF();
                case 3, 4 -> in.readInt();
                case 5, 6 -> {
                    in.readLong();
                    i++;
                }
                case 7, 8, 16, 19, 20 -> {
                    int x = in.readUnsignedShort();
                    if (tag == 7) {
                        classNameIdx[i] = x;
                    }
                }
                case 9 -> fieldrefs.add(new int[]{in.readUnsignedShort(), in.readUnsignedShort()});
                case 10, 11, 17, 18 -> in.readInt();
                case 12 -> {
                    natNameIdx[i] = in.readUnsignedShort();
                    in.readUnsignedShort();
                }
                case 15 -> {
                    in.readUnsignedByte();
                    in.readUnsignedShort();
                }
                default -> throw new IOException("constant pool tag " + tag);
            }
        }
        List<String> out = new ArrayList<>();
        for (int[] fr : fieldrefs) {
            String cls = utf8[classNameIdx[fr[0]]];
            String name = utf8[natNameIdx[fr[1]]];
            if (cls != null && name != null) {
                out.add(cls.replace('/', '.') + "." + name);
            }
        }
        return out;
    }

    /** An SVM substitution class: its target (Java name; "?" = a classNameProvider) and its declared methods "name(desc)". */
    record Substitution(String self, String target, List<String> methods) {
    }

    private static final String TARGET_CLASS = "Lcom/oracle/svm/core/annotate/TargetClass;";

    /** The {@code @TargetClass} substitution a class file declares, or null when it has none. */
    static Substitution substitution(byte[] bytes) throws IOException {
        DataInputStream in = new DataInputStream(new ByteArrayInputStream(bytes));
        if (in.readInt() != 0xCAFEBABE) {
            return null;
        }
        in.readUnsignedShort();
        in.readUnsignedShort();
        int n = in.readUnsignedShort();
        String[] utf8 = new String[n];
        int[] classNameIdx = new int[n];
        boolean mentions = false;
        for (int i = 1; i < n; i++) {
            int tag = in.readUnsignedByte();
            switch (tag) {
                case 1 -> {
                    utf8[i] = in.readUTF();
                    mentions |= utf8[i].equals(TARGET_CLASS);
                }
                case 3, 4 -> in.readInt();
                case 5, 6 -> {
                    in.readLong();
                    i++;
                }
                case 7, 8, 16, 19, 20 -> {
                    int x = in.readUnsignedShort();
                    if (tag == 7) {
                        classNameIdx[i] = x;
                    }
                }
                case 9, 10, 11, 12, 17, 18 -> in.readInt();
                case 15 -> {
                    in.readUnsignedByte();
                    in.readUnsignedShort();
                }
                default -> throw new IOException("constant pool tag " + tag);
            }
        }
        if (!mentions) {
            return null;
        }
        in.readUnsignedShort();
        String self = utf8[classNameIdx[in.readUnsignedShort()]].replace('/', '.');
        in.readUnsignedShort();
        in.skipBytes(2 * in.readUnsignedShort());
        int fields = in.readUnsignedShort();
        for (int i = 0; i < fields; i++) {
            in.skipBytes(6);
            skipAttributes(in);
        }
        List<String> methods = new ArrayList<>();
        int ms = in.readUnsignedShort();
        for (int i = 0; i < ms; i++) {
            in.readUnsignedShort();
            String name = utf8[in.readUnsignedShort()];
            String desc = utf8[in.readUnsignedShort()];
            // a substitution class's own (unannotated) constructor substitutes nothing; a @Substitute one does
            boolean substitute = substituteAnnotated(in, utf8);
            if (!name.equals("<init>") || substitute) {
                methods.add(name + desc);
            }
        }
        int attrs = in.readUnsignedShort();
        for (int i = 0; i < attrs; i++) {
            String an = utf8[in.readUnsignedShort()];
            int len = in.readInt();
            if (!an.equals("RuntimeVisibleAnnotations")) {
                in.skipBytes(len);
                continue;
            }
            int na = in.readUnsignedShort();
            for (int a = 0; a < na; a++) {
                String type = utf8[in.readUnsignedShort()];
                int pairs = in.readUnsignedShort();
                String value = null;
                String className = null;
                List<String> inner = new ArrayList<>();
                boolean provider = false;
                for (int p = 0; p < pairs; p++) {
                    String en = utf8[in.readUnsignedShort()];
                    List<String> vals = new ArrayList<>();
                    elementValue(in, utf8, vals);
                    switch (en) {
                        case "value" -> value = vals.isEmpty() ? null : vals.get(0);
                        case "className" -> className = vals.isEmpty() ? null : vals.get(0);
                        case "innerClass" -> inner.addAll(vals);
                        case "classNameProvider" -> provider = true;
                        default -> {
                        }
                    }
                }
                if (type.equals(TARGET_CLASS)) {
                    String t = provider ? "?"
                                    : className != null && !className.isEmpty() ? className
                                                    : value != null && value.startsWith("L") ? value.substring(1, value.length() - 1).replace('/', '.') : "?";
                    for (String ic : inner) {
                        t = t + "$" + ic;
                    }
                    return new Substitution(self, t, methods);
                }
            }
        }
        return null;
    }

    /** Reads a member's attributes; true when one of its annotations is {@code @Substitute}. */
    private static boolean substituteAnnotated(DataInputStream in, String[] utf8) throws IOException {
        boolean found = false;
        int n = in.readUnsignedShort();
        for (int i = 0; i < n; i++) {
            String an = utf8[in.readUnsignedShort()];
            int len = in.readInt();
            if (!an.equals("RuntimeVisibleAnnotations") && !an.equals("RuntimeInvisibleAnnotations")) {
                in.skipBytes(len);
                continue;
            }
            int na = in.readUnsignedShort();
            for (int a = 0; a < na; a++) {
                String type = utf8[in.readUnsignedShort()];
                found |= type.equals("Lcom/oracle/svm/core/annotate/Substitute;");
                int pairs = in.readUnsignedShort();
                for (int p = 0; p < pairs; p++) {
                    in.readUnsignedShort();
                    elementValue(in, utf8, new ArrayList<>());
                }
            }
        }
        return found;
    }

    private static void skipAttributes(DataInputStream in) throws IOException {
        int n = in.readUnsignedShort();
        for (int i = 0; i < n; i++) {
            in.readUnsignedShort();
            in.skipBytes(in.readInt());
        }
    }

    /** One annotation element value; strings and class descriptors are collected into {@code out}. */
    private static void elementValue(DataInputStream in, String[] utf8, List<String> out) throws IOException {
        int tag = in.readUnsignedByte();
        switch (tag) {
            case 's', 'c' -> out.add(utf8[in.readUnsignedShort()]);
            case 'B', 'C', 'D', 'F', 'I', 'J', 'S', 'Z' -> in.readUnsignedShort();
            case 'e' -> in.readInt();
            case '@' -> {
                in.readUnsignedShort();
                int pairs = in.readUnsignedShort();
                for (int p = 0; p < pairs; p++) {
                    in.readUnsignedShort();
                    elementValue(in, utf8, new ArrayList<>());
                }
            }
            case '[' -> {
                int k = in.readUnsignedShort();
                for (int i = 0; i < k; i++) {
                    elementValue(in, utf8, out);
                }
            }
            default -> throw new IOException("element value tag " + (char) tag);
        }
    }
}
