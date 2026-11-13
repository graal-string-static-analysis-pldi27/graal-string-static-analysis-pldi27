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
import java.lang.reflect.Modifier;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.svm.core.annotate.Alias;
import com.oracle.svm.core.annotate.RecomputeFieldValue;
import com.oracle.svm.core.annotate.TargetClass;
import com.oracle.svm.core.stringrep.StringView;

/**
 * A plain {@code @Alias} of a final
 * JDK field makes the substituted field non-final image-wide (AnnotationSubstitutionProcessor: {@code isFinal =
 * original.isFinal() && annotated.isFinal()}, and an alias field cannot be declared final), so its loads stop folding
 * (e.g. {@code String.coder}, or a class-init simulation that reads such a field). Every {@code @Alias} field of a
 * {@code stringrep} {@code @TargetClass} (scanned) whose original is final must carry
 * {@code @RecomputeFieldValue(isFinal = true)}.
 */
public class AliasFinalFieldTest {

    @Test
    public void everyAliasOfAFinalFieldStaysFinal() throws Exception {
        ClassLoader cl = StringView.class.getClassLoader();
        TreeSet<String> checked = new TreeSet<>();
        TreeSet<String> bad = new TreeSet<>();
        for (String simple : ClinitSimulationParityTest.stringrepClassNames()) {
            Class<?> c = Class.forName(StringView.class.getPackageName() + "." + simple, false, cl);
            TargetClass tc = c.getAnnotation(TargetClass.class);
            if (tc == null) {
                continue;
            }
            Assert.assertEquals(simple + ": no inner-class / provider targets in stringrep", 0, tc.innerClass().length);
            Class<?> target = tc.value() != TargetClass.class ? tc.value() : Class.forName(tc.className(), false, cl);
            for (Field a : c.getDeclaredFields()) {
                if (a.getAnnotation(Alias.class) == null) {
                    continue;
                }
                Field original = target.getDeclaredField(a.getName());
                if (!Modifier.isFinal(original.getModifiers())) {
                    continue;
                }
                RecomputeFieldValue r = a.getAnnotation(RecomputeFieldValue.class);
                String key = simple + "." + a.getName();
                checked.add(key);
                if (r == null || !r.isFinal() || r.kind() != RecomputeFieldValue.Kind.None) {
                    bad.add(key);
                }
            }
        }
        Assert.assertEquals("@Alias of a final field without @RecomputeFieldValue(kind = None, isFinal = true)", new TreeSet<String>(), bad);
        /* Non-vacuous: the String aliases (value, coder) and the final StringJoiner fields. */
        Assert.assertEquals("[Target_java_lang_String_StringRep.coder, Target_java_lang_String_StringRep.value, " +
                        "Target_java_util_StringJoiner.delimiter, Target_java_util_StringJoiner.prefix, Target_java_util_StringJoiner.suffix]", checked.toString());
    }
}
