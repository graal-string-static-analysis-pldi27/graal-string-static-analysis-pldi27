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
package com.oracle.svm.core.stringrep;

import com.oracle.svm.core.annotate.Alias;
import com.oracle.svm.core.annotate.RecomputeFieldValue;
import com.oracle.svm.core.annotate.RecomputeFieldValue.Kind;
import com.oracle.svm.core.annotate.TargetClass;

/**
 * Aliases of existing {@code java.lang.String} members (no new member). The constructor alias is the JDK's
 * value-sharing {@code String(byte[] value, byte coder)}, used by {@code StringView.builderCopy} where the JDK's
 * builder {@code toString} makes one plain copy (a Latin-1 builder, or a UTF-16 builder with {@code maybeLatin1}
 * clear); the array passed is always a fresh copy. Image runtime only (an alias has no hosted body).
 */
@TargetClass(java.lang.String.class)
final class Target_java_lang_String_StringRep {
    @Alias //
    @SuppressWarnings("unused")
    Target_java_lang_String_StringRep(byte[] value, byte coder) {
    }

    /**
     * The protected {@code String.getBytes(byte[], int, byte)}: {@link RepConcat#doConcat}'s copy of each operand, a
     * virtual call a rep's own override serves, as in the JDK's {@code StringConcatHelper.doConcat}. The invoker
     * guarantees {@code coder >= coder()}.
     */
    @Alias //
    native void getBytes(byte[] dst, int dstBegin, byte coder);

    /**
     * {@code String.value} (annotated exactly as the {@code Target_java_lang_String} alias in
     * {@code JavaLangSubstitutions}) and {@code String.coder}, read by {@link SingleByteString#equals}. Both must keep
     * {@code isFinal = true}: a plain {@code @Alias} of a final field makes the substituted field non-final
     * (AnnotationSubstitutionProcessor: {@code isFinal = original.isFinal() && annotated.isFinal()}), which stops
     * constant folding of {@code String.coder} image-wide (a class-init simulation reaching the {@code String.equals}
     * coder test then fails).
     */
    @Alias @RecomputeFieldValue(kind = Kind.None, isFinal = true) //
    byte[] value;

    @Alias @RecomputeFieldValue(kind = Kind.None, isFinal = true) //
    byte coder;
}
