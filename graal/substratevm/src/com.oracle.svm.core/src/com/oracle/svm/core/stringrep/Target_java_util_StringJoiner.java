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
 * StringJoiner accumulator: read-only access to the JDK 25
 * {@code java.util.StringJoiner} fields for {@link InterleavedStringArray#ofJoiner}, the replacement of an admitted
 * user-code {@code StringJoiner.toString()}. No field is added and no JDK body is changed.
 */
@TargetClass(className = "java.util.StringJoiner")
final class Target_java_util_StringJoiner {
    // Checkstyle: stop
    /*
     * AliasFinalFieldTest: prefix/delimiter/suffix are final in the JDK; a plain
     * alias would make them non-final image-wide (no folding of their loads).
     */
    @Alias @RecomputeFieldValue(kind = Kind.None, isFinal = true) String prefix;
    @Alias @RecomputeFieldValue(kind = Kind.None, isFinal = true) String delimiter;
    @Alias @RecomputeFieldValue(kind = Kind.None, isFinal = true) String suffix;
    @Alias String[] elts;
    @Alias int size;
    @Alias int len;
    // Checkstyle: resume
}
