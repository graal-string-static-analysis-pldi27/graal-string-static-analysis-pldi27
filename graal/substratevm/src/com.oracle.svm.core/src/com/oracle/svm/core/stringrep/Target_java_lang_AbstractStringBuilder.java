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
import com.oracle.svm.core.annotate.TargetClass;

/**
 * An alias of the existing JDK field {@code AbstractStringBuilder.maybeLatin1}, read by the builder-view factories of
 * {@link StringView}. JDK 25 sets it in every operation that can remove the last char above 0xFF of a UTF-16 builder
 * (setLength shrinking, setCharAt, delete, deleteCharAt, replace; inherited through append(AbstractStringBuilder) and
 * the copy constructor) and never clears it; the builder's toString tries to compress a UTF-16 builder only when set.
 * Also {@code count} (not final), read by the {@code StringBuffer} view factories under the buffer's monitor.
 */
@TargetClass(className = "java.lang.AbstractStringBuilder")
final class Target_java_lang_AbstractStringBuilder {
    // Checkstyle: stop
    @Alias boolean maybeLatin1;
    @Alias int count;
    // Checkstyle: resume
}
