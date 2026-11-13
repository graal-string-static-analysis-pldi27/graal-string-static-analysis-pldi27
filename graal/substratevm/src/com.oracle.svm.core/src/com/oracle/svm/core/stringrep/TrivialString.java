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

/**
 * A test representation (not a production one) showing that {@code String} can be subclassed in Native Image once
 * the builder JDK has de-finalized it: a flat one-char subclass whose inherited {@code value}/{@code coder} are set by
 * {@code super(...)}, so the {@code String.equals} intrinsic's field reads stay correct.
 */
public class TrivialString extends String {

    private final byte payload;

    private TrivialString(byte payload) {
        super(String.valueOf((char) payload));
        this.payload = payload;
    }

    public static TrivialString create(byte payload) {
        return new TrivialString(payload);
    }

    @Override
    public char charAt(int index) {
        if (index == 0) {
            return (char) payload;
        }
        // The JDK's own bounds check and StringIndexOutOfBoundsException.
        return super.charAt(index);
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof TrivialString ts) {
            return this.payload == ts.payload;
        }
        if (o instanceof String s) {
            return s.length() == 1 && s.charAt(0) == (char) payload;
        }
        return false;
    }

    @Override
    public int hashCode() {
        // The JDK's hash of a one-char String is the char; (char) maps a negative payload to its content
        return (char) payload;
    }
}
