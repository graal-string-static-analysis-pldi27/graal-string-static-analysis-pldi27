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

import com.oracle.svm.core.NeverInline;

/**
 * Debug only ({@code svm.stringanalysis.ic.exactfirst.super.check=1}): the checked replacement of the
 * trusted String narrowing at a D1 ({@code EXACT_RECV}) site's else. A receiver that is neither null nor a String fails
 * loudly with the site and its class. Never emitted at the default (0).
 */
public final class D1Check {

    private D1Check() {
    }

    @NeverInline("the parent's after-analysis census reads this invoke's argument state")
    public static String check(Object receiver, String site) {
        if (receiver == null || receiver instanceof String) {
            return (String) receiver;
        }
        throw new IllegalStateException("string-analysis exact-receiver CHECK failed: receiver class " + receiver.getClass().getName() + " at the EXACT_RECV site " + site);
    }
}
