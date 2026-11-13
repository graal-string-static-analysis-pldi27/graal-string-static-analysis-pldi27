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

import java.util.Set;

import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * SVM's monitor operations as a VM primitive (applied at the forward call crossing,
 * {@code RecursiveTracking.invokeUsage}).
 * <p>
 * {@code Object.wait/notify/notifyAll}, {@code Thread.holdsLock} and {@code Throwable.fillInStackTrace} (run by the
 * {@code Throwable} constructors, through {@code isLockedByAnyThread}) are substituted by calls into
 * {@code MonitorSupport}. Its implementation raw-reads and CASes the object's hidden monitor slot (a VM-reserved word
 * with no Java field) or keys a private weak identity map with the object. The engine cannot tell which word such a
 * raw access touches, so entering that code would refuse the whole object ({@code UNSAFE_ACCESS}), and through the
 * refusal inheritance everything stored below it.
 * <p>
 * The model: at a call whose resolved target is one of {@link #OPERATIONS}, the object argument (argument slot
 * {@link #OBJECT_SLOT}) is observed and the callee is not entered at that slot, exactly as the {@code MonitorEnterNode}
 * of a {@code synchronized} block already is (the engine's observation list); every other slot is entered as before.
 * The model is keyed on method identity (declaring class + name + descriptor), like the thread-local model. Its premise
 * and the completeness of the list are pinned over SVM's bytecode by {@code MonitorPrimitiveTest}: the operations
 * read nothing of the object but its class, its address (JFR) and the hidden slot; they store it nowhere except as an
 * identity key of the private weak monitor map (only queried by identity); they never return it, throw it or hand it
 * to other code. (A {@code Class} object is replaced by its hub's VM companion; a Class is never an allocation-site
 * object of the analysis.)
 */
final class MonitorPrimitive {

    private MonitorPrimitive() {
    }

    /** The declaring classes of the modelled operations: the abstract API and its only implementation. */
    static final Set<String> CLASSES = Set.of("com.oracle.svm.core.monitor.MonitorSupport", "com.oracle.svm.core.monitor.MultiThreadedMonitorSupport");

    /**
     * The modelled operations (name + descriptor): every operation of {@code MonitorSupport} on an object. The object is
     * the first declared parameter of each.
     */
    static final Set<String> OPERATIONS = Set.of(
                    "monitorEnter(Ljava/lang/Object;Lcom/oracle/svm/core/monitor/MonitorInflationCause;)V",
                    "monitorExit(Ljava/lang/Object;Lcom/oracle/svm/core/monitor/MonitorInflationCause;)V",
                    "prepareRelockObject(Ljava/lang/Object;)Ljava/lang/Object;",
                    "doRelockObject(Ljava/lang/Object;Ljava/lang/Object;)V",
                    "isLockedByCurrentThread(Ljava/lang/Object;)Z",
                    "isLockedByAnyThread(Ljava/lang/Object;)Z",
                    "wait(Ljava/lang/Object;J)V",
                    "doWait(Ljava/lang/Object;J)V",
                    "notify(Ljava/lang/Object;Z)V",
                    "ensureInitialized(Ljava/lang/Object;)V");

    /** The object's argument slot (slot 0 is the {@code MonitorSupport} singleton, the receiver). */
    static final int OBJECT_SLOT = 1;

    /** Is {@code m} one of the modelled operations (by method identity)? */
    static boolean isOperation(ResolvedJavaMethod m) {
        if (m == null) {
            return false;
        }
        try {
            return CLASSES.contains(m.getDeclaringClass().toJavaName()) && OPERATIONS.contains(m.getName() + m.getSignature().toMethodDescriptor());
        } catch (Throwable t) {
            return false;
        }
    }
}
