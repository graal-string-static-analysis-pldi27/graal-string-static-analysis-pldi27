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

import com.oracle.svm.hosted.stringanalysis.ThreadLocalModel.TlOp;
import org.junit.Assert;
import org.junit.Test;

import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaType;

/**
 * Pins for the thread-local model: the translated
 * operations are recognised by method identity (declaring class + name + descriptor) — the per-thread map
 * primitives of {@code java.lang.ThreadLocal}, never the public API — and every other method of the abstract
 * map internals is a BYPASS (a named refusal when a tracked value enters it).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.hotspot", "jdk.internal.vm.ci/jdk.vm.ci.runtime", "jdk.internal.vm.ci/jdk.vm.ci.meta",
                "jdk.internal.vm.ci/jdk.vm.ci.code"})
public class ThreadLocalModelTest {

    private final MetaAccessProvider metaAccess = HotSpotJVMCIRuntime.runtime().getHostJVMCIBackend().getMetaAccess();

    private ResolvedJavaMethod method(String className, String name, String descriptor) throws ClassNotFoundException {
        ResolvedJavaType t = metaAccess.lookupJavaType(Class.forName(className, false, Object.class.getClassLoader()));
        for (ResolvedJavaMethod m : t.getDeclaredMethods(false)) {
            if (m.getName().equals(name) && m.getSignature().toMethodDescriptor().equals(descriptor)) {
                return m;
            }
        }
        for (ResolvedJavaMethod m : t.getDeclaredConstructors(false)) {
            if (name.equals("<init>") && m.getSignature().toMethodDescriptor().equals(descriptor)) {
                return m;
            }
        }
        throw new AssertionError("no method " + className + "." + name + descriptor);
    }

    @Test
    public void primitivesAreTranslated() throws ClassNotFoundException {
        Assert.assertEquals(TlOp.READ, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal", "get", "(Ljava/lang/Thread;)Ljava/lang/Object;")));
        Assert.assertEquals(TlOp.WRITE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap", "set", "(Ljava/lang/ThreadLocal;Ljava/lang/Object;)V")));
        Assert.assertEquals(TlOp.WRITE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap", "<init>", "(Ljava/lang/ThreadLocal;Ljava/lang/Object;)V")));
        Assert.assertEquals(TlOp.KILL, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap", "remove", "(Ljava/lang/ThreadLocal;)V")));
        Assert.assertEquals(TlOp.INHERIT, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap", "<init>", "(Ljava/lang/ThreadLocal$ThreadLocalMap;)V")));
    }

    @Test
    public void publicApiAndCallersAreOrdinaryCode() throws ClassNotFoundException {
        // the public API and the JDK code around the primitives stay analysed code (they lead to the primitives)
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal", "get", "()Ljava/lang/Object;")));
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal", "set", "(Ljava/lang/Object;)V")));
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal", "setInitialValue", "(Ljava/lang/Thread;)Ljava/lang/Object;")));
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal", "initialValue", "()Ljava/lang/Object;")));
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.InheritableThreadLocal", "childValue", "(Ljava/lang/Object;)Ljava/lang/Object;")));
    }

    @Test
    public void mapInternalsAreBypass() throws ClassNotFoundException {
        Assert.assertEquals(TlOp.BYPASS, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap", "getEntry",
                        "(Ljava/lang/ThreadLocal;)Ljava/lang/ThreadLocal$ThreadLocalMap$Entry;")));
        Assert.assertEquals(TlOp.BYPASS, ThreadLocalModel.classifyTlOp(method("java.lang.ThreadLocal$ThreadLocalMap$Entry", "<init>", "(Ljava/lang/ThreadLocal;Ljava/lang/Object;)V")));
    }

    @Test
    public void currentThreadAccessors() throws ClassNotFoundException {
        Assert.assertEquals(TlOp.CURRENT_THREAD, ThreadLocalModel.classifyTlOp(method("java.lang.Thread", "currentThread", "()Ljava/lang/Thread;")));
        Assert.assertEquals(TlOp.CURRENT_THREAD, ThreadLocalModel.classifyTlOp(method("java.lang.Thread", "currentCarrierThread", "()Ljava/lang/Thread;")));
        Assert.assertEquals(TlOp.NONE, ThreadLocalModel.classifyTlOp(method("java.lang.Thread", "getName", "()Ljava/lang/String;")));
    }

    @Test
    public void currentThreadVariableMatchedByIdentityNotName() {
        // an object that merely prints as the current-thread variable is not that variable
        Assert.assertFalse(ThreadLocalModel.isCurrentThreadVmtl(new Object() {
            @Override
            public String toString() {
                return "FastThreadLocal:PlatformThreads.currentThread";
            }
        }));
        Assert.assertFalse(ThreadLocalModel.isCurrentThreadVmtl(null));
    }

    // --- the override-drop proof of fwd.overridefilterfix (exact dispatch) ---

    private ResolvedJavaType type(Class<?> c) {
        return metaAccess.lookupJavaType(c);
    }

    @Test
    public void overrideDropKeepsOnTopBlock() throws ClassNotFoundException {
        ResolvedJavaMethod objToString = method("java.lang.Object", "toString", "()Ljava/lang/String;");
        Assert.assertFalse(ForwardFixpoint.overrideDropProven(true, null, objToString));
    }

    @Test
    public void overrideDropDropsObjectToStringForStringBlock() throws ClassNotFoundException {
        ResolvedJavaMethod objToString = method("java.lang.Object", "toString", "()Ljava/lang/String;");
        Assert.assertTrue(ForwardFixpoint.overrideDropProven(true, java.util.List.of(type(String.class)), objToString));
        // a block that may be exactly the declaring class keeps it
        Assert.assertFalse(ForwardFixpoint.overrideDropProven(true, java.util.List.of(type(String.class), type(Object.class)), objToString));
    }

    @Test
    public void overrideDropKeepsAtArgumentPosition() throws ClassNotFoundException {
        ResolvedJavaMethod objToString = method("java.lang.Object", "toString", "()Ljava/lang/String;");
        Assert.assertFalse(ForwardFixpoint.overrideDropProven(false, java.util.List.of(type(String.class)), objToString));
    }

    @Test
    public void overrideDropKeepsThreadLocalSetForThreadLocalBlock() throws ClassNotFoundException {
        // the Step 1 finding: ThreadLocal.set must survive for a receiver that may be exactly a ThreadLocal
        ResolvedJavaMethod set = method("java.lang.ThreadLocal", "set", "(Ljava/lang/Object;)V");
        Assert.assertFalse(ForwardFixpoint.overrideDropProven(true, java.util.List.of(type(ThreadLocal.class)), set));
    }
}
