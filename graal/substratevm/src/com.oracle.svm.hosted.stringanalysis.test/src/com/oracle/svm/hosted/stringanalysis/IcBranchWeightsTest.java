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

import org.junit.Assert;
import org.junit.Test;

import jdk.graal.compiler.nodes.ProfileData.BranchProbabilityData;
import jdk.graal.compiler.nodes.extended.BranchProbabilityNode;

/**
 * The IC chain's rep-arm branch probability: every rep-arm {@code If} is {@code SLOW_PATH_PROFILE} (the else, plain
 * Strings and the non-overriding flat reps, likely).
 */
@AddExports({"jdk.internal.vm.ci/jdk.vm.ci.meta", "jdk.internal.vm.ci/jdk.vm.ci.code",
                "jdk.graal.compiler/jdk.graal.compiler.core.common.type",
                "jdk.graal.compiler/jdk.graal.compiler.debug",
                "jdk.graal.compiler/jdk.graal.compiler.graph",
                "jdk.graal.compiler/jdk.graal.compiler.nodes",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.calc",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.extended",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.graphbuilderconf",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.java",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.spi",
                "jdk.graal.compiler/jdk.graal.compiler.nodes.util",
                "jdk.graal.compiler/jdk.graal.compiler.options"})
public class IcBranchWeightsTest {

    @Test
    public void theDefaultIsTheElseLikely() {
        long before = InlineCacheTrivialMethodNodePlugin.REP_ARM_IFS.get();
        BranchProbabilityData w = InlineCacheTrivialMethodNodePlugin.repArmProfile();
        Assert.assertSame("the emitted rep-arm profile", BranchProbabilityNode.SLOW_PATH_PROFILE, w);
        Assert.assertTrue("the else likely", w.getDesignatedSuccessorProbability() < 0.5);
        Assert.assertEquals(before + 1, InlineCacheTrivialMethodNodePlugin.REP_ARM_IFS.get());
        Assert.assertTrue(InlineCacheTrivialMethodNodePlugin.codegenKnobSummary().startsWith("[string-analysis] codegen-knobs: chain rep-arm ifs="));
    }
}
