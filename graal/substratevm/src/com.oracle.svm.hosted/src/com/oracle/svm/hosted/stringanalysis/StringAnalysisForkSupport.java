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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

public final class StringAnalysisForkSupport {

    private static final AtomicReference<Process> childProcess = new AtomicReference<>();
    private static volatile Path profilePath;
    private static volatile boolean forkStarted;

    private StringAnalysisForkSupport() {
    }

    public static void setFork(Process process, Path path) {
        childProcess.set(process);
        profilePath = path;
        forkStarted = true;
    }

    public static Process getChildProcess() {
        return childProcess.get();
    }

    public static Path getProfilePath() {
        return profilePath;
    }

    public static boolean forkStarted() {
        return forkStarted;
    }

    // ------------------------------------------------------------------
    // The guard-trip rerun at objret=0. A child that ran with the object-return rule active (objret!=0, premise PASS,
    // >= 1 usable named query) and tripped EVALUATION_GUARD writes no profile but a marker; the driver then reruns the
    // child once with -Dsvm.stringanalysis.fwd.rtrack.objret=0 (after the inherited JVM options: the last -D wins) and
    // uses that run's profile. An inert run or an objret=0 run never reruns.
    // ------------------------------------------------------------------
    private static volatile List<String> childCommand;
    private static volatile Path childLog;
    private static volatile boolean objretRerunRequested;
    private static volatile boolean objretRerunDone;
    static final String OBJRET_ZERO = "-Dsvm.stringanalysis.fwd.rtrack.objret=0";
    /** The rerun is a plain objret=0 child (an inherited census=1 would start named queries there). */
    static final String OBJRET_CENSUS_ZERO = "-Dsvm.stringanalysis.fwd.rtrack.objret.census=0";

    /** Pure (JUnit): rerun iff the object-return rule was active (delivery on, premise PASS, a usable named query) and the guard tripped. */
    public static boolean objretRerunDecision(boolean deliver, boolean premisePass, int usableQueries, boolean guardTripped) {
        return deliver && premisePass && usableQueries > 0 && guardTripped;
    }

    public static void setChildCommand(List<String> command, Path log) {
        childCommand = List.copyOf(command);
        childLog = log;
    }

    /** Child side: the analysis asks for the rerun (read when the profile would be dumped). */
    static void requestObjretRerun() {
        objretRerunRequested = true;
    }

    public static boolean objretRerunRequested() {
        return objretRerunRequested;
    }

    /** The marker the child writes instead of its profile. */
    public static Path rerunMarker(Path profile) {
        return Path.of(profile.toString() + ".objret-rerun");
    }

    /**
     * Pure (JUnit): the rerun command = the child's command with {@link #OBJRET_ZERO} and {@link #OBJRET_CENSUS_ZERO}
     * right after the JVM options (the last -D wins).
     */
    public static List<String> rerunCommand(List<String> command, int jvmOptionsEnd) {
        List<String> out = new ArrayList<>(command);
        out.add(jvmOptionsEnd, OBJRET_CENSUS_ZERO);
        out.add(jvmOptionsEnd, OBJRET_ZERO);
        return out;
    }

    /**
     * Driver side: if the exited child left the rerun marker (and no rerun ran yet), delete it, start the child again at
     * objret=0 (the first run's log is kept as {@code <log>.objret-first.log}) and return the new process; else null.
     */
    public static Process rerunIfRequested() throws IOException {
        Path profile = profilePath;
        List<String> cmd = childCommand;
        if (profile == null || cmd == null || objretRerunDone || !Files.exists(rerunMarker(profile))) {
            return null;
        }
        Files.deleteIfExists(rerunMarker(profile));
        objretRerunDone = true;
        int jvmEnd = cmd.indexOf("--module");
        List<String> rc = rerunCommand(cmd, jvmEnd < 0 ? 1 : jvmEnd);
        System.out.println("[objret-rerun] reason=EVALUATION_GUARD: the child ran with rule U active and tripped the evaluation guard; rerunning it with " + OBJRET_ZERO + " " + OBJRET_CENSUS_ZERO);
        ProcessBuilder pb = new ProcessBuilder(rc);
        if (childLog != null) {
            // the discarded run's log is kept beside it; the child log is the rerun's alone (it is the result)
            Path first = Path.of(childLog.toString() + ".objret-first.log");
            Files.copy(childLog, first, java.nio.file.StandardCopyOption.REPLACE_EXISTING);
            System.out.println("[objret-rerun] the discarded objret=1 run's child log: " + first);
            pb.redirectOutput(childLog.toFile());
        }
        pb.redirectErrorStream(true);
        Process p = pb.start();
        childProcess.set(p);
        Runtime.getRuntime().addShutdownHook(new Thread(p::destroyForcibly));
        return p;
    }
}