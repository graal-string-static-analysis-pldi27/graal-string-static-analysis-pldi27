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

public final class SugEdge {

    public enum FlowRole {
        RECEIVER,
        ARG,
        NONE
    }

    private final SugVertex from;
    private final SugVertex to;
    private final SugEdgeType edgeType;
    private final int paramIndex;
    private final FlowRole flowRole;

    SugEdge(SugVertex from, SugVertex to, SugEdgeType edgeType, int paramIndex, FlowRole flowRole) {
        this.from = from;
        this.to = to;
        this.edgeType = edgeType;
        this.paramIndex = paramIndex;
        this.flowRole = flowRole;
    }

    public SugVertex getFrom() {
        return from;
    }

    public SugVertex getTo() {
        return to;
    }

    public SugEdgeType getEdgeType() {
        return edgeType;
    }

    public int getParamIndex() {
        return paramIndex;
    }

    public FlowRole getFlowRole() {
        return flowRole;
    }

    @Override
    public String toString() {
        String extra = edgeType == SugEdgeType.PARAMETER ? "[" + paramIndex + "]" : "";
        return "V" + from.getId() + " --" + edgeType + extra + "[" + flowRole + "]-> V" + to.getId();
    }
}
