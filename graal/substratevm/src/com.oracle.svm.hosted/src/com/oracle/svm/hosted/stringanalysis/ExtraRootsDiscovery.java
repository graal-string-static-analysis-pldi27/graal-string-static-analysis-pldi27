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

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.graalvm.collections.EconomicMap;
import org.graalvm.nativeimage.hosted.Feature.BeforeAnalysisAccess;

import com.oracle.svm.configure.ConfigurationFile;
import com.oracle.svm.configure.ConfigurationParser;
import com.oracle.svm.core.SubstrateOptions;
import com.oracle.svm.core.configure.ConfigurationFiles;
import com.oracle.svm.hosted.FeatureImpl;
import com.oracle.svm.hosted.ImageClassLoader;

import jdk.graal.compiler.util.json.JsonParser;

/**
 * Discovery and registration of user-class extra roots for the string analysis fork: reads
 * {@code predefined-classes-config.json} plus the reflection section of {@code reachability-metadata.json} (filtered
 * by a prefix deny-list); the manual {@code StringAnalysisExtraRoots} flag remains as an override. Invoked from
 * {@link StringAnalysisFeature}'s {@code beforeAnalysis}.
 */
final class ExtraRootsDiscovery {

    /**
     * The extra-root registration reason of a reflection-config member (the reflection extra-root rule). The values are
     * load-bearing: {@link ReflectionBridge#childReflectionExtraRoot} matches them by {@code startsWith}/{@code endsWith}
     * against {@link #REFLECTION_REASON_PREFIX}/{@link #REFLECTION_REASON_SUFFIX} (pinned by {@code SinkAndExceptionFlowRulesTest}).
     */
    public static final String REFLECTION_METHOD_REASON = "string-analysis extra root (reflection)";
    /** The constructor twin of {@link #REFLECTION_METHOD_REASON}. */
    public static final String REFLECTION_CONSTRUCTOR_REASON = "string-analysis extra root constructor (reflection)";
    /** The reflective-reason match prefix (the non-reflective extra-root reasons below share it but lack the suffix). */
    public static final String REFLECTION_REASON_PREFIX = "string-analysis extra root";
    /** The reflective-reason match suffix (only the two reflective reasons end with it). */
    public static final String REFLECTION_REASON_SUFFIX = "(reflection)";

    static void registerExtraRoots(BeforeAnalysisAccess access) {
        if (!SubstrateOptions.StringAnalysisFork.getValue()) {
            return;
        }
        registerRedirectTargetRoots(access);
        String extraRoots = SubstrateOptions.StringAnalysisExtraRoots.getValue();
        Map<String, List<MethodSpec>> rootClasses;
        if (extraRoots != null && !extraRoots.isEmpty()) {
            rootClasses = new LinkedHashMap<>();
            for (String n : extraRoots.split(",")) {
                String trimmed = n.trim();
                if (!trimmed.isEmpty()) {
                    rootClasses.put(trimmed, null);
                }
            }
        } else {
            rootClasses = discoverAutoRoots();
        }
        if (rootClasses.isEmpty()) {
            return;
        }
        FeatureImpl.BeforeAnalysisAccessImpl impl = (FeatureImpl.BeforeAnalysisAccessImpl) access;
        com.oracle.graal.pointsto.BigBang bb = impl.getBigBang();
        com.oracle.graal.pointsto.meta.AnalysisMetaAccess metaAccess = impl.getMetaAccess();
        ImageClassLoader loader = impl.getImageClassLoader();
        for (Map.Entry<String, List<MethodSpec>> entry : rootClasses.entrySet()) {
            registerClassAsRoot(loader, bb, metaAccess, entry.getKey(), entry.getValue());
        }
    }

    /** The reason of a {@link #registerRedirectTargetRoots} root. */
    static final String REDIRECT_TARGET_REASON = "string-analysis REDIRECT target root";

    /**
     * The bodies the parent's REDIRECT lowering calls ({@link EqualsMatrixNodePlugin#redirectTargets}) are roots of the
     * child, so their body sites get profile (IC) entries. No Java code calls them and the REDIRECT rewrite is
     * parent-only, so the child would not reach them otherwise.
     */
    static void registerRedirectTargetRoots(BeforeAnalysisAccess access) {
        FeatureImpl.BeforeAnalysisAccessImpl impl = (FeatureImpl.BeforeAnalysisAccessImpl) access;
        for (java.lang.reflect.Method m : EqualsMatrixNodePlugin.redirectTargets()) {
            impl.getBigBang().addRootMethod(m, true, REDIRECT_TARGET_REASON);
        }
    }

    private record MethodSpec(String name, List<String> paramTypes) {
    }

    private static boolean registerClassAsRoot(ImageClassLoader loader, com.oracle.graal.pointsto.BigBang bb,
                    com.oracle.graal.pointsto.meta.AnalysisMetaAccess metaAccess, String className, List<MethodSpec> methodSpecs) {
        try {
            Class<?> rootClass = loader.findClass(className).get();
            int modifiers = rootClass.getModifiers();
            boolean instantiable = !java.lang.reflect.Modifier.isAbstract(modifiers) && !java.lang.reflect.Modifier.isInterface(modifiers) && !rootClass.isPrimitive() && !rootClass.isArray();
            if (instantiable) {
                metaAccess.lookupJavaType(rootClass).registerAsInstantiated("string-analysis extra root class");
            }
            int registered = 0;
            int ctorsRegistered = 0;
            if (methodSpecs == null) {
                for (java.lang.reflect.Method m : rootClass.getDeclaredMethods()) {
                    int mod = m.getModifiers();
                    if (java.lang.reflect.Modifier.isNative(mod) || java.lang.reflect.Modifier.isAbstract(mod)) {
                        continue;
                    }
                    bb.addRootMethod(m, true, "string-analysis extra root");
                    registered++;
                }
                if (instantiable) {
                    for (java.lang.reflect.Constructor<?> ctor : rootClass.getDeclaredConstructors()) {
                        if (java.lang.reflect.Modifier.isNative(ctor.getModifiers())) {
                            continue;
                        }
                        try {
                            bb.addRootMethod(ctor, true, "string-analysis extra root constructor");
                            ctorsRegistered++;
                        } catch (Exception e) {
                            System.err.println("[string-analysis-fork] could not register constructor: " + ctor + " : " + e.getMessage());
                        }
                    }
                }
            } else {
                for (MethodSpec spec : methodSpecs) {
                    java.lang.reflect.Executable match = findExecutable(rootClass, spec);
                    if (match == null) {
                        System.err.println("[string-analysis-fork] reflection method not found: " + className + "." + spec.name() + spec.paramTypes());
                        continue;
                    }
                    if (match instanceof java.lang.reflect.Method m) {
                        int mod = m.getModifiers();
                        if (java.lang.reflect.Modifier.isNative(mod) || java.lang.reflect.Modifier.isAbstract(mod)) {
                            continue;
                        }
                        bb.addRootMethod(m, true, REFLECTION_METHOD_REASON);
                        registered++;
                    } else if (match instanceof java.lang.reflect.Constructor<?> ctor) {
                        if (java.lang.reflect.Modifier.isNative(ctor.getModifiers())) {
                            continue;
                        }
                        try {
                            bb.addRootMethod(ctor, true, REFLECTION_CONSTRUCTOR_REASON);
                            ctorsRegistered++;
                        } catch (Exception e) {
                            System.err.println("[string-analysis-fork] could not register constructor: " + ctor + " : " + e.getMessage());
                        }
                    }
                }
            }
            System.out.println("[string-analysis-fork] registered " + registered + " methods + " + ctorsRegistered + " constructors from: " + className + (instantiable ? "" : " (not instantiated)") +
                            (methodSpecs == null ? " (manual/all)" : methodSpecs.isEmpty() ? " (class-only)" : " (reflection-specific)"));
            return true;
        } catch (Exception e) {
            System.out.println("[string-analysis-fork] could not register extra root: " + className + " : " + e.getMessage());
            return false;
        }
    }

    private static java.lang.reflect.Executable findExecutable(Class<?> rootClass, MethodSpec spec) {
        Class<?>[] paramClasses = new Class<?>[spec.paramTypes().size()];
        for (int i = 0; i < spec.paramTypes().size(); i++) {
            paramClasses[i] = resolveParamClass(rootClass, spec.paramTypes().get(i));
            if (paramClasses[i] == null) {
                return null;
            }
        }
        if ("<init>".equals(spec.name())) {
            try {
                return rootClass.getDeclaredConstructor(paramClasses);
            } catch (NoSuchMethodException e) {
                for (java.lang.reflect.Constructor<?> ctor : rootClass.getDeclaredConstructors()) {
                    Class<?>[] mp = ctor.getParameterTypes();
                    if (mp.length != paramClasses.length) {
                        continue;
                    }
                    boolean match = true;
                    for (int i = 0; i < mp.length; i++) {
                        if (!mp[i].equals(paramClasses[i]) && !paramClasses[i].isAssignableFrom(mp[i])) {
                            match = false;
                            break;
                        }
                    }
                    if (match) {
                        return ctor;
                    }
                }
                return null;
            }
        }
        for (java.lang.reflect.Method m : rootClass.getDeclaredMethods()) {
            if (!m.getName().equals(spec.name())) {
                continue;
            }
            Class<?>[] mp = m.getParameterTypes();
            if (mp.length != paramClasses.length) {
                continue;
            }
            boolean match = true;
            for (int i = 0; i < mp.length; i++) {
                if (!mp[i].equals(paramClasses[i]) && !paramClasses[i].isAssignableFrom(mp[i])) {
                    match = false;
                    break;
                }
            }
            if (match) {
                return m;
            }
        }
        return null;
    }

    private static Class<?> resolveParamClass(Class<?> declaringClass, String typeName) {
        Class<?> prim = resolvePrimitive(typeName);
        if (prim != null) {
            return prim;
        }
        if (typeName.endsWith("[]")) {
            Class<?> comp = resolveParamClass(declaringClass, typeName.substring(0, typeName.length() - 2));
            if (comp == null) {
                return null;
            }
            return java.lang.reflect.Array.newInstance(comp, 0).getClass();
        }
        try {
            return Class.forName(typeName, false, declaringClass.getClassLoader());
        } catch (ClassNotFoundException e) {
            try {
                return Class.forName(typeName, false, Thread.currentThread().getContextClassLoader());
            } catch (ClassNotFoundException e2) {
                return null;
            }
        }
    }

    private static Class<?> resolvePrimitive(String typeName) {
        return switch (typeName) {
            case "boolean" -> boolean.class;
            case "byte" -> byte.class;
            case "char" -> char.class;
            case "short" -> short.class;
            case "int" -> int.class;
            case "long" -> long.class;
            case "float" -> float.class;
            case "double" -> double.class;
            case "void" -> void.class;
            default -> null;
        };
    }

    private static final String[] AUTO_ROOT_DENY_PREFIXES = {
                    "java.", "javax.", "jdk.", "sun.", "com.sun.", "org.graalvm.",
                    "com.oracle.", "org.apache.logging.log4j.", "org.apache.logging.slf4j.",
                    "com.fasterxml.jackson.", "org.slf4j.", "org.dacapo."
    };

    private static boolean isUserClass(String className) {
        for (String prefix : AUTO_ROOT_DENY_PREFIXES) {
            if (className.startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    private static Map<String, List<MethodSpec>> discoverAutoRoots() {
        Set<String> fromPredefined = new LinkedHashSet<>();
        Map<String, List<MethodSpec>> fromReflection = new LinkedHashMap<>();
        try {
            for (Path path : ConfigurationFiles.findConfigurationFiles(ConfigurationFile.PREDEFINED_CLASSES_NAME.getFileName())) {
                try (java.io.Reader reader = Files.newBufferedReader(path)) {
                    Object json = new JsonParser(reader).parse();
                    for (Object originObj : ConfigurationParser.asList(json, "predefined-classes config must be an array")) {
                        EconomicMap<String, Object> origin = ConfigurationParser.asMap(originObj, "predefined class origin must be an object");
                        Object classesObj = origin.get("classes");
                        if (classesObj == null) {
                            continue;
                        }
                        for (Object clazzObj : ConfigurationParser.asList(classesObj, "'classes' must be an array")) {
                            EconomicMap<String, Object> clazz = ConfigurationParser.asMap(clazzObj, "class descriptor must be an object");
                            Object nameInfo = clazz.get("nameInfo");
                            if (nameInfo instanceof String name) {
                                fromPredefined.add(name.replace('/', '.'));
                            }
                        }
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("[string-analysis-fork] could not read predefined-classes config: " + e.getMessage());
        }
        try {
            for (Path path : ConfigurationFiles.findConfigurationFiles(ConfigurationFile.REACHABILITY_METADATA.getFileName())) {
                try (java.io.Reader reader = Files.newBufferedReader(path)) {
                    Object json = new JsonParser(reader).parse();
                    EconomicMap<String, Object> root = ConfigurationParser.asMap(json, "reachability metadata must be an object");
                    Object reflectionObj = root.get("reflection");
                    if (reflectionObj == null) {
                        continue;
                    }
                    for (Object entryObj : ConfigurationParser.asList(reflectionObj, "'reflection' must be an array")) {
                        EconomicMap<String, Object> entry = ConfigurationParser.asMap(entryObj, "reflection entry must be an object");
                        Object typeObj = entry.get("type");
                        if (!(typeObj instanceof String type)) {
                            continue;
                        }
                        Object methodsObj = entry.get("methods");
                        if (methodsObj == null) {
                            continue;
                        }
                        List<MethodSpec> specs = new ArrayList<>();
                        for (Object methodObj : ConfigurationParser.asList(methodsObj, "'methods' must be an array")) {
                            EconomicMap<String, Object> method = ConfigurationParser.asMap(methodObj, "method descriptor must be an object");
                            Object nameObj = method.get("name");
                            if (!(nameObj instanceof String methodName)) {
                                continue;
                            }
                            List<String> paramTypes = new ArrayList<>();
                            Object paramsObj = method.get("parameterTypes");
                            if (paramsObj instanceof List<?> params) {
                                for (Object p : params) {
                                    if (p instanceof String pt) {
                                        paramTypes.add(pt);
                                    }
                                }
                            }
                            specs.add(new MethodSpec(methodName, paramTypes));
                        }
                        fromReflection.put(type, specs);
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("[string-analysis-fork] could not read reachability metadata: " + e.getMessage());
        }
        Map<String, List<MethodSpec>> result = new LinkedHashMap<>();
        for (String name : fromPredefined) {
            if (isUserClass(name)) {
                result.put(name, Collections.emptyList());
            }
        }
        for (Map.Entry<String, List<MethodSpec>> e : fromReflection.entrySet()) {
            if (isUserClass(e.getKey())) {
                result.put(e.getKey(), e.getValue());
            }
        }
        System.out.println("[string-analysis-fork] Auto-discovered " + result.size() +
                        " user classes from config metadata (predefined=" + fromPredefined.size() +
                        ", reflection=" + fromReflection.size() + ")");
        return result;
    }
}