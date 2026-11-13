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

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * The JDK models as data. A family is a table mapping a resolved JDK method (declaring class, name, descriptor) to an
 * {@link Op}, a list of {@link Effect}s from a small closed set of kinds. The engine ({@link JdkModelEngine}, called from
 * the {@code RecursiveTracking} crossings: forward {@code invokeUsage}, backward {@code resultOfTarget}) desugars them
 * into its existing events (a synthetic-member store, load, escape; a continuation at the call's result; a desugared
 * call). No per-API code: a new family is a new table.
 * <p>
 * A family names the JDK fields its slots abstract ({@link Family#abstracted}, e.g. {@code ArrayList.elementData}). Any
 * IR access to an abstracted field, in either direction, refuses by name ({@code JDK_MODEL_UNMODELLED}), so an IR walk
 * that meets the representation (a callback's return into JDK code, a backward caller fan into it, an image-heap
 * container) is never silently incomplete. A method of a {@link Family#closed} class that the table does not list
 * refuses by name too (no IR fallback); other methods (templates inherited from {@code AbstractList}, ...) are walked as
 * IR, and their calls on {@code this} dispatch back into the model. A family is off for the image when one of its
 * abstracted fields is Unsafe-, reflection- or JNI-accessed (census {@code off=}).
 */
final class JdkModels {

    private JdkModels() {
    }

    /** A synthetic member (a model slot) of a real atom's table; never equal to a real field. */
    static final class Slot {
        final String name;

        private Slot(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return "<" + name + ">";
        }
    }

    /** The slots (the model vocabulary). */
    static final Slot ELEM = new Slot("elem");
    static final Slot KEYS = new Slot("keys");
    static final Slot VALS = new Slot("vals");
    /**
     * F2: the map a fresh {@code Map.Entry} view belongs to ({@code getKey()} = {@code load 0 <map> <keys>},
     * {@code setValue(v)} writes through {@code 0.<map>}).
     */
    static final Slot MAP = new Slot("map");
    /**
     * F6: the five components of a {@code Collectors$CollectorImpl} record. The record's real fields are registered for
     * reflection (its {@code ObjectMethods} read them), so every IR access to them refuses; the modelled constructors
     * store these slots and the modelled accessors load them instead.
     */
    static final Slot SUPPLIER = new Slot("supplier");
    static final Slot ACCUMULATOR = new Slot("accumulator");
    static final Slot COMBINER = new Slot("combiner");
    static final Slot FINISHER = new Slot("finisher");
    static final Slot CHARACTERISTICS = new Slot("characteristics");

    static Slot slot(String name) {
        return switch (name) {
            case "<elem>" -> ELEM;
            case "<keys>" -> KEYS;
            case "<vals>" -> VALS;
            case "<map>" -> MAP;
            case "<supplier>" -> SUPPLIER;
            case "<accumulator>" -> ACCUMULATOR;
            case "<combiner>" -> COMBINER;
            case "<finisher>" -> FINISHER;
            case "<characteristics>" -> CHARACTERISTICS;
            default -> null;
        };
    }

    /**
     * The abstraction map's values: {@code "<elem>[]"} = the field holds an array whose elements are the slot's values
     * (ArrayList.elementData: its initial store is translated, its heap snapshot fills the slot); {@code "<elem>"} = a
     * field of a representation node holding a slot value (LinkedList$Node.item); {@code "-"} = a representation-internal
     * link (LinkedList.first, Node.next). Every IR access to any of them refuses.
     */
    static Slot arrayRepSlot(String rep) {
        return rep != null && rep.endsWith("[]") ? slot(rep.substring(0, rep.length() - 2)) : null;
    }

    /**
     * An operand of an effect: argument {@code slot} (0 = the receiver), {@link #RESULT} (the op's fresh result
     * {@code R}) or a temp ({@code $k}: a callback result bound by {@code -> $k}; {@code $} = {@code $1}; slot
     * {@code TEMP - (k - 1)}), followed by a member chain (a slot name, a real field "Class.field" or {@code []}), e.g.
     * {@code 0.<elem>} (each stored element), {@code 0.java.util.ArrayList$SubList.root} (a real field's value).
     */
    record Ref(int slot, List<String> members) {
        static final int RESULT = -1;
        /** The slot of temp {@code $1}; temp {@code $k} is {@code TEMP - (k - 1)}. */
        static final int TEMP = -11;
        /** {@code _}: a callback argument that is no tracked value (a primitive, a constant, a fresh untracked object). */
        static final int NONE = -3;
        /**
         * {@code S}: the op's sink, a callback argument (a consumer the JDK code hands to the callback) whose
         * {@code accept(x)} is the op's one store {@code store o m S}; an engine operand, never an atom.
         */
        static final int SINK = -4;

        /** {@code k}, {@code R}, {@code $} or {@code _}, optionally followed by members: {@code .m1/m2/...} (a field name has dots). */
        static Ref parse(String w) {
            if (w.equals("_")) {
                return new Ref(NONE, List.of());
            }
            if (w.equals("S")) {
                return new Ref(SINK, List.of());
            }
            int dot = w.indexOf('.');
            String head = dot < 0 ? w : w.substring(0, dot);
            int s = head.equals("R") ? RESULT : head.startsWith("$") ? TEMP - (head.length() == 1 ? 0 : Integer.parseInt(head.substring(1)) - 1) : Integer.parseInt(head);
            return new Ref(s, dot < 0 ? List.of() : List.of(w.substring(dot + 1).split("/")));
        }

        static boolean isTemp(int slot) {
            return slot <= TEMP;
        }

        /** The index k of temp {@code $k}. */
        static int tempIndex(int slot) {
            return TEMP - slot + 1;
        }

        static Ref of(int slot) {
            return new Ref(slot, List.of());
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder(slot == RESULT ? "R" : isTemp(slot) ? "$" + tempIndex(slot) : slot == NONE ? "_" : slot == SINK ? "S" : String.valueOf(slot));
            for (int i = 0; i < members.size(); i++) {
                sb.append(i == 0 ? '.' : '/').append(members.get(i));
            }
            return sb.toString();
        }
    }

    /**
     * A callback's result (and a fresh object's binding): unused ({@code BIND_NONE}), the call's result ({@code -> result};
     * for fresh: the op's result {@code R}) or the temp {@code $k} ({@code BIND_TEMP + k - 1}).
     */
    static final int BIND_NONE = 0;
    static final int BIND_RESULT = 1;
    static final int BIND_TEMP = 2;

    /**
     * One effect of an op, one record per kind. Sealed, so every switch over effects (the engine's forward, backward and
     * birth code, the premise checker) is exhaustive and a new kind cannot be forgotten in one of them.
     */
    sealed interface Effect permits Alias, Store, Callback, Fresh, Observe, Ir, Unmodelled, ClassCheck {
        /** Every operand of the effect (its reads and its writes). */
        List<Ref> operands();

        static String siteMethod(String site) {
            return site.substring(0, site.lastIndexOf('@'));
        }

        static int siteBci(String site) {
            return Integer.parseInt(site.substring(site.lastIndexOf('@') + 1));
        }
    }

    /** The result is the operand {@code a} (an argument, or a member chain of it: the {@code load}). */
    record Alias(Ref a) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a);
        }

        @Override
        public String toString() {
            return "alias " + a;
        }
    }

    /** {@code a.member := v} ({@code a} may be a chain: a write-through view; {@code v} a chain: a bulk copy; {@code S}: a sink's values). */
    record Store(Ref a, String member, Ref v) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a, v);
        }

        @Override
        public String toString() {
            return "store " + a + " " + member + " " + v;
        }
    }

    /**
     * The JDK calls {@code a.cb(cbArgs)} ({@code a} may be an element: targets from the element's type); {@code bind} =
     * its result; {@code sites} = its JDK-internal invokes "holder#name(desc)@bci" (checked by the premise JUnit): a usage
     * the callback produces is recorded there, the sites the parent parses.
     */
    record Callback(Ref a, String cb, List<Ref> cbArgs, int bind, List<String> sites) implements Effect {
        @Override
        public List<Ref> operands() {
            List<Ref> out = new ArrayList<>(1 + cbArgs.size());
            out.add(a);
            out.addAll(cbArgs);
            return out;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder("call ").append(a).append(' ').append(cb);
            for (Ref r : cbArgs) {
                sb.append(' ').append(r);
            }
            sb.append(bind == BIND_RESULT ? " -> result" : bind >= BIND_TEMP ? " -> $" + (bind - BIND_TEMP + 1) : "");
            for (String s : sites) {
                sb.append(" @ ").append(s);
            }
            return sb.toString();
        }
    }

    /**
     * A new object of the JDK class {@code fresh} (a {@code Class.forName} name), born at the call; {@code exact} = its
     * class is exactly that (else a subtype). {@code bind}: {@link #BIND_RESULT} = the op's result {@code R}, or the temp
     * {@code $k} ({@code fresh C -> $k}): an object the JDK code creates and passes on (a callback's argument, a stored
     * value) without returning it. {@code store R ...} / {@code store $k ...} give its initial stores.
     */
    record Fresh(String fresh, boolean exact, int bind) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of();
        }

        @Override
        public String toString() {
            return "fresh " + (exact ? "" : "~") + fresh + (bind >= BIND_TEMP ? " -> $" + (bind - BIND_TEMP + 1) : "");
        }
    }

    /** The argument is only looked at (identity, null check): nothing recorded. */
    record Observe(Ref a) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a);
        }

        @Override
        public String toString() {
            return "observe " + a;
        }
    }

    /**
     * The argument enters the real callee (a slot whose effects the IR states exactly). In a closed class (Vector's
     * AbstractList templates, the deferred spliterators) only with the explicit marker {@code ir-closed}: there every
     * access of the walked IR to a representation field refuses by the field rule, and that rule keeps the walk sound.
     */
    record Ir(Ref a, boolean closed) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a);
        }

        @Override
        public String toString() {
            return (closed ? "ir-closed " : "ir ") + a;
        }
    }

    /**
     * F2: the JDK code takes the class of {@code a} ({@code a.getClass()}, an exact {@code instanceof}) at its internal
     * {@code sites}. A string atom there records the CLASS_CHECK usage at the site (as the IR walk's
     * {@code Object.getClass} usage would; no whitelist admits it); any other atom is only observed. F2's key protocol
     * states it explicitly (a tree bin's {@code comparableClassFor(k)}) since a String key reaches it; the premise checker
     * requires the effect in a family with {@link Family#explicitClassChecks}.
     */
    record ClassCheck(Ref a, List<String> sites) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder("classcheck ").append(a);
            for (String s : sites) {
                sb.append(" @ ").append(s);
            }
            return sb.toString();
        }
    }

    /** A named refusal (the operation is not modelled; never an IR fallback). */
    record Unmodelled(Ref a) implements Effect {
        @Override
        public List<Ref> operands() {
            return List.of(a);
        }

        @Override
        public String toString() {
            return "unmodelled " + a;
        }
    }

    /**
     * A family operation: the effects of one modelled method. {@code resultIr}: the result is the real callee's (walked
     * backward; in a closed class only as {@code result ir-closed}). {@code key}: two resolved targets with equal keys are
     * one model application (the unknown-receiver rule).
     */
    record Op(Family family, String method, List<Effect> effects, boolean resultIr, boolean resultIrClosed, String key) {
        boolean hasResultEffect() {
            if (resultIr) {
                return true;
            }
            for (Effect e : effects) {
                if (e instanceof Alias || e instanceof Fresh f && f.bind() == BIND_RESULT || e instanceof Callback c && c.bind() == BIND_RESULT) {
                    return true;
                }
            }
            return false;
        }

        /** The op's fresh result ({@code R}), or null. */
        Fresh fresh() {
            for (Effect e : effects) {
                if (e instanceof Fresh f && f.bind() == BIND_RESULT) {
                    return f;
                }
            }
            return null;
        }

        /** The effect that binds the temp {@code $k} (a callback's result, or a fresh object), or null. */
        Effect tempBinder(int k) {
            for (Effect e : effects) {
                if (e instanceof Callback c && c.bind() == BIND_TEMP + k - 1 || e instanceof Fresh f && f.bind() == BIND_TEMP + k - 1) {
                    return e;
                }
            }
            return null;
        }

        /** The store whose value is the op's sink {@code S} (its target: the owner and member the sink's values go to), or null. */
        Store sinkStore() {
            for (Effect e : effects) {
                if (e instanceof Store s && s.v().slot() == Ref.SINK) {
                    return s;
                }
            }
            return null;
        }
    }

    /**
     * A family: its knob, table, closed classes, abstracted fields, and the unknown-receiver rule's data: its interfaces
     * (a {@code java.*} method implementing one of their methods is the family's to list) and its templates (open
     * {@code java.*} classes whose unlisted methods are walked as IR, their calls on {@code this} dispatching back into
     * the models or a user override). {@code requires} = the families whose slots its entries read (F4 on F1 and F3); the
     * family is off when one of them is disabled or off (census {@code off={<id>=requires:<id>}}), so it never reads empty
     * slots.
    
     */
    static final class Family {
        final String id;
        final boolean enabled;
        final Map<String, Op> table = new LinkedHashMap<>();
        final Set<String> closed;
        /**
         * The abstraction map: representation field ("Class.field") -> kind ({@link #arrayRepSlot}). The field is never a
         * table member: an IR access to it refuses; an allocation's initial store of an array representation becomes a
         * store of the slot.
         */
        final Map<String, String> abstracted;
        final Set<String> interfaces;
        final Set<String> templates;
        final Set<String> requires;
        /** F4: class-name prefixes the family closes as a whole, except names starting with an {@link #openPrefixes} entry. */
        Set<String> closedPrefixes = Set.of();
        Set<String> openPrefixes = Set.of();
        /**
         * F4: a lazy family: its entries model operations whose JDK code runs later (a stream stage's callbacks run at
         * the terminal operation), so the eager premise checker does not apply, and an op whose callback sites do not
         * resolve is refused by name instead of walked as IR (an IR fallback would re-mint the internal stage objects).
         */
        boolean lazy;
        /**
         * F2 premise data: {@code entryClasses} maps a node representation's owner class to the fresh entry class (a node
         * leaving the representation is a fresh entry whose {@code <map>} is the owner); {@code viewCaches} are real
         * fields holding a fresh view made by an earlier call ({@code AbstractMap.keySet}); {@code explicitClassChecks}:
         * every class check must be an explicit {@code classcheck} effect (a callback on a String key does not cover it).
         */
        Map<String, String> entryClasses = Map.of();
        Set<String> viewCaches = Set.of();
        boolean explicitClassChecks;
        /**
         * The family's representation-insensitive class-check sites: the JDK takes a key's class there only to order a
         * structure whose results do not depend on that order (a tree bin's {@code comparableClassFor},
         * {@code compareComparables}, {@code tieBreakOrder}: a non-String key is ordered by class name and identity hash,
         * and lookups search both sides when a comparison is inconclusive). The model guarantees result correctness only;
         * bin-internal ordering and the worst case may differ (how the runtime {@code comparableClassFor} treats a rep is a
         * separate runtime concern). So a {@code classcheck} effect at such a site records no usage of a string atom
         * (census {@code <family>.classcheck-repinsensitive}). Only a declared model effect qualifies: a {@code getClass()} in user code or in
         * IR-walked JDK code stays a CLASS_CHECK usage.
         */
        Set<String> repInsensitiveClassChecks = Set.of();
        /**
         * The family's same-class callback sites: the JDK calls back there only when the receiver's class is the
         * argument's class (a tree bin's {@code compareComparables(kc, k, x)} calls {@code k.compareTo(x)} only if
         * {@code x.getClass() == kc}, {@code kc} being {@code k}'s class). A string atom as the argument there meets only a
         * String-cone receiver, so the targets are the callback's resolution over {@code java.lang.String} (no resolution
         * of the stored keys, whose backward walk reaches {@code String.substring}'s JDK allocations and refuses).
         */
        Set<String> sameClassCallbacks = Set.of();
        /**
         * F6 premise data. {@code stringSinks}: the family models the string argument of a sink ({@code println(s)}): a
         * call into {@code java.lang.String} is the walk's terminal / Phase-A business (observed, never walked), a call on
         * an {@code ir} receiver that passes a tracked value is a callback on it. {@code exactFields}: JDK-internal fields
         * always holding an object of one exact class (a {@code PrintStream}'s {@code textOut} is the
         * {@code BufferedWriter} its constructor makes), so a call on it is that class's code (walked). {@code recordSlots}:
         * real record fields modelled over slots; the engine translates an inlined record constructor's commit into slot
         * stores ({@code JdkModelEngine.recordSlot}), so the reflection-registered field is never a table member.
         */
        boolean stringSinks;
        Map<String, String> exactFields = Map.of();
        Map<String, String> recordSlots = Map.of();

        Family(String id, boolean defaultOn, Set<String> closed, Map<String, String> abstracted, String... lines) {
            this(id, defaultOn, closed, abstracted, Set.of(), Set.of(), Set.of(), lines);
        }

        Family(String id, boolean defaultOn, Set<String> closed, Map<String, String> abstracted, Set<String> interfaces, Set<String> templates, String... lines) {
            this(id, defaultOn, closed, abstracted, interfaces, templates, Set.of(), lines);
        }

        Family(String id, boolean defaultOn, Set<String> closed, Map<String, String> abstracted, Set<String> interfaces, Set<String> templates, Set<String> requires, String... lines) {
            this.id = id;
            this.enabled = defaultOn;

            this.closed = closed;
            this.abstracted = abstracted;
            this.interfaces = interfaces;
            this.templates = templates;
            this.requires = requires;
            for (String l : lines) {
                Op op = parse(this, l);
                if (table.put(op.method, op) != null) {
                    throw new IllegalStateException("duplicate model entry " + op.method);
                }
            }
        }
    }

    /**
     * The entry syntax: {@code holder#name(desc) : effect ; effect ...}, where an effect is {@code alias <ref>},
     * {@code load o m1 [m2 ...]} (= {@code alias} of the chain), {@code store o [m1 ...] m <ref>} ({@code o} a slot,
     * {@code R} or a temp; {@code o.m1...} the owner, {@code m} the stored member), {@code fresh [~]<class> [-> $k]},
     * {@code call <ref> holder#name(desc) [<ref> ...] [-> result | -> $k] @ site [@ site ...]} (at least one site
     * {@code holder#name(desc)@bci}), {@code observe a}, {@code ir a} / {@code ir-closed a}, {@code unmodelled a},
     * {@code result ir} / {@code result ir-closed}, or {@code key <k>} (the collapse key, default the method itself). A
     * {@code <ref>} is {@code k}, {@code R}, {@code $k}, {@code S} (the op's sink) or {@code _}, with an optional
     * {@code .member} chain.
     */
    static Op parse(Family f, String line) {
        int c = line.indexOf(" : ");
        String method = line.substring(0, c).trim();
        List<Effect> effects = new ArrayList<>();
        boolean resultIr = false;
        boolean resultIrClosed = false;
        String key = method;
        for (String part : line.substring(c + 3).split(" ; ")) {
            String[] w = part.trim().split("\\s+");
            switch (w[0]) {
                case "alias" -> effects.add(new Alias(Ref.parse(w[1])));
                case "load" -> {
                    List<String> p = new ArrayList<>();
                    for (int i = 2; i < w.length; i++) {
                        p.add(w[i]);
                    }
                    effects.add(new Alias(new Ref(Integer.parseInt(w[1]), List.copyOf(p))));
                }
                case "store" -> {
                    Ref owner = Ref.parse(w[1]);
                    List<String> chain = new ArrayList<>(owner.members());
                    for (int i = 2; i < w.length - 2; i++) {
                        chain.add(w[i]);
                    }
                    effects.add(new Store(new Ref(owner.slot(), List.copyOf(chain)), w[w.length - 2], Ref.parse(w[w.length - 1])));
                }
                case "fresh" -> {
                    boolean exact = !w[1].startsWith("~");
                    int bind = BIND_RESULT;
                    if (w.length == 4 && w[2].equals("->") && w[3].matches("\\$[1-9]?")) {
                        bind = BIND_TEMP + (w[3].length() == 1 ? 0 : w[3].charAt(1) - '1');
                    } else if (w.length != 2) {
                        throw new IllegalArgumentException("model entry " + method + ": malformed fresh " + part);
                    }
                    effects.add(new Fresh(exact ? w[1] : w[1].substring(1), exact, bind));
                }
                case "call" -> {
                    List<Ref> args = new ArrayList<>();
                    int bind = BIND_NONE;
                    List<String> sites = new ArrayList<>();
                    for (int i = 3; i < w.length; i++) {
                        if (w[i].equals("->") && i + 1 < w.length && bind == BIND_NONE && sites.isEmpty()) {
                            bind = w[++i].equals("result") ? BIND_RESULT : w[i].matches("\\$[1-9]?") ? BIND_TEMP + (w[i].length() == 1 ? 0 : w[i].charAt(1) - '1') : -1;
                        } else if (w[i].equals("@") && i + 1 < w.length) {
                            sites.add(w[++i]);
                        } else if (bind == BIND_NONE && sites.isEmpty()) {
                            args.add(Ref.parse(w[i]));
                        } else {
                            throw new IllegalArgumentException("model entry " + method + ": malformed callback " + part);
                        }
                    }
                    if (bind < 0 || sites.isEmpty() || sites.stream().anyMatch(s -> s.lastIndexOf('@') <= 0 || !s.substring(s.lastIndexOf('@') + 1).matches("\\d+") || s.indexOf('#') < 0)) {
                        // A callback's usages are recorded at its JDK-internal invokes, so the sites are table data
                        throw new IllegalArgumentException("model entry " + method + ": a callback needs its sites `@ holder#name(desc)@bci`: " + part);
                    }
                    effects.add(new Callback(Ref.parse(w[1]), w[2], List.copyOf(args), bind, List.copyOf(sites)));
                }
                case "classcheck" -> {
                    List<String> sites = new ArrayList<>();
                    for (int i = 2; i + 1 < w.length && w[i].equals("@"); i += 2) {
                        sites.add(w[i + 1]);
                    }
                    if (sites.isEmpty() || w.length != 2 + 2 * sites.size() || sites.stream().anyMatch(x -> x.lastIndexOf('@') <= 0 || !x.substring(x.lastIndexOf('@') + 1).matches("\\d+") || x
                                    .indexOf('#') < 0)) {
                        throw new IllegalArgumentException("model entry " + method + ": a class check needs its sites `@ holder#name(desc)@bci`: " + part);
                    }
                    effects.add(new ClassCheck(Ref.parse(w[1]), List.copyOf(sites)));
                }
                case "observe" -> effects.add(new Observe(Ref.of(Integer.parseInt(w[1]))));
                case "ir" -> effects.add(new Ir(Ref.of(Integer.parseInt(w[1])), false));
                case "ir-closed" -> effects.add(new Ir(Ref.of(Integer.parseInt(w[1])), true));
                case "unmodelled" -> effects.add(new Unmodelled(Ref.of(Integer.parseInt(w[1]))));
                case "result" -> {
                    resultIr = true;
                    resultIrClosed = w.length > 1 && w[1].equals("ir-closed");
                    if (w.length != 2 || !w[1].equals("ir") && !resultIrClosed) {
                        throw new IllegalArgumentException("model entry " + method + ": malformed " + part);
                    }
                }
                case "key" -> key = w[1];
                default -> throw new IllegalArgumentException("model entry " + method + ": unknown effect " + part);
            }
        }
        Op op = new Op(f, method, List.copyOf(effects), resultIr, resultIrClosed, f.id + ":" + key);
        check(op, !key.equals(method));
        return op;
    }

    /** The parser's per-entry rules (the operands' bindings; fresh temps, {@code R} and {@code S} as callback operands). */
    private static void check(Op op, boolean keyed) {
        String method = op.method();
        List<Effect> effects = op.effects();
        boolean fresh = op.fresh() != null;
        int sinkStores = 0;
        boolean sinkPassed = false;
        for (Effect e : effects) {
            List<Ref> ops = e.operands();
            for (int i = 0; i < ops.size(); i++) {
                Ref r = ops.get(i);
                if (r.slot() == Ref.RESULT && !fresh) {
                    throw new IllegalArgumentException("model entry " + method + ": R names the op's FRESH result, which it has none of: " + e);
                }
                if (r.slot() == Ref.RESULT && e instanceof Alias) {
                    throw new IllegalArgumentException("model entry " + method + ": alias R (the FRESH result is the result already): " + e);
                }
                if (Ref.isTemp(r.slot()) && effects.stream().filter(x -> x instanceof Callback cb && cb.bind() == BIND_TEMP + Ref.tempIndex(r.slot()) - 1 ||
                                x instanceof Fresh fr && fr.bind() == BIND_TEMP + Ref.tempIndex(r.slot()) - 1).count() != 1) {
                    throw new IllegalArgumentException("model entry " + method + ": " + r + " needs exactly one binder `-> " + r + "`: " + e);
                }
                if (r.slot() == Ref.SINK) {
                    boolean asArg = e instanceof Callback cb && i > 0 && r.members().isEmpty();
                    boolean asValue = e instanceof Store s && r == s.v() && r.members().isEmpty();
                    if (!asArg && !asValue) {
                        throw new IllegalArgumentException("model entry " + method + ": S (the sink) only as a callback argument or a store's value: " + e);
                    }
                    sinkPassed |= asArg;
                    sinkStores += asValue ? 1 : 0;
                }
            }
            if (e instanceof Store s && s.a().slot() == Ref.SINK) {
                throw new IllegalArgumentException("model entry " + method + ": S cannot own a store: " + e);
            }
        }
        if (sinkStores > 1 || sinkPassed != (sinkStores == 1)) {
            throw new IllegalArgumentException("model entry " + method + ": a sink S is passed to a callback and is the value of exactly one store");
        }
        if (effects.stream().filter(e -> e instanceof Fresh fr && fr.bind() == BIND_RESULT).count() > 1 || fresh && op.resultIr()) {
            throw new IllegalArgumentException("model entry " + method + ": one FRESH result, and no `result ir` beside it");
        }
        if (keyed && (op.resultIr() || effects.stream().anyMatch(e -> e instanceof Ir))) {
            // a collapsed application runs once for several targets: its effects must not depend on the target's IR
            throw new IllegalArgumentException("model entry " + method + ": a collapse key with an IR effect");
        }
    }

    /**
     * The cross-family rules, checked once at class initialisation (a violation fails the first model lookup): (1) no
     * effect names an abstracted field or record component field of any family as a member (a store or load of the
     * representation would bypass the slots; only the engine's commit translation and heap fill may translate it); (2) a
     * closed class's entry walks the IR only with the explicit marker ({@code ir-closed}, {@code result ir-closed}), and an
     * open class's entry never carries it; (3) every {@code requires} names a family.
     */
    static void validate(List<Family> families) {
        Set<String> abstractedFields = new java.util.HashSet<>();
        Set<String> closedClasses = new java.util.HashSet<>();
        Set<String> ids = new java.util.HashSet<>();
        for (Family f : families) {
            abstractedFields.addAll(f.abstracted.keySet());
            abstractedFields.addAll(f.recordSlots.keySet()); // a record component field is a slot's too
            closedClasses.addAll(f.closed);
            ids.add(f.id);
        }
        java.util.function.Predicate<String> closedAnywhere = cls -> closedClasses.contains(cls) || families.stream().anyMatch(f -> closedBy(f, cls));
        for (Family f : families) {
            for (String r : f.requires) {
                if (!ids.contains(r) || r.equals(f.id)) {
                    throw new IllegalStateException("family " + f.id + ": requires an unknown family " + r);
                }
            }
            for (Op op : f.table.values()) {
                String holder = op.method().substring(0, op.method().indexOf('#'));
                boolean closedHolder = closedAnywhere.test(holder);
                for (Effect e : op.effects()) {
                    List<String> members = new ArrayList<>();
                    for (Ref r : e.operands()) {
                        members.addAll(r.members());
                    }
                    if (e instanceof Store s) {
                        members.add(s.member());
                    }
                    for (String m : members) {
                        if (abstractedFields.contains(m)) {
                            throw new IllegalStateException("model entry " + op.method() + ": names the abstracted field " + m + " (only the slots may): " + e);
                        }
                    }
                    if (e instanceof Ir ir && ir.closed() != closedHolder) {
                        throw new IllegalStateException("model entry " + op.method() + ": " + (closedHolder ? "`ir` in a closed class needs `ir-closed`" : "`ir-closed` in an open class") + ": " + e);
                    }
                }
                if (op.resultIr() && op.resultIrClosed() != closedHolder) {
                    throw new IllegalStateException("model entry " + op.method() + ": " + (closedHolder ? "`result ir` in a closed class needs `result ir-closed`"
                                    : "`result ir-closed` in an open class"));
                }
            }
        }
    }
    // ------------------------------------------------------------------
    // The families (tables). Slots are argument indices of the call (0 = the receiver of an instance method).
    // JDK citations: the JDK sources, src/java.base/share/classes/ (jdk:).
    // ------------------------------------------------------------------

    // One table style, the literal descriptors `proposeEntries` writes (no descriptor constants).

    /**
     * F7, identity: static methods of {@code java.util.Objects} (jdk:java/util/Objects.java). No representation, no closed
     * class: an unlisted slot or method is the IR.
     */
    static final Family F7 = new Family("f7", true, Set.of(), Map.of(),
                    // :218-222 `if (obj == null) throw new NullPointerException(); return obj;`
                    "java.util.Objects#requireNonNull(Ljava/lang/Object;)Ljava/lang/Object; : alias 0",
                    // :244-248 the message goes into the NPE (thrown): the IR states it (exception flow)
                    "java.util.Objects#requireNonNull(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object; : alias 0 ; ir 1",
                    // :337-342 the supplier is called for the NPE message only: the IR states it
                    "java.util.Objects#requireNonNull(Ljava/lang/Object;Ljava/util/function/Supplier;)Ljava/lang/Object; : alias 0 ; ir 1",
                    // :294-296 `(obj != null) ? obj : requireNonNull(defaultObj, "defaultObj")`
                    "java.util.Objects#requireNonNullElse(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; : alias 0 ; alias 1",
                    // :61-63 `(a == b) || (a != null && a.equals(b))`
                    "java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z : call 0 java.lang.Object#equals(Ljava/lang/Object;)Z 1 @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11",
                    // :96-98 `o != null ? o.hashCode() : 0`
                    "java.util.Objects#hashCode(Ljava/lang/Object;)I : call 0 java.lang.Object#hashCode()I @ java.util.Objects#hashCode(Ljava/lang/Object;)I@5",
                    // :138-140 `String.valueOf(o)` = `(obj == null) ? "null" : obj.toString()` (jdk:java/lang/String.java valueOf(Object));
                    // the result (the literal "null" too) is the IR's
                    "java.util.Objects#toString(Ljava/lang/Object;)Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; -> result @ java.lang.String#valueOf(Ljava/lang/Object;)Ljava/lang/String;@11 ; result ir",
                    // :152-154 `(o != null) ? o.toString() : nullDefault`
                    "java.util.Objects#toString(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/String; : call 0 java.lang.Object#toString()Ljava/lang/String; -> result @ java.util.Objects#toString(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/String;@5 ; alias 1 ; result ir",
                    // :262-264 / :278-280 `obj == null` / `obj != null`
                    "java.util.Objects#isNull(Ljava/lang/Object;)Z : observe 0",
                    "java.util.Objects#nonNull(Ljava/lang/Object;)Z : observe 0");

    /**
     * F1, sequences: the storage lists. One slot {@code <elem>} (index-insensitive, as arrays are) stands for the
     * representation arrays ({@code elementData} of ArrayList and Vector). Every method of a closed class is listed or
     * refuses by name; every virtual call on {@code this} or on an argument is a callback (re-dispatch: a subclass
     * override answers). JDK citations: jdk:java/util/ArrayList.java, Vector.java, Stack.java; the callback sites are the
     * invokes of the builder JDK's bytecode (the premise JUnit checks every one). Not listed (refuse by name):
     * {@code clone} (a shallow copy of every field of a subclass: a wildcard store), {@code sort} (TimSort: comparator
     * calls at many sites, temporary arrays copy the elements), serialization, the sublists' spliterators (F4).
     */
    static final Family F1 = new Family("f1", true,
                    // closed: the storage classes and their listed views (the deferred views stay open: their IR is walked, and its
                    // accesses to a representation refuse by the field rule)
                    Set.of("java.util.ArrayList", "java.util.ArrayList$Itr", "java.util.ArrayList$ListItr", "java.util.ArrayList$SubList", "java.util.ArrayList$SubList$1",
                                    "java.util.ArrayList$ArrayListSpliterator", "java.util.Vector", "java.util.Vector$Itr", "java.util.Vector$ListItr",
                                    "java.util.Vector$1", "java.util.Vector$VectorSpliterator", "java.util.Stack", "java.util.LinkedList", "java.util.LinkedList$ListItr", "java.util.LinkedList$Node",
                                    "java.util.ArrayDeque", "java.util.ArrayDeque$DeqIterator", "java.util.PriorityQueue"),
                    Map.ofEntries(Map.entry("java.util.ArrayList.elementData", "<elem>[]"), Map.entry("java.util.Vector.elementData", "<elem>[]"),
                                    Map.entry("java.util.Vector$VectorSpliterator.array", "-@java.util.Vector$VectorSpliterator.this$0"),
                                    // LinkedList: a node representation (the element field item; the links first/last/next/prev; the
                                    // list iterator's and the spliterator's links into their list's nodes)
                                    Map.entry("java.util.LinkedList.first", "-"), Map.entry("java.util.LinkedList.last", "-"), Map.entry("java.util.LinkedList$Node.item", "<elem>"), Map.entry(
                                                    "java.util.LinkedList$Node.next", "-"),
                                    Map.entry("java.util.LinkedList$Node.prev", "-"), Map.entry("java.util.LinkedList$ListItr.lastReturned", "-@java.util.LinkedList$ListItr.this$0"),
                                    Map.entry("java.util.LinkedList$ListItr.next", "-@java.util.LinkedList$ListItr.this$0"), Map.entry("java.util.LinkedList$LLSpliterator.current",
                                                    "-@java.util.LinkedList$LLSpliterator.list"),
                                    Map.entry("java.util.ArrayDeque.elements", "<elem>[]"), Map.entry("java.util.PriorityQueue.queue", "<elem>[]")),
                    Set.of("java.util.List", "java.util.ListIterator"),
                    Set.of("java.util.AbstractList", "java.util.AbstractCollection", "java.util.AbstractSequentialList", "java.util.List", "java.util.Collection",
                                    "java.util.SequencedCollection", "java.util.ListIterator", "java.util.Iterator", "java.util.AbstractList$Itr", "java.util.AbstractList$ListItr",
                                    "java.util.AbstractList$SubList", "java.util.AbstractList$RandomAccessSubList", "java.util.AbstractList$SubList$1",
                                    "java.util.concurrent.CopyOnWriteArrayList", "java.util.concurrent.CopyOnWriteArrayList$COWSubList",
                                    "java.util.concurrent.CopyOnWriteArrayList$COWIterator", "java.util.concurrent.CopyOnWriteArrayList$COWSubListIterator",
                                    "java.util.AbstractQueue", "java.util.Queue", "java.util.Deque", "java.util.ImmutableCollections$AbstractImmutableList",
                                    "java.util.ImmutableCollections$AbstractImmutableCollection", "java.util.ImmutableCollections$SubList", "java.util.Collections$EmptyList",
                                    "java.util.Collections$CopiesList", "java.util.Collections$EmptyListIterator", "java.util.Collections$EmptyIterator", "java.util.ReverseOrderListView",
                                    "java.util.ReverseOrderListView$Rand", "java.util.Collections$SingletonList", "java.util.ImmutableCollections$List12", "java.util.ImmutableCollections$ListN",
                                    "java.util.Arrays$ArrayList", "java.util.ImmutableCollections$ListItr", "java.util.ReverseOrderListView$DescendingListIterator",
                                    "java.util.LinkedList$DescendingIterator", "java.util.LinkedList$LLSpliterator", "java.util.LinkedList$ReverseOrderLinkedListView",
                                    "java.util.ArrayDeque$DescendingIterator", "java.util.ArrayDeque$DeqSpliterator",
                                    "java.util.PriorityQueue$Itr", "java.util.PriorityQueue$PriorityQueueSpliterator", "java.util.ArrayList$SubList$2"),
                    // ---- ArrayList :155-193 the constructors (<init>(Collection): `a = c.toArray()`, the representation is a or a copy of it)
                    "java.util.ArrayList#<init>()V : observe 0 ; key seq.new",
                    "java.util.ArrayList#<init>(I)V : observe 0 ; key seq.newCap",
                    "java.util.ArrayList#<init>(Ljava/util/Collection;)V : call 1 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.ArrayList#<init>(Ljava/util/Collection;)V@5 ; store 0 <elem> $.[]",
                    // :200-227 capacity (copies inside the representation), :253-264 size
                    "java.util.ArrayList#trimToSize()V : observe 0 ; key seq.trim",
                    "java.util.ArrayList#ensureCapacity(I)V : observe 0 ; key seq.ensureCapacity",
                    "java.util.ArrayList#size()I : observe 0 ; key seq.size",
                    "java.util.ArrayList#isEmpty()Z : observe 0 ; key seq.isEmpty",
                    // :275-277 `indexOf(o) >= 0` (a virtual call on this); :286-335 `o.equals(es[i])` in indexOfRange / lastIndexOfRange
                    "java.util.ArrayList#contains(Ljava/lang/Object;)Z : call 0 java.util.ArrayList#indexOf(Ljava/lang/Object;)I 1 @ java.util.ArrayList#contains(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayList#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#indexOfRange(Ljava/lang/Object;II)I@54",
                    "java.util.ArrayList#lastIndexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#lastIndexOfRange(Ljava/lang/Object;II)I@58",
                    // :369-409 a copy of the elements; toArray(a) fills a when it is large enough
                    "java.util.ArrayList#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.ArrayList#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : fresh ~[Ljava.lang.Object; ; store R [] 0.<elem> ; store 1 [] 0.<elem> ; alias 1",
                    // :427-475 element access
                    "java.util.ArrayList#get(I)Ljava/lang/Object; : load 0 <elem> ; key seq.get",
                    "java.util.ArrayList#getFirst()Ljava/lang/Object; : load 0 <elem> ; key seq.getFirst",
                    "java.util.ArrayList#getLast()Ljava/lang/Object; : load 0 <elem> ; key seq.getLast",
                    "java.util.ArrayList#set(ILjava/lang/Object;)Ljava/lang/Object; : store 0 <elem> 2 ; load 0 <elem> ; key seq.set",
                    // :482-541 additions (addFirst/addLast re-dispatch to add)
                    "java.util.ArrayList#add(Ljava/lang/Object;)Z : store 0 <elem> 1 ; key seq.add",
                    "java.util.ArrayList#add(ILjava/lang/Object;)V : store 0 <elem> 2 ; key seq.addAt",
                    "java.util.ArrayList#addFirst(Ljava/lang/Object;)V : call 0 java.util.ArrayList#add(ILjava/lang/Object;)V _ 1 @ java.util.ArrayList#addFirst(Ljava/lang/Object;)V@3",
                    "java.util.ArrayList#addLast(Ljava/lang/Object;)V : call 0 java.util.ArrayList#add(Ljava/lang/Object;)Z 1 @ java.util.ArrayList#addLast(Ljava/lang/Object;)V@2",
                    // :551-596 removals by position (the old element is the result; the rest shifts inside the representation)
                    "java.util.ArrayList#remove(I)Ljava/lang/Object; : load 0 <elem> ; key seq.removeAt",
                    "java.util.ArrayList#removeFirst()Ljava/lang/Object; : load 0 <elem> ; key seq.removeFirst",
                    "java.util.ArrayList#removeLast()Ljava/lang/Object; : load 0 <elem> ; key seq.removeLast",
                    // :663-690 `e.hashCode()` on each element; :696-716 `o.equals(es[i])`; :732 clear
                    "java.util.ArrayList#hashCode()I : call 0.<elem> java.lang.Object#hashCode()I @ java.util.ArrayList#hashCodeRange(II)I@53",
                    // :599-652 equals: `Objects.equals(es[i], otherEs[i])` with another ArrayList, else the other list's iterator
                    // (two callback results: the iterator $1 and each of its elements $2)
                    "java.util.ArrayList#equals(Ljava/lang/Object;)Z : classcheck 1 @ java.util.ArrayList#equals(Ljava/lang/Object;)Z@22 ; call 0.<elem> java.lang.Object#equals(Ljava/lang/Object;)Z 1.<elem> @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11 ; call 1 java.util.List#iterator()Ljava/util/Iterator; -> $1 @ java.util.ArrayList" +
                                    "#equalsRange(Ljava/util/List;II)Z@22 ; call $1 java.util.Iterator#hasNext()Z @ java.util.ArrayList#equalsRange(Ljava/util/List;II)Z@36 @ java.util.ArrayList" +
                                    "#equalsRange(Ljava/util/List;II)Z@71 ; call $1 java.util.Iterator#next()Ljava/lang/Object; -> $2 @ java.util.ArrayList#equalsRange(Ljava/util/List;II)Z@50 ; call 0.<elem> java.lang.Object#equals(Ljava/lang/Object;)Z" +
                                    " $2 @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11",
                    "java.util.ArrayList#remove(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#remove(Ljava/lang/Object;)Z@50",
                    "java.util.ArrayList#clear()V : observe 0 ; key seq.clear",
                    // :752-816 `a = c.toArray()` copied into the representation
                    "java.util.ArrayList#addAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.ArrayList#addAll(Ljava/util/Collection;)Z@1 ; store 0 <elem> $.[]",
                    "java.util.ArrayList#addAll(ILjava/util/Collection;)Z : call 2 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.ArrayList#addAll(ILjava/util/Collection;)Z@6 ; store 0 <elem> $.[]",
                    "java.util.ArrayList#removeRange(II)V : observe 0",
                    // :873-958 batchRemove: `c.contains(es[r])` at two sites
                    "java.util.ArrayList#removeAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#contains(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@29 @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@70",
                    "java.util.ArrayList#retainAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#contains(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@29 @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@70",
                    // :1005-1031 the iterators (fresh, their this$0 is the list; ListItr has its own this$0 beside Itr's)
                    "java.util.ArrayList#iterator()Ljava/util/Iterator; : fresh java.util.ArrayList$Itr ; store R java.util.ArrayList$Itr.this$0 0",
                    "java.util.ArrayList#listIterator()Ljava/util/ListIterator; : fresh java.util.ArrayList$ListItr ; store R java.util.ArrayList$ListItr.this$0 0 ; store R java.util.ArrayList$Itr.this$0 0",
                    "java.util.ArrayList#listIterator(I)Ljava/util/ListIterator; : fresh java.util.ArrayList$ListItr ; store R java.util.ArrayList$ListItr.this$0 0 ; store R java.util.ArrayList$Itr.this$0 0",
                    // :1190-1193 a view over this (F3: the write-through SubList)
                    "java.util.ArrayList#subList(II)Ljava/util/List; : fresh java.util.ArrayList$SubList ; store R java.util.ArrayList$SubList.root 0",
                    // :1598-1611 `action.accept(elementAt(es, i))`; :1623 the spliterator (F3); :1750-1807 removeIf / replaceAll
                    "java.util.ArrayList#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.ArrayList#forEach(Ljava/util/function/Consumer;)V@46",
                    "java.util.ArrayList#spliterator()Ljava/util/Spliterator; : fresh java.util.ArrayList$ArrayListSpliterator ; store R java.util.ArrayList$ArrayListSpliterator.this$0 0",
                    "java.util.ArrayList#removeIf(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayList#removeIf(Ljava/util/function/Predicate;II)Z@29 @ java.util.ArrayList" +
                                    "#removeIf(Ljava/util/function/Predicate;II)Z@82",
                    "java.util.ArrayList#replaceAll(Ljava/util/function/UnaryOperator;)V : call 1 java.util.function.UnaryOperator#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.<elem> -> $ @ java.util.ArrayList" +
                                    "#replaceAllRange(Ljava/util/function/UnaryOperator;II)V@41 ; store 0 <elem> $",
                    // ---- ArrayList$Itr :1036-1100 (this$0 = the list): `next` reads the list's representation; `remove` re-dispatches
                    "java.util.ArrayList$Itr#hasNext()Z : observe 0 ; key seq.itrHasNext",
                    "java.util.ArrayList$Itr#next()Ljava/lang/Object; : load 0 java.util.ArrayList$Itr.this$0 <elem> ; key seq.itrNext",
                    "java.util.ArrayList$Itr#remove()V : call 0.java.util.ArrayList$Itr.this$0 java.util.ArrayList#remove(I)Ljava/lang/Object; _ @ java.util.ArrayList$Itr#remove()V@27",
                    "java.util.ArrayList$Itr#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$Itr.this$0/<elem> @ java.util.ArrayList" +
                                    "$Itr#forEachRemaining(Ljava/util/function/Consumer;)V@73",
                    "java.util.ArrayList$Itr#checkForComodification()V : observe 0",
                    // ---- ArrayList$ListItr :1103-1160 (its own this$0)
                    "java.util.ArrayList$ListItr#hasPrevious()Z : observe 0",
                    "java.util.ArrayList$ListItr#nextIndex()I : observe 0",
                    "java.util.ArrayList$ListItr#previousIndex()I : observe 0",
                    "java.util.ArrayList$ListItr#previous()Ljava/lang/Object; : load 0 java.util.ArrayList$ListItr.this$0 <elem>",
                    "java.util.ArrayList$ListItr#set(Ljava/lang/Object;)V : call 0.java.util.ArrayList$ListItr.this$0 java.util.ArrayList#set(ILjava/lang/Object;)Ljava/lang/Object; _ 1 @ java.util.ArrayList$ListItr#set(Ljava/lang/Object;)V@28",
                    "java.util.ArrayList$ListItr#add(Ljava/lang/Object;)V : call 0.java.util.ArrayList$ListItr.this$0 java.util.ArrayList#add(ILjava/lang/Object;)V _ 1 @ java.util.ArrayList$ListItr#add(Ljava/lang/Object;)V@15",
                    // ---- ArrayList$SubList :1196-1596 (root = the list): reads and writes go through root's representation
                    "java.util.ArrayList$SubList#get(I)Ljava/lang/Object; : load 0 java.util.ArrayList$SubList.root <elem>",
                    "java.util.ArrayList$SubList#set(ILjava/lang/Object;)Ljava/lang/Object; : store 0 java.util.ArrayList$SubList.root <elem> 2 ; load 0 java.util.ArrayList$SubList.root <elem>",
                    "java.util.ArrayList$SubList#size()I : observe 0",
                    "java.util.ArrayList$SubList#add(ILjava/lang/Object;)V : call 0.java.util.ArrayList$SubList.root java.util.ArrayList#add(ILjava/lang/Object;)V _ 2 @ java.util.ArrayList$SubList#add(ILjava/lang/Object;)V@20",
                    "java.util.ArrayList$SubList#remove(I)Ljava/lang/Object; : call 0.java.util.ArrayList$SubList.root java.util.ArrayList#remove(I)Ljava/lang/Object; _ -> result @ java.util.ArrayList$SubList#remove(I)Ljava/lang/Object;@23",
                    "java.util.ArrayList$SubList#removeRange(II)V : call 0.java.util.ArrayList$SubList.root java.util.ArrayList#removeRange(II)V _ _ @ java.util.ArrayList$SubList#removeRange(II)V@20",
                    "java.util.ArrayList$SubList#addAll(Ljava/util/Collection;)Z : call 0 java.util.ArrayList$SubList#addAll(ILjava/util/Collection;)Z _ 1 @ java.util.ArrayList$SubList#addAll(Ljava/util/Collection;)Z@6",
                    "java.util.ArrayList$SubList#addAll(ILjava/util/Collection;)Z : call 2 java.util.Collection#size()I @ java.util.ArrayList$SubList#addAll(ILjava/util/Collection;)Z@6 ; call 0.java.util.ArrayList$SubList.root java.util.ArrayList" +
                                    "#addAll(ILjava/util/Collection;)Z _ 2 @ java.util.ArrayList$SubList#addAll(ILjava/util/Collection;)Z@33",
                    "java.util.ArrayList$SubList#replaceAll(Ljava/util/function/UnaryOperator;)V : call 1 java.util.function.UnaryOperator#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.java.util.ArrayList$SubList.root/<elem> -> $ @ java.util.ArrayList" +
                                    "#replaceAllRange(Ljava/util/function/UnaryOperator;II)V@41 ; store 0 java.util.ArrayList$SubList.root <elem> $",
                    "java.util.ArrayList$SubList#removeAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#contains(Ljava/lang/Object;)Z 0.java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@29 @ java.util.ArrayList" +
                                    "#batchRemove(Ljava/util/Collection;ZII)Z@70",
                    "java.util.ArrayList$SubList#retainAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#contains(Ljava/lang/Object;)Z 0.java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList#batchRemove(Ljava/util/Collection;ZII)Z@29 @ java.util.ArrayList" +
                                    "#batchRemove(Ljava/util/Collection;ZII)Z@70",
                    "java.util.ArrayList$SubList#removeIf(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList" +
                                    "#removeIf(Ljava/util/function/Predicate;II)Z@29 @ java.util.ArrayList#removeIf(Ljava/util/function/Predicate;II)Z@82",
                    "java.util.ArrayList$SubList#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.java.util.ArrayList$SubList.root/<elem>",
                    "java.util.ArrayList$SubList#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : fresh ~[Ljava.lang.Object; ; store R [] 0.java.util.ArrayList$SubList.root/<elem> ; store 1 [] 0.java.util.ArrayList$SubList.root/<elem> ; alias 1",
                    "java.util.ArrayList$SubList#equals(Ljava/lang/Object;)Z : call 1 java.util.List#iterator()Ljava/util/Iterator; -> $1 @ java.util.ArrayList#equalsRange(Ljava/util/List;II)Z@22 ; call $1 java.util.Iterator#hasNext()Z @ java.util.ArrayList" +
                                    "#equalsRange(Ljava/util/List;II)Z@36 @ java.util.ArrayList#equalsRange(Ljava/util/List;II)Z@71 ; call $1 java.util.Iterator#next()Ljava/lang/Object; -> $2 @ java.util.ArrayList" +
                                    "#equalsRange(Ljava/util/List;II)Z@50 ; call 0.java.util.ArrayList$SubList.root/<elem> java.lang.Object#equals(Ljava/lang/Object;)Z $2 @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11",
                    "java.util.ArrayList$SubList#hashCode()I : call 0.java.util.ArrayList$SubList.root/<elem> java.lang.Object#hashCode()I @ java.util.ArrayList#hashCodeRange(II)I@53",
                    "java.util.ArrayList$SubList#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList#indexOfRange(Ljava/lang/Object;II)I@54",
                    "java.util.ArrayList$SubList#lastIndexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList#lastIndexOfRange(Ljava/lang/Object;II)I@58",
                    "java.util.ArrayList$SubList#contains(Ljava/lang/Object;)Z : call 0 java.util.ArrayList$SubList#indexOf(Ljava/lang/Object;)I 1 @ java.util.ArrayList$SubList#contains(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayList$SubList#iterator()Ljava/util/Iterator; : call 0 java.util.AbstractList#listIterator()Ljava/util/ListIterator; -> result @ java.util.ArrayList$SubList#iterator()Ljava/util/Iterator;@1",
                    "java.util.ArrayList$SubList#listIterator(I)Ljava/util/ListIterator; : fresh java.util.ArrayList$SubList$1 ; store R java.util.ArrayList$SubList$1.this$0 0",
                    "java.util.ArrayList$SubList#subList(II)Ljava/util/List; : fresh java.util.ArrayList$SubList ; store R java.util.ArrayList$SubList.root 0.java.util.ArrayList$SubList.root ; store R java.util.ArrayList$SubList.parent 0",
                    // ---- ArrayList$SubList$1 :1366-1480 (this$0 = the sublist; its root's representation)
                    "java.util.ArrayList$SubList$1#hasNext()Z : observe 0",
                    "java.util.ArrayList$SubList$1#hasPrevious()Z : observe 0",
                    "java.util.ArrayList$SubList$1#nextIndex()I : observe 0",
                    "java.util.ArrayList$SubList$1#previousIndex()I : observe 0",
                    "java.util.ArrayList$SubList$1#next()Ljava/lang/Object; : load 0 java.util.ArrayList$SubList$1.this$0 java.util.ArrayList$SubList.root <elem>",
                    "java.util.ArrayList$SubList$1#previous()Ljava/lang/Object; : load 0 java.util.ArrayList$SubList$1.this$0 java.util.ArrayList$SubList.root <elem>",
                    "java.util.ArrayList$SubList$1#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$SubList$1.this$0/java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList" +
                                    "$SubList$1#forEachRemaining(Ljava/util/function/Consumer;)V@95",
                    "java.util.ArrayList$SubList$1#remove()V : call 0.java.util.ArrayList$SubList$1.this$0 java.util.ArrayList$SubList#remove(I)Ljava/lang/Object; _ @ java.util.ArrayList$SubList$1#remove()V@27",
                    "java.util.ArrayList$SubList$1#set(Ljava/lang/Object;)V : call 0.java.util.ArrayList$SubList$1.this$0/java.util.ArrayList$SubList.root java.util.ArrayList#set(ILjava/lang/Object;)Ljava/lang/Object; _ 1 @ java.util.ArrayList$SubList$1#set(Ljava/lang/Object;)V@39",
                    "java.util.ArrayList$SubList$1#add(Ljava/lang/Object;)V : call 0.java.util.ArrayList$SubList$1.this$0 java.util.ArrayList$SubList#add(ILjava/lang/Object;)V _ 1 @ java.util.ArrayList$SubList$1#add(Ljava/lang/Object;)V@15",
                    // ---- ArrayList$ArrayListSpliterator :1663-1733 (F4 needs tryAdvance / forEachRemaining / trySplit)
                    "java.util.ArrayList$ArrayListSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$ArrayListSpliterator.this$0/<elem> @ java.util.ArrayList" +
                                    "$ArrayListSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@48",
                    "java.util.ArrayList$ArrayListSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$ArrayListSpliterator.this$0/<elem> @ java.util.ArrayList" +
                                    "$ArrayListSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@95",
                    "java.util.ArrayList$ArrayListSpliterator#trySplit()Ljava/util/ArrayList$ArrayListSpliterator; : fresh java.util.ArrayList$ArrayListSpliterator ; store R java.util.ArrayList$ArrayListSpliterator.this$0 0.java.util.ArrayList$ArrayListSpliterator.this$0",
                    "java.util.ArrayList$ArrayListSpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.ArrayList$ArrayListSpliterator ; store R java.util.ArrayList$ArrayListSpliterator.this$0 0.java.util.ArrayList$ArrayListSpliterator.this$0",
                    "java.util.ArrayList$ArrayListSpliterator#estimateSize()J : observe 0",
                    "java.util.ArrayList$ArrayListSpliterator#characteristics()I : observe 0",
                    // ---- Vector (jdk:java/util/Vector.java; elementData :106 is protected: a user subclass's access meets the field rule)
                    "java.util.Vector#<init>()V : observe 0 ; key seq.new",
                    "java.util.Vector#<init>(I)V : observe 0 ; key seq.newCap",
                    "java.util.Vector#<init>(II)V : observe 0",
                    "java.util.Vector#<init>(Ljava/util/Collection;)V : call 1 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.Vector#<init>(Ljava/util/Collection;)V@5 ; store 0 <elem> $.[]",
                    "java.util.Vector#copyInto([Ljava/lang/Object;)V : store 1 [] 0.<elem>",
                    "java.util.Vector#trimToSize()V : observe 0 ; key seq.trim",
                    "java.util.Vector#ensureCapacity(I)V : observe 0 ; key seq.ensureCapacity",
                    "java.util.Vector#setSize(I)V : observe 0",
                    "java.util.Vector#capacity()I : observe 0",
                    "java.util.Vector#size()I : observe 0 ; key seq.size",
                    "java.util.Vector#isEmpty()Z : observe 0 ; key seq.isEmpty",
                    "java.util.Vector#elements()Ljava/util/Enumeration; : fresh java.util.Vector$1 ; store R java.util.Vector$1.this$0 0",
                    "java.util.Vector#contains(Ljava/lang/Object;)Z : call 0 java.util.Vector#indexOf(Ljava/lang/Object;I)I 1 _ @ java.util.Vector#contains(Ljava/lang/Object;)Z@3",
                    "java.util.Vector#indexOf(Ljava/lang/Object;)I : call 0 java.util.Vector#indexOf(Ljava/lang/Object;I)I 1 _ @ java.util.Vector#indexOf(Ljava/lang/Object;)I@3",
                    "java.util.Vector#indexOf(Ljava/lang/Object;I)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.Vector#indexOf(Ljava/lang/Object;I)I@51",
                    "java.util.Vector#lastIndexOf(Ljava/lang/Object;)I : call 0 java.util.Vector#lastIndexOf(Ljava/lang/Object;I)I 1 _ @ java.util.Vector#lastIndexOf(Ljava/lang/Object;)I@8",
                    "java.util.Vector#lastIndexOf(Ljava/lang/Object;I)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.Vector#lastIndexOf(Ljava/lang/Object;I)I@85",
                    "java.util.Vector#elementAt(I)Ljava/lang/Object; : load 0 <elem> ; key seq.get",
                    "java.util.Vector#firstElement()Ljava/lang/Object; : load 0 <elem> ; key seq.getFirst",
                    "java.util.Vector#lastElement()Ljava/lang/Object; : load 0 <elem> ; key seq.getLast",
                    "java.util.Vector#setElementAt(Ljava/lang/Object;I)V : store 0 <elem> 1",
                    "java.util.Vector#removeElementAt(I)V : observe 0",
                    "java.util.Vector#insertElementAt(Ljava/lang/Object;I)V : store 0 <elem> 1",
                    "java.util.Vector#addElement(Ljava/lang/Object;)V : store 0 <elem> 1",
                    "java.util.Vector#removeElement(Ljava/lang/Object;)Z : call 0 java.util.Vector#indexOf(Ljava/lang/Object;)I 1 @ java.util.Vector#removeElement(Ljava/lang/Object;)Z@12 ; call 0 java.util.Vector#removeElementAt(I)V _ @ java.util.Vector" +
                                    "#removeElement(Ljava/lang/Object;)Z@22",
                    "java.util.Vector#removeAllElements()V : observe 0 ; key seq.clear",
                    "java.util.Vector#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.Vector#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : fresh ~[Ljava.lang.Object; ; store R [] 0.<elem> ; store 1 [] 0.<elem> ; alias 1",
                    "java.util.Vector#get(I)Ljava/lang/Object; : load 0 <elem> ; key seq.get",
                    "java.util.Vector#set(ILjava/lang/Object;)Ljava/lang/Object; : store 0 <elem> 2 ; load 0 <elem> ; key seq.set",
                    "java.util.Vector#add(Ljava/lang/Object;)Z : store 0 <elem> 1 ; key seq.add",
                    "java.util.Vector#remove(Ljava/lang/Object;)Z : call 0 java.util.Vector#removeElement(Ljava/lang/Object;)Z 1 @ java.util.Vector#remove(Ljava/lang/Object;)Z@2",
                    "java.util.Vector#add(ILjava/lang/Object;)V : call 0 java.util.Vector#insertElementAt(Ljava/lang/Object;I)V 2 _ @ java.util.Vector#add(ILjava/lang/Object;)V@3",
                    "java.util.Vector#remove(I)Ljava/lang/Object; : load 0 <elem> ; key seq.removeAt",
                    "java.util.Vector#clear()V : call 0 java.util.Vector#removeAllElements()V @ java.util.Vector#clear()V@1",
                    "java.util.Vector#addAll(Ljava/util/Collection;)Z : call 1 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.Vector#addAll(Ljava/util/Collection;)Z@1 ; store 0 <elem> $.[]",
                    "java.util.Vector#addAll(ILjava/util/Collection;)Z : call 2 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.Vector#addAll(ILjava/util/Collection;)Z@22 ; store 0 <elem> $.[]",
                    "java.util.Vector#removeRange(II)V : observe 0",
                    // :1015-1037 `super.equals(o)` / `super.hashCode()` / `super.toString()` / `super.containsAll(c)`: AbstractList's
                    // templates (the IR: their calls on this re-dispatch into the model; they touch no representation)
                    "java.util.Vector#equals(Ljava/lang/Object;)Z : ir-closed 0 ; ir-closed 1",
                    "java.util.Vector#hashCode()I : ir-closed 0",
                    "java.util.Vector#toString()Ljava/lang/String; : ir-closed 0 ; result ir-closed",
                    "java.util.Vector#containsAll(Ljava/util/Collection;)Z : ir-closed 0 ; ir-closed 1",
                    "java.util.Vector#listIterator(I)Ljava/util/ListIterator; : fresh java.util.Vector$ListItr ; store R java.util.Vector$ListItr.this$0 0 ; store R java.util.Vector$Itr.this$0 0",
                    "java.util.Vector#listIterator()Ljava/util/ListIterator; : fresh java.util.Vector$ListItr ; store R java.util.Vector$ListItr.this$0 0 ; store R java.util.Vector$Itr.this$0 0",
                    "java.util.Vector#iterator()Ljava/util/Iterator; : fresh java.util.Vector$Itr ; store R java.util.Vector$Itr.this$0 0",
                    "java.util.Vector#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.Vector#forEach(Ljava/util/function/Consumer;)V@46",
                    "java.util.Vector#replaceAll(Ljava/util/function/UnaryOperator;)V : call 1 java.util.function.UnaryOperator#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.<elem> -> $ @ java.util.Vector" +
                                    "#replaceAll(Ljava/util/function/UnaryOperator;)V@49 ; store 0 <elem> $",
                    "java.util.Vector#removeIf(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.Vector#bulkRemove(Ljava/util/function/Predicate;)Z@33 @ java.util.Vector" +
                                    "#bulkRemove(Ljava/util/function/Predicate;)Z@93",
                    "java.util.Vector#spliterator()Ljava/util/Spliterator; : fresh java.util.Vector$VectorSpliterator ; store R java.util.Vector$VectorSpliterator.this$0 0",
                    // Vector$1 (elements()), Vector$Itr, Vector$ListItr, Vector$VectorSpliterator (its `array` is a snapshot of the representation)
                    "java.util.Vector$1#hasMoreElements()Z : observe 0",
                    "java.util.Vector$1#nextElement()Ljava/lang/Object; : load 0 java.util.Vector$1.this$0 <elem>",
                    "java.util.Vector$Itr#hasNext()Z : observe 0 ; key seq.itrHasNext",
                    "java.util.Vector$Itr#next()Ljava/lang/Object; : load 0 java.util.Vector$Itr.this$0 <elem> ; key seq.vitrNext",
                    "java.util.Vector$Itr#remove()V : call 0.java.util.Vector$Itr.this$0 java.util.Vector#remove(I)Ljava/lang/Object; _ @ java.util.Vector$Itr#remove()V@35",
                    "java.util.Vector$Itr#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Vector$Itr.this$0/<elem> @ java.util.Vector" +
                                    "$Itr#forEachRemaining(Ljava/util/function/Consumer;)V@91",
                    "java.util.Vector$Itr#checkForComodification()V : observe 0",
                    "java.util.Vector$ListItr#hasPrevious()Z : observe 0",
                    "java.util.Vector$ListItr#nextIndex()I : observe 0",
                    "java.util.Vector$ListItr#previousIndex()I : observe 0",
                    "java.util.Vector$ListItr#previous()Ljava/lang/Object; : load 0 java.util.Vector$ListItr.this$0 <elem>",
                    "java.util.Vector$ListItr#set(Ljava/lang/Object;)V : call 0.java.util.Vector$ListItr.this$0 java.util.Vector#set(ILjava/lang/Object;)Ljava/lang/Object; _ 1 @ java.util.Vector$ListItr#set(Ljava/lang/Object;)V@36",
                    "java.util.Vector$ListItr#add(Ljava/lang/Object;)V : call 0.java.util.Vector$ListItr.this$0 java.util.Vector#add(ILjava/lang/Object;)V _ 1 @ java.util.Vector$ListItr#add(Ljava/lang/Object;)V@22",
                    "java.util.Vector$VectorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Vector$VectorSpliterator.this$0/<elem> @ java.util.Vector" +
                                    "$VectorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@32",
                    "java.util.Vector$VectorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Vector$VectorSpliterator.this$0/<elem> @ java.util.Vector" +
                                    "$VectorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@37",
                    "java.util.Vector$VectorSpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.Vector$VectorSpliterator ; store R java.util.Vector$VectorSpliterator.this$0 0.java.util.Vector$VectorSpliterator.this$0",
                    "java.util.Vector$VectorSpliterator#estimateSize()J : observe 0",
                    "java.util.Vector$VectorSpliterator#characteristics()I : observe 0",
                    // ---- Stack (jdk:java/util/Stack.java): every call on this is a callback (a subclass may override it)
                    "java.util.Stack#<init>()V : observe 0 ; key seq.new",
                    "java.util.Stack#push(Ljava/lang/Object;)Ljava/lang/Object; : call 0 java.util.Vector#addElement(Ljava/lang/Object;)V 1 @ java.util.Stack#push(Ljava/lang/Object;)Ljava/lang/Object;@2 ; alias 1",
                    "java.util.Stack#pop()Ljava/lang/Object; : call 0 java.util.Vector#size()I @ java.util.Stack#pop()Ljava/lang/Object;@1 ; call 0 java.util.Stack#peek()Ljava/lang/Object; -> result @ java.util.Stack#pop()Ljava/lang/Object;" +
                                    "@6 ; call 0 java.util.Vector#removeElementAt(I)V _ @ java.util.Stack#pop()Ljava/lang/Object;@14",
                    "java.util.Stack#peek()Ljava/lang/Object; : call 0 java.util.Vector#size()I @ java.util.Stack#peek()Ljava/lang/Object;@1 ; call 0 java.util.Vector#elementAt(I)Ljava/lang/Object; _ -> result @ java.util.Stack#peek()Ljava/lang/Object;@21",
                    "java.util.Stack#empty()Z : call 0 java.util.Vector#size()I @ java.util.Stack#empty()Z@1",
                    "java.util.Stack#search(Ljava/lang/Object;)I : call 0 java.util.Vector#lastIndexOf(Ljava/lang/Object;)I 1 @ java.util.Stack#search(Ljava/lang/Object;)I@2 ; call 0 java.util.Vector#size()I @ java.util.Stack#search(Ljava/lang/Object;)I@11",
                    // ---- LinkedList, ArrayDeque, PriorityQueue, the immutable lists, Arrays.asList, Collections.singletonList, List.of
                    // (from the builder JDK's bytecode through the premise checker's proposals, JdkModelPremiseTest#proposeEntries;
                    // not listed, refused by name: clone, reversed, descendingIterator, the spliterators of LinkedList/ArrayDeque/
                    // PriorityQueue, PriorityQueue's iterator and its copy constructors (two callback results), ArrayDeque's
                    // addAll / removeAll / retainAll / copy constructor (a lambda that captures the deque))
                    "java.util.LinkedList#<init>()V : observe 0 ; key seq.new",
                    "java.util.LinkedList#<init>(Ljava/util/Collection;)V : call 0 java.util.LinkedList#addAll(Ljava/util/Collection;)Z 1 @ java.util.LinkedList#<init>(Ljava/util/Collection;)V@6",
                    "java.util.LinkedList#remove()Ljava/lang/Object; : call 0 java.util.LinkedList#removeFirst()Ljava/lang/Object; -> result @ java.util.LinkedList#remove()Ljava/lang/Object;@1",
                    "java.util.LinkedList#remove(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.LinkedList#remove(Ljava/lang/Object;)Z@53",
                    "java.util.LinkedList#remove(I)Ljava/lang/Object; : alias 0.<elem> ; key seq.removeAt",
                    "java.util.LinkedList#size()I : observe 0 ; key seq.size",
                    "java.util.LinkedList#get(I)Ljava/lang/Object; : alias 0.<elem> ; key seq.get",
                    "java.util.LinkedList#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.LinkedList#indexOf(Ljava/lang/Object;)I@52",
                    "java.util.LinkedList#clear()V : observe 0 ; key seq.clear",
                    "java.util.LinkedList#lastIndexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.LinkedList#lastIndexOf(Ljava/lang/Object;)I@58",
                    "java.util.LinkedList#add(ILjava/lang/Object;)V : store 0 <elem> 2 ; key seq.addAt",
                    "java.util.LinkedList#add(Ljava/lang/Object;)Z : store 0 <elem> 1 ; key seq.add",
                    "java.util.LinkedList#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.LinkedList#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : store 1 [] 0.<elem> ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.LinkedList#contains(Ljava/lang/Object;)Z : call 0 java.util.LinkedList#indexOf(Ljava/lang/Object;)I 1 @ java.util.LinkedList#contains(Ljava/lang/Object;)Z@2",
                    "java.util.LinkedList#addAll(ILjava/util/Collection;)Z : call 2 java.util.Collection#toArray()[Ljava/lang/Object; -> $ @ java.util.LinkedList#addAll(ILjava/util/Collection;)Z@6 ; store 0 <elem> $.[]",
                    "java.util.LinkedList#addAll(Ljava/util/Collection;)Z : call 0 java.util.LinkedList#addAll(ILjava/util/Collection;)Z _ 1 @ java.util.LinkedList#addAll(Ljava/util/Collection;)Z@6",
                    "java.util.LinkedList#set(ILjava/lang/Object;)Ljava/lang/Object; : store 0 <elem> 2 ; alias 0.<elem> ; key seq.set",
                    "java.util.LinkedList#peek()Ljava/lang/Object; : alias 0.<elem>",
                    "java.util.LinkedList#getFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.getFirst",
                    "java.util.LinkedList#getLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.getLast",
                    "java.util.LinkedList#element()Ljava/lang/Object; : call 0 java.util.LinkedList#getFirst()Ljava/lang/Object; -> result @ java.util.LinkedList#element()Ljava/lang/Object;@1",
                    "java.util.LinkedList#addFirst(Ljava/lang/Object;)V : store 0 <elem> 1 ; key seq.addFirst",
                    "java.util.LinkedList#addLast(Ljava/lang/Object;)V : store 0 <elem> 1 ; key seq.addLast",
                    "java.util.LinkedList#removeFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.removeFirst",
                    "java.util.LinkedList#removeLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.removeLast",
                    "java.util.LinkedList#listIterator(I)Ljava/util/ListIterator; : fresh java.util.LinkedList$ListItr ; store R java.util.LinkedList$ListItr.this$0 0",
                    "java.util.LinkedList#poll()Ljava/lang/Object; : alias 0.<elem>",
                    "java.util.LinkedList#offer(Ljava/lang/Object;)Z : call 0 java.util.LinkedList#add(Ljava/lang/Object;)Z 1 @ java.util.LinkedList#offer(Ljava/lang/Object;)Z@2",
                    "java.util.LinkedList#push(Ljava/lang/Object;)V : call 0 java.util.LinkedList#addFirst(Ljava/lang/Object;)V 1 @ java.util.LinkedList#push(Ljava/lang/Object;)V@2",
                    "java.util.LinkedList#pop()Ljava/lang/Object; : call 0 java.util.LinkedList#removeFirst()Ljava/lang/Object; -> result @ java.util.LinkedList#pop()Ljava/lang/Object;@1",
                    "java.util.LinkedList#pollFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.pollFirst",
                    "java.util.LinkedList#pollLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.pollLast",
                    "java.util.LinkedList#offerLast(Ljava/lang/Object;)Z : call 0 java.util.LinkedList#addLast(Ljava/lang/Object;)V 1 @ java.util.LinkedList#offerLast(Ljava/lang/Object;)Z@2",
                    "java.util.LinkedList#peekFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.peekFirst",
                    "java.util.LinkedList#removeFirstOccurrence(Ljava/lang/Object;)Z : call 0 java.util.LinkedList#remove(Ljava/lang/Object;)Z 1 @ java.util.LinkedList#removeFirstOccurrence(Ljava/lang/Object;)Z@2",
                    "java.util.LinkedList#offerFirst(Ljava/lang/Object;)Z : call 0 java.util.LinkedList#addFirst(Ljava/lang/Object;)V 1 @ java.util.LinkedList#offerFirst(Ljava/lang/Object;)Z@2",
                    "java.util.LinkedList#peekLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.peekLast",
                    "java.util.LinkedList#removeLastOccurrence(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.LinkedList#removeLastOccurrence(Ljava/lang/Object;)Z@53",
                    "java.util.LinkedList$ListItr#remove()V : observe 0",
                    "java.util.LinkedList$ListItr#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.LinkedList$ListItr.this$0/<elem> @ java.util.LinkedList$ListItr#forEachRemaining(Ljava/util/function/Consumer;)V@41",
                    "java.util.LinkedList$ListItr#add(Ljava/lang/Object;)V : store 0 java.util.LinkedList$ListItr.this$0 <elem> 1",
                    "java.util.LinkedList$ListItr#hasNext()Z : observe 0",
                    "java.util.LinkedList$ListItr#next()Ljava/lang/Object; : call 0 java.util.LinkedList$ListItr#hasNext()Z @ java.util.LinkedList$ListItr#next()Ljava/lang/Object;@5 ; alias 0.java.util.LinkedList$ListItr.this$0/<elem>",
                    "java.util.LinkedList$ListItr#set(Ljava/lang/Object;)V : store 0 java.util.LinkedList$ListItr.this$0 <elem> 1",
                    "java.util.LinkedList$ListItr#nextIndex()I : observe 0",
                    "java.util.LinkedList$ListItr#checkForComodification()V : observe 0",
                    "java.util.LinkedList$ListItr#previousIndex()I : observe 0",
                    "java.util.LinkedList$ListItr#hasPrevious()Z : observe 0",
                    "java.util.LinkedList$ListItr#previous()Ljava/lang/Object; : call 0 java.util.LinkedList$ListItr#hasPrevious()Z @ java.util.LinkedList$ListItr#previous()Ljava/lang/Object;@5 ; alias 0.java.util.LinkedList$ListItr.this$0/<elem>",
                    "java.util.ArrayDeque#<init>(I)V : observe 0 ; key seq.newCap",
                    "java.util.ArrayDeque#<init>()V : observe 0 ; key seq.new",
                    "java.util.ArrayDeque#remove()Ljava/lang/Object; : call 0 java.util.ArrayDeque#removeFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#remove()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#remove(Ljava/lang/Object;)Z : call 0 java.util.ArrayDeque#removeFirstOccurrence(Ljava/lang/Object;)Z 1 @ java.util.ArrayDeque#remove(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayDeque#size()I : observe 0 ; key seq.size",
                    "java.util.ArrayDeque#clear()V : observe 0 ; key seq.clear",
                    "java.util.ArrayDeque#isEmpty()Z : observe 0 ; key seq.isEmpty",
                    "java.util.ArrayDeque#add(Ljava/lang/Object;)Z : call 0 java.util.ArrayDeque#addLast(Ljava/lang/Object;)V 1 @ java.util.ArrayDeque#add(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayDeque#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : call 0 java.util.ArrayDeque#size()I @ java.util.ArrayDeque#toArray([Ljava/lang/Object;)[Ljava/lang/Object;@1 ; store 1 [] 0.<elem> ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.ArrayDeque#toArray()[Ljava/lang/Object; : fresh ~[Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.ArrayDeque#iterator()Ljava/util/Iterator; : call 0 java.util.ArrayDeque#size()I @ java.util.ArrayDeque$DeqIterator#<init>(Ljava/util/ArrayDeque;)V@19 ; fresh java.util.ArrayDeque$DeqIterator ; store R java.util.ArrayDeque$DeqIterator.this$0 0",
                    "java.util.ArrayDeque#contains(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayDeque#contains(Ljava/lang/Object;)Z@45",
                    "java.util.ArrayDeque#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.ArrayDeque#forEach(Ljava/util/function/Consumer;)V@48",
                    "java.util.ArrayDeque#peek()Ljava/lang/Object; : call 0 java.util.ArrayDeque#peekFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#peek()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#removeIf(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayDeque#bulkRemove(Ljava/util/function/Predicate;)Z@43 @ java.util.ArrayDeque#bulkRemoveModified(Ljava/util/function/Predicate;I)Z@71",
                    "java.util.ArrayDeque#getFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.getFirst",
                    "java.util.ArrayDeque#getLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.getLast",
                    "java.util.ArrayDeque#element()Ljava/lang/Object; : call 0 java.util.ArrayDeque#getFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#element()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#addFirst(Ljava/lang/Object;)V : store 0 <elem> 1 ; key seq.addFirst",
                    "java.util.ArrayDeque#addLast(Ljava/lang/Object;)V : store 0 <elem> 1 ; key seq.addLast",
                    "java.util.ArrayDeque#removeFirst()Ljava/lang/Object; : call 0 java.util.ArrayDeque#pollFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#removeFirst()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#removeLast()Ljava/lang/Object; : call 0 java.util.ArrayDeque#pollLast()Ljava/lang/Object; -> result @ java.util.ArrayDeque#removeLast()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#poll()Ljava/lang/Object; : call 0 java.util.ArrayDeque#pollFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#poll()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#offer(Ljava/lang/Object;)Z : call 0 java.util.ArrayDeque#offerLast(Ljava/lang/Object;)Z 1 @ java.util.ArrayDeque#offer(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayDeque#push(Ljava/lang/Object;)V : call 0 java.util.ArrayDeque#addFirst(Ljava/lang/Object;)V 1 @ java.util.ArrayDeque#push(Ljava/lang/Object;)V@2",
                    "java.util.ArrayDeque#pop()Ljava/lang/Object; : call 0 java.util.ArrayDeque#removeFirst()Ljava/lang/Object; -> result @ java.util.ArrayDeque#pop()Ljava/lang/Object;@1",
                    "java.util.ArrayDeque#pollFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.pollFirst",
                    "java.util.ArrayDeque#pollLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.pollLast",
                    "java.util.ArrayDeque#offerLast(Ljava/lang/Object;)Z : call 0 java.util.ArrayDeque#addLast(Ljava/lang/Object;)V 1 @ java.util.ArrayDeque#offerLast(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayDeque#peekFirst()Ljava/lang/Object; : alias 0.<elem> ; key seq.peekFirst",
                    "java.util.ArrayDeque#removeFirstOccurrence(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayDeque#removeFirstOccurrence(Ljava/lang/Object;)Z@45",
                    "java.util.ArrayDeque#offerFirst(Ljava/lang/Object;)Z : call 0 java.util.ArrayDeque#addFirst(Ljava/lang/Object;)V 1 @ java.util.ArrayDeque#offerFirst(Ljava/lang/Object;)Z@2",
                    "java.util.ArrayDeque#peekLast()Ljava/lang/Object; : alias 0.<elem> ; key seq.peekLast",
                    "java.util.ArrayDeque#removeLastOccurrence(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.ArrayDeque#removeLastOccurrence(Ljava/lang/Object;)Z@49",
                    "java.util.ArrayDeque$DeqIterator#remove()V : observe 0",
                    "java.util.ArrayDeque$DeqIterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayDeque$DeqIterator.this$0/<elem> @ java.util.ArrayDeque$DeqIterator#forEachRemaining(Ljava/util/function/Consumer;)V@110",
                    "java.util.ArrayDeque$DeqIterator#hasNext()Z : observe 0",
                    "java.util.ArrayDeque$DeqIterator#next()Ljava/lang/Object; : alias 0.java.util.ArrayDeque$DeqIterator.this$0/<elem>",
                    "java.util.ArrayDeque$DeqIterator#postDelete(Z)V : observe 0",
                    "java.util.PriorityQueue#<init>(ILjava/util/Comparator;)V : store 0 java.util.PriorityQueue.comparator 2",
                    "java.util.PriorityQueue#<init>()V : observe 0 ; key seq.new",
                    "java.util.PriorityQueue#<init>(I)V : observe 0 ; key seq.newCap",
                    "java.util.PriorityQueue#<init>(Ljava/util/Comparator;)V : store 0 java.util.PriorityQueue.comparator 1",
                    "java.util.PriorityQueue#remove(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.PriorityQueue#indexOf(Ljava/lang/Object;)I@27 ; call 0.<elem> java.lang.Comparable#compareTo(Ljava/lang/Object;)I 0.<elem> @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@72 @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@51 @ java.util.PriorityQueue#siftUpComparable(ILjava/lang/Object;[Ljava/lang/Object;)V@25 ; call 0.java.util.PriorityQueue.comparator java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 0.<elem> 0.<elem> @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@66 @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@44 @ java.util.PriorityQueue#siftUpUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;Ljava/util/Comparator;)V@21",
                    "java.util.PriorityQueue#size()I : observe 0 ; key seq.size",
                    "java.util.PriorityQueue#clear()V : observe 0 ; key seq.clear",
                    "java.util.PriorityQueue#add(Ljava/lang/Object;)Z : call 0 java.util.PriorityQueue#offer(Ljava/lang/Object;)Z 1 @ java.util.PriorityQueue#add(Ljava/lang/Object;)Z@2",
                    "java.util.PriorityQueue#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.PriorityQueue#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : store 1 [] 0.<elem> ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.PriorityQueue#contains(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.<elem> @ java.util.PriorityQueue#indexOf(Ljava/lang/Object;)I@27",
                    "java.util.PriorityQueue#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.PriorityQueue#forEach(Ljava/util/function/Consumer;)V@36",
                    "java.util.PriorityQueue#peek()Ljava/lang/Object; : alias 0.<elem>",
                    "java.util.PriorityQueue#removeIf(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.PriorityQueue#bulkRemove(Ljava/util/function/Predicate;)Z@38 @ java.util.PriorityQueue#bulkRemove(Ljava/util/function/Predicate;)Z@114 ; call 0.<elem> java.lang.Comparable#compareTo(Ljava/lang/Object;)I 0.<elem> @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@72 @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@51 ; call 0.java.util.PriorityQueue.comparator java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 0.<elem> 0.<elem> @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@66 @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@44",
                    "java.util.PriorityQueue#comparator()Ljava/util/Comparator; : alias 0.java.util.PriorityQueue.comparator",
                    "java.util.PriorityQueue#poll()Ljava/lang/Object; : call 0.<elem> java.lang.Comparable#compareTo(Ljava/lang/Object;)I 0.<elem> @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@72 @ java.util.PriorityQueue#siftDownComparable(ILjava/lang/Object;[Ljava/lang/Object;I)V@51 ; call 0.java.util.PriorityQueue.comparator java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 0.<elem> 0.<elem> @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@66 @ java.util.PriorityQueue#siftDownUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;ILjava/util/Comparator;)V@44 ; alias 0.<elem>",
                    "java.util.PriorityQueue#offer(Ljava/lang/Object;)Z : call 1 java.lang.Comparable#compareTo(Ljava/lang/Object;)I 0.<elem> @ java.util.PriorityQueue#siftUpComparable(ILjava/lang/Object;[Ljava/lang/Object;)V@25 ; call 0.java.util.PriorityQueue.comparator java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 1 0.<elem> @ java.util.PriorityQueue#siftUpUsingComparator(ILjava/lang/Object;[Ljava/lang/Object;Ljava/util/Comparator;)V@21 ; store 0 <elem> 1",
                    "java.util.ImmutableCollections$List12#<init>(Ljava/lang/Object;)V : store 0 java.util.ImmutableCollections$List12.e0 1",
                    "java.util.ImmutableCollections$List12#<init>(Ljava/lang/Object;Ljava/lang/Object;)V : store 0 java.util.ImmutableCollections$List12.e0 1 ; store 0 java.util.ImmutableCollections$List12.e1 2",
                    "java.util.ImmutableCollections$List12#size()I : observe 0",
                    "java.util.ImmutableCollections$List12#get(I)Ljava/lang/Object; : call 0 java.util.AbstractCollection#size()I @ java.util.ImmutableCollections$AbstractImmutableList#outOfBounds(I)Ljava/lang/IndexOutOfBoundsException;@26 ; alias 0.java.util.ImmutableCollections$List12.e0 ; alias 0.java.util.ImmutableCollections$List12.e1",
                    "java.util.ImmutableCollections$List12#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$List12.e0 @ java.util.ImmutableCollections$List12#indexOf(Ljava/lang/Object;)I@10 ; call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$List12.e1 @ java.util.ImmutableCollections$List12#indexOf(Ljava/lang/Object;)I@33",
                    "java.util.ImmutableCollections$List12#lastIndexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$List12.e1 @ java.util.ImmutableCollections$List12#lastIndexOf(Ljava/lang/Object;)I@20 ; call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$List12.e0 @ java.util.ImmutableCollections$List12#lastIndexOf(Ljava/lang/Object;)I@33",
                    "java.util.ImmutableCollections$List12#isEmpty()Z : observe 0",
                    "java.util.ImmutableCollections$List12#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : store 1 [] 0.java.util.ImmutableCollections$List12.e0 ; store 1 [] 0.java.util.ImmutableCollections$List12.e1 ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.java.util.ImmutableCollections$List12.e0 ; store R [] 0.java.util.ImmutableCollections$List12.e1",
                    "java.util.ImmutableCollections$List12#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.java.util.ImmutableCollections$List12.e0 ; store R [] 0.java.util.ImmutableCollections$List12.e1",
                    "java.util.ImmutableCollections$List12#spliterator()Ljava/util/Spliterator; : ir 0 ; result ir",
                    "java.util.ImmutableCollections$List12#readObject(Ljava/io/ObjectInputStream;)V : observe 0 ; observe 1",
                    "java.util.ImmutableCollections$List12#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ImmutableCollections$List12.e0 @ java.util.ImmutableCollections$List12#forEach(Ljava/util/function/Consumer;)V@5 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ImmutableCollections$List12.e1 @ java.util.ImmutableCollections$List12#forEach(Ljava/util/function/Consumer;)V@25",
                    "java.util.ImmutableCollections$ListN#<init>([Ljava/lang/Object;Z)V : store 0 java.util.ImmutableCollections$ListN.elements 1",
                    "java.util.ImmutableCollections$ListN#size()I : observe 0",
                    "java.util.ImmutableCollections$ListN#get(I)Ljava/lang/Object; : alias 0.java.util.ImmutableCollections$ListN.elements/[]",
                    "java.util.ImmutableCollections$ListN#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$ListN.elements/[] @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11",
                    "java.util.ImmutableCollections$ListN#lastIndexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.ImmutableCollections$ListN.elements/[] @ java.util.Objects#equals(Ljava/lang/Object;Ljava/lang/Object;)Z@11",
                    "java.util.ImmutableCollections$ListN#isEmpty()Z : observe 0",
                    "java.util.ImmutableCollections$ListN#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.java.util.ImmutableCollections$ListN.elements/[]",
                    "java.util.ImmutableCollections$ListN#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : store 1 [] 0.java.util.ImmutableCollections$ListN.elements/[] ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.java.util.ImmutableCollections$ListN.elements/[]",
                    "java.util.ImmutableCollections$ListN#readObject(Ljava/io/ObjectInputStream;)V : observe 0 ; observe 1",
                    "java.util.ImmutableCollections$ListItr#remove()V : observe 0",
                    "java.util.ImmutableCollections$ListItr#add(Ljava/lang/Object;)V : observe 0 ; observe 1",
                    "java.util.ImmutableCollections$ListItr#hasNext()Z : observe 0",
                    "java.util.ImmutableCollections$ListItr#next()Ljava/lang/Object; : call 0.java.util.ImmutableCollections$ListItr.list java.util.List#get(I)Ljava/lang/Object; _ -> result @ java.util.ImmutableCollections$ListItr#next()Ljava/lang/Object;@10",
                    "java.util.ImmutableCollections$ListItr#set(Ljava/lang/Object;)V : observe 0 ; observe 1",
                    "java.util.ImmutableCollections$ListItr#nextIndex()I : observe 0",
                    "java.util.ImmutableCollections$ListItr#previousIndex()I : observe 0",
                    "java.util.ImmutableCollections$ListItr#hasPrevious()Z : observe 0",
                    "java.util.ImmutableCollections$ListItr#previous()Ljava/lang/Object; : call 0.java.util.ImmutableCollections$ListItr.list java.util.List#get(I)Ljava/lang/Object; _ -> result @ java.util.ImmutableCollections$ListItr#previous()Ljava/lang/Object;@23",
                    "java.util.Arrays$ArrayList#size()I : observe 0",
                    "java.util.Arrays$ArrayList#get(I)Ljava/lang/Object; : alias 0.java.util.Arrays$ArrayList.a/[]",
                    "java.util.Arrays$ArrayList#indexOf(Ljava/lang/Object;)I : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.Arrays$ArrayList.a/[] @ java.util.Arrays$ArrayList#indexOf(Ljava/lang/Object;)I@46",
                    "java.util.Arrays$ArrayList#replaceAll(Ljava/util/function/UnaryOperator;)V : call 1 java.util.function.UnaryOperator#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.java.util.Arrays$ArrayList.a/[] -> $ @ java.util.Arrays$ArrayList#replaceAll(Ljava/util/function/UnaryOperator;)V@24 ; store 0 java.util.Arrays$ArrayList.a [] $",
                    "java.util.Arrays$ArrayList#toArray()[Ljava/lang/Object; : fresh ~[Ljava.lang.Object; ; store R [] 0.java.util.Arrays$ArrayList.a/[]",
                    "java.util.Arrays$ArrayList#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : call 0 java.util.Arrays$ArrayList#size()I @ java.util.Arrays$ArrayList#toArray([Ljava/lang/Object;)[Ljava/lang/Object;@1 ; store 1 [] 0.java.util.Arrays$ArrayList.a/[] ; alias 1 ; fresh ~[Ljava.lang.Object; ; store R [] 0.java.util.Arrays$ArrayList.a/[]",
                    "java.util.Arrays$ArrayList#iterator()Ljava/util/Iterator; : fresh java.util.Arrays$ArrayItr ; store R java.util.Arrays$ArrayItr.a 0.java.util.Arrays$ArrayList.a",
                    "java.util.Arrays$ArrayList#contains(Ljava/lang/Object;)Z : call 0 java.util.Arrays$ArrayList#indexOf(Ljava/lang/Object;)I 1 @ java.util.Arrays$ArrayList#contains(Ljava/lang/Object;)Z@2",
                    "java.util.Arrays$ArrayList#spliterator()Ljava/util/Spliterator; : ir 0 ; result ir",
                    "java.util.Arrays$ArrayList#set(ILjava/lang/Object;)Ljava/lang/Object; : store 0 java.util.Arrays$ArrayList.a [] 2 ; alias 0.java.util.Arrays$ArrayList.a/[]",
                    "java.util.Arrays$ArrayList#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Arrays$ArrayList.a/[] @ java.util.Arrays$ArrayList#forEach(Ljava/util/function/Consumer;)V@31",
                    "java.util.Arrays$ArrayItr#hasNext()Z : observe 0",
                    "java.util.Arrays$ArrayItr#next()Ljava/lang/Object; : alias 0.java.util.Arrays$ArrayItr.a/[]",
                    "java.util.Collections$SingletonList#size()I : observe 0",
                    "java.util.Collections$SingletonList#get(I)Ljava/lang/Object; : alias 0.java.util.Collections$SingletonList.element",
                    "java.util.Collections$SingletonList#hashCode()I : call 0.java.util.Collections$SingletonList.element java.lang.Object#hashCode()I @ java.util.Objects#hashCode(Ljava/lang/Object;)I@5",
                    "java.util.Collections$SingletonList#sort(Ljava/util/Comparator;)V : observe 0 ; observe 1",
                    "java.util.Collections$SingletonList#replaceAll(Ljava/util/function/UnaryOperator;)V : observe 0 ; observe 1",
                    "java.util.Collections$SingletonList#iterator()Ljava/util/Iterator; : fresh java.util.Collections$1 ; store R java.util.Collections$1.val$e 0.java.util.Collections$SingletonList.element",
                    "java.util.Collections$SingletonList#contains(Ljava/lang/Object;)Z : call 1 java.lang.Object#equals(Ljava/lang/Object;)Z 0.java.util.Collections$SingletonList.element @ java.util.Collections#eq(Ljava/lang/Object;Ljava/lang/Object;)Z@18",
                    "java.util.Collections$SingletonList#spliterator()Ljava/util/Spliterator; : ir 0 ; result ir",
                    "java.util.Collections$SingletonList#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Collections$SingletonList.element @ java.util.Collections$SingletonList#forEach(Ljava/util/function/Consumer;)V@5",
                    "java.util.Collections$SingletonList#removeIf(Ljava/util/function/Predicate;)Z : observe 0 ; observe 1",
                    "java.util.Collections$1#remove()V : observe 0",
                    "java.util.Collections$1#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Collections$1.val$e @ java.util.Collections$1#forEachRemaining(Ljava/util/function/Consumer;)V@22",
                    "java.util.Collections$1#hasNext()Z : observe 0",
                    "java.util.Collections$1#next()Ljava/lang/Object; : alias 0.java.util.Collections$1.val$e",
                    // The spliterator coverage F4 needs: the spliterators over F1's slots are fresh
                    // views (no trySplit batch arrays for LinkedList: the IR, whose representation accesses refuse)
                    "java.util.LinkedList#spliterator()Ljava/util/Spliterator; : fresh java.util.LinkedList$LLSpliterator ; store R java.util.LinkedList$LLSpliterator.list 0",
                    "java.util.LinkedList$LLSpliterator#<init>(Ljava/util/LinkedList;II)V : store 0 java.util.LinkedList$LLSpliterator.list 1",
                    "java.util.LinkedList$LLSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.LinkedList$LLSpliterator.list/<elem> @ java.util.LinkedList$LLSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@54",
                    "java.util.LinkedList$LLSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.LinkedList$LLSpliterator.list/<elem> @ java.util.LinkedList$LLSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@53",
                    "java.util.LinkedList$LLSpliterator#characteristics()I : observe 0",
                    "java.util.LinkedList$LLSpliterator#estimateSize()J : observe 0",
                    "java.util.LinkedList$LLSpliterator#getEst()I : observe 0",
                    "java.util.ArrayDeque#spliterator()Ljava/util/Spliterator; : fresh java.util.ArrayDeque$DeqSpliterator ; store R java.util.ArrayDeque$DeqSpliterator.this$0 0",
                    "java.util.ArrayDeque$DeqSpliterator#<init>(Ljava/util/ArrayDeque;)V : store 0 java.util.ArrayDeque$DeqSpliterator.this$0 1",
                    "java.util.ArrayDeque$DeqSpliterator#<init>(Ljava/util/ArrayDeque;II)V : store 0 java.util.ArrayDeque$DeqSpliterator.this$0 1",
                    "java.util.ArrayDeque$DeqSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayDeque$DeqSpliterator.this$0/<elem> @ java.util.ArrayDeque$DeqSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@102",
                    "java.util.ArrayDeque$DeqSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayDeque$DeqSpliterator.this$0/<elem> @ java.util.ArrayDeque$DeqSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@77",
                    "java.util.ArrayDeque$DeqSpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.ArrayDeque$DeqSpliterator ; store R java.util.ArrayDeque$DeqSpliterator.this$0 0.java.util.ArrayDeque$DeqSpliterator.this$0",
                    "java.util.ArrayDeque$DeqSpliterator#trySplit()Ljava/util/ArrayDeque$DeqSpliterator; : fresh java.util.ArrayDeque$DeqSpliterator ; store R java.util.ArrayDeque$DeqSpliterator.this$0 0.java.util.ArrayDeque$DeqSpliterator.this$0",
                    "java.util.ArrayDeque$DeqSpliterator#characteristics()I : observe 0",
                    "java.util.ArrayDeque$DeqSpliterator#estimateSize()J : observe 0",
                    "java.util.ArrayDeque$DeqSpliterator#getFence()I : observe 0",
                    "java.util.PriorityQueue#spliterator()Ljava/util/Spliterator; : fresh java.util.PriorityQueue$PriorityQueueSpliterator ; store R java.util.PriorityQueue$PriorityQueueSpliterator.this$0 0",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#<init>(Ljava/util/PriorityQueue;III)V : store 0 java.util.PriorityQueue$PriorityQueueSpliterator.this$0 1",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.PriorityQueue$PriorityQueueSpliterator.this$0/<elem> @ java.util.PriorityQueue$PriorityQueueSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@86",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.PriorityQueue$PriorityQueueSpliterator.this$0/<elem> @ java.util.PriorityQueue$PriorityQueueSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@99",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.PriorityQueue$PriorityQueueSpliterator ; store R java.util.PriorityQueue$PriorityQueueSpliterator.this$0 0.java.util.PriorityQueue$PriorityQueueSpliterator.this$0",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#trySplit()Ljava/util/PriorityQueue$PriorityQueueSpliterator; : fresh java.util.PriorityQueue$PriorityQueueSpliterator ; store R java.util.PriorityQueue$PriorityQueueSpliterator.this$0 0.java.util.PriorityQueue$PriorityQueueSpliterator.this$0",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#characteristics()I : observe 0",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#estimateSize()J : observe 0",
                    "java.util.PriorityQueue$PriorityQueueSpliterator#getFence()I : observe 0",
                    "java.util.ArrayList$SubList#spliterator()Ljava/util/Spliterator; : fresh java.util.ArrayList$SubList$2 ; store R java.util.ArrayList$SubList$2.this$0 0",
                    "java.util.ArrayList$SubList$2#<init>(Ljava/util/ArrayList$SubList;)V : store 0 java.util.ArrayList$SubList$2.this$0 1",
                    "java.util.ArrayList$SubList$2#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$SubList$2.this$0/java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList$SubList$2#forEachRemaining(Ljava/util/function/Consumer;)V@103",
                    "java.util.ArrayList$SubList$2#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.ArrayList$SubList$2.this$0/java.util.ArrayList$SubList.root/<elem> @ java.util.ArrayList$SubList$2#tryAdvance(Ljava/util/function/Consumer;)Z@44",
                    "java.util.ArrayList$SubList$2#trySplit()Ljava/util/Spliterator; : call 0 java.util.ArrayList$SubList$2#trySplit()Ljava/util/ArrayList$ArrayListSpliterator; -> result @ java.util.ArrayList$SubList$2#trySplit()Ljava/util/Spliterator;@1",
                    "java.util.ArrayList$SubList$2#trySplit()Ljava/util/ArrayList$ArrayListSpliterator; : fresh java.util.ArrayList$ArrayListSpliterator ; store R java.util.ArrayList$ArrayListSpliterator.this$0 0.java.util.ArrayList$SubList$2.this$0/java.util.ArrayList$SubList.root",
                    "java.util.ArrayList$SubList$2#characteristics()I : observe 0",
                    "java.util.ArrayList$SubList$2#estimateSize()J : observe 0",
                    "java.util.ArrayList$SubList$2#getFence()I : observe 0",
                    "java.util.Arrays#asList([Ljava/lang/Object;)Ljava/util/List; : fresh java.util.Arrays$ArrayList ; store R java.util.Arrays$ArrayList.a 0",
                    "java.util.Collections#singletonList(Ljava/lang/Object;)Ljava/util/List; : fresh java.util.Collections$SingletonList ; store R java.util.Collections$SingletonList.element 0",
                    "java.util.List#of(Ljava/lang/Object;)Ljava/util/List; : fresh java.util.ImmutableCollections$List12 ; store R java.util.ImmutableCollections$List12.e0 0",
                    "java.util.List#of(Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/List; : fresh java.util.ImmutableCollections$List12 ; store R java.util.ImmutableCollections$List12.e0 0 ; store R java.util.ImmutableCollections$List12.e1 1");

    /**
     * F3, views and wrappers over real fields: the {@code Collections.unmodifiable*} and {@code Collections.synchronized*}
     * collection and list wrappers and their iterators. Every operation forwards to the delegate ({@code c},
     * {@code list}, the wrapped iterator {@code i}) as a callback whose receiver is that field's value, or throws (an
     * observation). The callback's targets come from the delegate atom's exact type: one crossing per wrapper rather than
     * a CHA fan over every implementation (which a recursion such as {@code Collections$UnmodifiableCollection.stream()}
     * needs). Views whose representation is a storage list's slot (the iterators of ArrayList, Vector, LinkedList,
     * ArrayDeque, the sublist, the spliterators) and views over real fields of F1's lists are F1 entries. No closed class,
     * no abstracted field: an unlisted method is walked as IR. Not listed (walked as IR): the factories (a class chosen at
     * run time), serialization, {@code reversed}, the {@code Checked*} wrappers (their type check builds an exception
     * message from the element's class: exception flow). JDK citations: jdk:java/util/Collections.java.
     */
    static final Family F3 = new Family("f3", true, Set.of(), Map.of(), Set.of(),
                    Set.of("java.util.Collections$CheckedCollection", "java.util.Collections$CheckedList", "java.util.Collections$CheckedRandomAccessList",
                                    "java.util.Collections$CheckedCollection$1", "java.util.Collections$CheckedList$1"),
                    // The spliterator coverage F4 needs: the default spliterators (jdk:java/util/Spliterators.java
                    // IteratorSpliterator over a collection or an iterator; ArraySpliterator over an array), the singleton spliterator
                    // (Collections.singletonSpliterator), and the traversal defaults of Iterable and Iterator (real fields: open classes)
                    "java.util.Collection#spliterator()Ljava/util/Spliterator; : fresh java.util.Spliterators$IteratorSpliterator ; store R java.util.Spliterators$IteratorSpliterator.collection 0",
                    "java.lang.Iterable#spliterator()Ljava/util/Spliterator; : call 0 java.lang.Iterable#iterator()Ljava/util/Iterator; -> $1 @ java.lang.Iterable#spliterator()Ljava/util/Spliterator;@1 ; fresh java.util.Spliterators$IteratorSpliterator ; store R java.util.Spliterators$IteratorSpliterator.it $1",
                    "java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V : call 0 java.lang.Iterable#iterator()Ljava/util/Iterator; -> $1 @ java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V@6 ; call $1 java.util.Iterator#hasNext()Z @ java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V@13 ; call $1 java.util.Iterator#next()Ljava/lang/Object; -> $2 @ java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V@22 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V $2 @ java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V@30",
                    "java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 0 java.util.Iterator#hasNext()Z @ java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V@6 ; call 0 java.util.Iterator#next()Ljava/lang/Object; -> $1 @ java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V@16 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V $1 @ java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V@21",
                    "java.util.Spliterators$IteratorSpliterator#<init>(Ljava/util/Iterator;I)V : store 0 java.util.Spliterators$IteratorSpliterator.it 1",
                    "java.util.Spliterators$IteratorSpliterator#<init>(Ljava/util/Iterator;JI)V : store 0 java.util.Spliterators$IteratorSpliterator.it 1",
                    "java.util.Spliterators$IteratorSpliterator#<init>(Ljava/util/Collection;I)V : store 0 java.util.Spliterators$IteratorSpliterator.collection 1",
                    "java.util.Spliterators$IteratorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#iterator()Ljava/util/Iterator; -> $1 @ java.util.Spliterators$IteratorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@26 ; call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#size()I @ java.util.Spliterators$IteratorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@41 ; store 0 java.util.Spliterators$IteratorSpliterator.it $1 ; call 0.java.util.Spliterators$IteratorSpliterator.it java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V 1 @ java.util.Spliterators$IteratorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@52 ; call $1 java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V 1 @ java.util.Spliterators$IteratorSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@52",
                    "java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#iterator()Ljava/util/Iterator; -> $1 @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@24 ; call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#size()I @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@37 ; store 0 java.util.Spliterators$IteratorSpliterator.it $1 ; call 0.java.util.Spliterators$IteratorSpliterator.it java.util.Iterator#hasNext()Z @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@50 ; call $1 java.util.Iterator#hasNext()Z @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@50 ; call 0.java.util.Spliterators$IteratorSpliterator.it java.util.Iterator#next()Ljava/lang/Object; -> $2 @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@63 ; call $1 java.util.Iterator#next()Ljava/lang/Object; -> $3 @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@63 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V $2 @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@68 ; call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V $3 @ java.util.Spliterators$IteratorSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@68",
                    "java.util.Spliterators$IteratorSpliterator#estimateSize()J : call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#iterator()Ljava/util/Iterator; -> $1 @ java.util.Spliterators$IteratorSpliterator#estimateSize()J@12 ; call 0.java.util.Spliterators$IteratorSpliterator.collection java.util.Collection#size()I @ java.util.Spliterators$IteratorSpliterator#estimateSize()J@25 ; store 0 java.util.Spliterators$IteratorSpliterator.it $1",
                    "java.util.Spliterators$IteratorSpliterator#characteristics()I : observe 0",
                    "java.util.Spliterators$ArraySpliterator#<init>([Ljava/lang/Object;IIIJ)V : store 0 java.util.Spliterators$ArraySpliterator.array 1",
                    "java.util.Spliterators$ArraySpliterator#<init>([Ljava/lang/Object;III)V : store 0 java.util.Spliterators$ArraySpliterator.array 1",
                    "java.util.Spliterators$ArraySpliterator#<init>([Ljava/lang/Object;I)V : store 0 java.util.Spliterators$ArraySpliterator.array 1",
                    "java.util.Spliterators$ArraySpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Spliterators$ArraySpliterator.array/[] @ java.util.Spliterators$ArraySpliterator#forEachRemaining(Ljava/util/function/Consumer;)V@53",
                    "java.util.Spliterators$ArraySpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Spliterators$ArraySpliterator.array/[] @ java.util.Spliterators$ArraySpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@49",
                    "java.util.Spliterators$ArraySpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.Spliterators$ArraySpliterator ; store R java.util.Spliterators$ArraySpliterator.array 0.java.util.Spliterators$ArraySpliterator.array",
                    "java.util.Spliterators$ArraySpliterator#characteristics()I : observe 0",
                    "java.util.Spliterators$ArraySpliterator#estimateSize()J : observe 0",
                    "java.util.Collections$2#<init>(Ljava/lang/Object;)V : store 0 java.util.Collections$2.val$element 1",
                    "java.util.Collections$2#forEachRemaining(Ljava/util/function/Consumer;)V : call 0 java.util.Collections$2#tryAdvance(Ljava/util/function/Consumer;)Z 1 @ java.util.Collections$2#forEachRemaining(Ljava/util/function/Consumer;)V@2",
                    "java.util.Collections$2#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Collections$2.val$element @ java.util.Collections$2#tryAdvance(Ljava/util/function/Consumer;)Z@29",
                    "java.util.Collections$2#characteristics()I : observe 0",
                    "java.util.Collections$2#estimateSize()J : observe 0",
                    "java.util.Collections$UnmodifiableCollection#<init>(Ljava/util/Collection;)V : store 0 java.util.Collections$UnmodifiableCollection.c 1",
                    "java.util.Collections$UnmodifiableCollection#remove(Ljava/lang/Object;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#size()I : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#size()I @ java.util.Collections$UnmodifiableCollection#size()I@4",
                    "java.util.Collections$UnmodifiableCollection#toString()Ljava/lang/String; : call 0.java.util.Collections$UnmodifiableCollection.c java.lang.Object#toString()Ljava/lang/String; -> result @ java.util.Collections$UnmodifiableCollection#toString()Ljava/lang/String;@4",
                    "java.util.Collections$UnmodifiableCollection#clear()V : observe 0",
                    "java.util.Collections$UnmodifiableCollection#isEmpty()Z : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#isEmpty()Z @ java.util.Collections$UnmodifiableCollection#isEmpty()Z@4",
                    "java.util.Collections$UnmodifiableCollection#add(Ljava/lang/Object;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#toArray()[Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#toArray()[Ljava/lang/Object; -> result @ java.util.Collections$UnmodifiableCollection#toArray()[Ljava/lang/Object;@4",
                    "java.util.Collections$UnmodifiableCollection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object; 1 -> result @ java.util.Collections$UnmodifiableCollection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object;@5",
                    "java.util.Collections$UnmodifiableCollection#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#toArray([Ljava/lang/Object;)[Ljava/lang/Object; 1 -> result @ java.util.Collections$UnmodifiableCollection#toArray([Ljava/lang/Object;)[Ljava/lang/Object;@5",
                    "java.util.Collections$UnmodifiableCollection#iterator()Ljava/util/Iterator; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#iterator()Ljava/util/Iterator; -> $ @ java.util.Collections$UnmodifiableCollection$1#<init>(Ljava/util/Collections$UnmodifiableCollection;)V@22 ; fresh java.util.Collections$UnmodifiableCollection$1 ; store R java.util.Collections$UnmodifiableCollection$1.this$0 0 ; store R java.util.Collections$UnmodifiableCollection$1.i $",
                    "java.util.Collections$UnmodifiableCollection#stream()Ljava/util/stream/Stream; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#stream()Ljava/util/stream/Stream; -> result @ java.util.Collections$UnmodifiableCollection#stream()Ljava/util/stream/Stream;@4",
                    "java.util.Collections$UnmodifiableCollection#contains(Ljava/lang/Object;)Z : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#contains(Ljava/lang/Object;)Z 1 @ java.util.Collections$UnmodifiableCollection#contains(Ljava/lang/Object;)Z@5",
                    "java.util.Collections$UnmodifiableCollection#spliterator()Ljava/util/Spliterator; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#spliterator()Ljava/util/Spliterator; -> result @ java.util.Collections$UnmodifiableCollection#spliterator()Ljava/util/Spliterator;@4",
                    "java.util.Collections$UnmodifiableCollection#addAll(Ljava/util/Collection;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#forEach(Ljava/util/function/Consumer;)V : call 0.java.util.Collections$UnmodifiableCollection.c java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V 1 @ java.util.Collections$UnmodifiableCollection#forEach(Ljava/util/function/Consumer;)V@5",
                    "java.util.Collections$UnmodifiableCollection#removeIf(Ljava/util/function/Predicate;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#removeAll(Ljava/util/Collection;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#retainAll(Ljava/util/Collection;)Z : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableCollection#containsAll(Ljava/util/Collection;)Z : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#containsAll(Ljava/util/Collection;)Z 1 @ java.util.Collections$UnmodifiableCollection#containsAll(Ljava/util/Collection;)Z@5",
                    "java.util.Collections$UnmodifiableCollection#parallelStream()Ljava/util/stream/Stream; : call 0.java.util.Collections$UnmodifiableCollection.c java.util.Collection#parallelStream()Ljava/util/stream/Stream; -> result @ java.util.Collections$UnmodifiableCollection#parallelStream()Ljava/util/stream/Stream;@4",
                    "java.util.Collections$UnmodifiableCollection$1#<init>(Ljava/util/Collections$UnmodifiableCollection;)V : call 0.java.util.Collections$UnmodifiableCollection$1.this$0/java.util.Collections$UnmodifiableCollection.c java.util.Collection#iterator()Ljava/util/Iterator; -> $ @ java.util.Collections$UnmodifiableCollection$1#<init>(Ljava/util/Collections$UnmodifiableCollection;)V@22 ; store 0 java.util.Collections$UnmodifiableCollection$1.this$0 1 ; store 0 java.util.Collections$UnmodifiableCollection$1.i $",
                    "java.util.Collections$UnmodifiableCollection$1#remove()V : observe 0",
                    "java.util.Collections$UnmodifiableCollection$1#forEachRemaining(Ljava/util/function/Consumer;)V : call 0.java.util.Collections$UnmodifiableCollection$1.i java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V 1 @ java.util.Collections$UnmodifiableCollection$1#forEachRemaining(Ljava/util/function/Consumer;)V@5",
                    "java.util.Collections$UnmodifiableCollection$1#hasNext()Z : call 0.java.util.Collections$UnmodifiableCollection$1.i java.util.Iterator#hasNext()Z @ java.util.Collections$UnmodifiableCollection$1#hasNext()Z@4",
                    "java.util.Collections$UnmodifiableCollection$1#next()Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableCollection$1.i java.util.Iterator#next()Ljava/lang/Object; -> result @ java.util.Collections$UnmodifiableCollection$1#next()Ljava/lang/Object;@4",
                    "java.util.Collections$UnmodifiableList#<init>(Ljava/util/List;)V : store 0 java.util.Collections$UnmodifiableCollection.c 1 ; store 0 java.util.Collections$UnmodifiableList.list 1",
                    "java.util.Collections$UnmodifiableList#remove(I)Ljava/lang/Object; : ir 0 ; result ir",
                    "java.util.Collections$UnmodifiableList#get(I)Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableList.list java.util.List#get(I)Ljava/lang/Object; _ -> result @ java.util.Collections$UnmodifiableList#get(I)Ljava/lang/Object;@5",
                    "java.util.Collections$UnmodifiableList#equals(Ljava/lang/Object;)Z : call 0.java.util.Collections$UnmodifiableList.list java.util.List#equals(Ljava/lang/Object;)Z 1 @ java.util.Collections$UnmodifiableList#equals(Ljava/lang/Object;)Z@10",
                    "java.util.Collections$UnmodifiableList#hashCode()I : call 0.java.util.Collections$UnmodifiableList.list java.util.List#hashCode()I @ java.util.Collections$UnmodifiableList#hashCode()I@4",
                    "java.util.Collections$UnmodifiableList#sort(Ljava/util/Comparator;)V : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableList#indexOf(Ljava/lang/Object;)I : call 0.java.util.Collections$UnmodifiableList.list java.util.List#indexOf(Ljava/lang/Object;)I 1 @ java.util.Collections$UnmodifiableList#indexOf(Ljava/lang/Object;)I@5",
                    "java.util.Collections$UnmodifiableList#lastIndexOf(Ljava/lang/Object;)I : call 0.java.util.Collections$UnmodifiableList.list java.util.List#lastIndexOf(Ljava/lang/Object;)I 1 @ java.util.Collections$UnmodifiableList#lastIndexOf(Ljava/lang/Object;)I@5",
                    "java.util.Collections$UnmodifiableList#replaceAll(Ljava/util/function/UnaryOperator;)V : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableList#add(ILjava/lang/Object;)V : observe 0 ; observe 2",
                    "java.util.Collections$UnmodifiableList#subList(II)Ljava/util/List; : call 0.java.util.Collections$UnmodifiableList.list java.util.List#subList(II)Ljava/util/List; _ _ -> $ @ java.util.Collections$UnmodifiableList#subList(II)Ljava/util/List;@10 ; fresh java.util.Collections$UnmodifiableList ; store R java.util.Collections$UnmodifiableCollection.c $ ; store R java.util.Collections$UnmodifiableList.list $",
                    "java.util.Collections$UnmodifiableList#addAll(ILjava/util/Collection;)Z : observe 0 ; observe 2",
                    "java.util.Collections$UnmodifiableList#set(ILjava/lang/Object;)Ljava/lang/Object; : ir 0 ; ir 2 ; result ir",
                    "java.util.Collections$UnmodifiableList#listIterator(I)Ljava/util/ListIterator; : call 0.java.util.Collections$UnmodifiableList.list java.util.List#listIterator(I)Ljava/util/ListIterator; _ -> $ @ java.util.Collections$UnmodifiableList$1#<init>(Ljava/util/Collections$UnmodifiableList;I)V@31 ; fresh java.util.Collections$UnmodifiableList$1 ; store R java.util.Collections$UnmodifiableList$1.this$0 0 ; store R java.util.Collections$UnmodifiableList$1.i $",
                    "java.util.Collections$UnmodifiableList#listIterator()Ljava/util/ListIterator; : call 0 java.util.Collections$UnmodifiableList#listIterator(I)Ljava/util/ListIterator; _ -> result @ java.util.Collections$UnmodifiableList#listIterator()Ljava/util/ListIterator;@2",
                    "java.util.Collections$UnmodifiableList$1#<init>(Ljava/util/Collections$UnmodifiableList;I)V : call 0.java.util.Collections$UnmodifiableList$1.this$0/java.util.Collections$UnmodifiableList.list java.util.List#listIterator(I)Ljava/util/ListIterator; _ -> $ @ java.util.Collections$UnmodifiableList$1#<init>(Ljava/util/Collections$UnmodifiableList;I)V@31 ; store 0 java.util.Collections$UnmodifiableList$1.this$0 1 ; store 0 java.util.Collections$UnmodifiableList$1.i $",
                    "java.util.Collections$UnmodifiableList$1#remove()V : observe 0",
                    "java.util.Collections$UnmodifiableList$1#forEachRemaining(Ljava/util/function/Consumer;)V : call 0.java.util.Collections$UnmodifiableList$1.i java.util.Iterator#forEachRemaining(Ljava/util/function/Consumer;)V 1 @ java.util.Collections$UnmodifiableList$1#forEachRemaining(Ljava/util/function/Consumer;)V@5",
                    "java.util.Collections$UnmodifiableList$1#add(Ljava/lang/Object;)V : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableList$1#hasNext()Z : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#hasNext()Z @ java.util.Collections$UnmodifiableList$1#hasNext()Z@4",
                    "java.util.Collections$UnmodifiableList$1#next()Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#next()Ljava/lang/Object; -> result @ java.util.Collections$UnmodifiableList$1#next()Ljava/lang/Object;@4",
                    "java.util.Collections$UnmodifiableList$1#set(Ljava/lang/Object;)V : observe 0 ; observe 1",
                    "java.util.Collections$UnmodifiableList$1#nextIndex()I : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#nextIndex()I @ java.util.Collections$UnmodifiableList$1#nextIndex()I@4",
                    "java.util.Collections$UnmodifiableList$1#previousIndex()I : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#previousIndex()I @ java.util.Collections$UnmodifiableList$1#previousIndex()I@4",
                    "java.util.Collections$UnmodifiableList$1#hasPrevious()Z : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#hasPrevious()Z @ java.util.Collections$UnmodifiableList$1#hasPrevious()Z@4",
                    "java.util.Collections$UnmodifiableList$1#previous()Ljava/lang/Object; : call 0.java.util.Collections$UnmodifiableList$1.i java.util.ListIterator#previous()Ljava/lang/Object; -> result @ java.util.Collections$UnmodifiableList$1#previous()Ljava/lang/Object;@4",
                    "java.util.Collections$UnmodifiableRandomAccessList#<init>(Ljava/util/List;)V : store 0 java.util.Collections$UnmodifiableCollection.c 1 ; store 0 java.util.Collections$UnmodifiableList.list 1",
                    "java.util.Collections$UnmodifiableRandomAccessList#subList(II)Ljava/util/List; : call 0.java.util.Collections$UnmodifiableList.list java.util.List#subList(II)Ljava/util/List; _ _ -> $ @ java.util.Collections$UnmodifiableRandomAccessList#subList(II)Ljava/util/List;@10 ; fresh java.util.Collections$UnmodifiableRandomAccessList ; store R java.util.Collections$UnmodifiableCollection.c $ ; store R java.util.Collections$UnmodifiableList.list $",
                    "java.util.Collections$SynchronizedCollection#<init>(Ljava/util/Collection;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 0",
                    "java.util.Collections$SynchronizedCollection#<init>(Ljava/util/Collection;Ljava/lang/Object;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 2",
                    "java.util.Collections$SynchronizedCollection#remove(Ljava/lang/Object;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#remove(Ljava/lang/Object;)Z 1 @ java.util.Collections$SynchronizedCollection#remove(Ljava/lang/Object;)Z@12",
                    "java.util.Collections$SynchronizedCollection#size()I : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#size()I @ java.util.Collections$SynchronizedCollection#size()I@11",
                    "java.util.Collections$SynchronizedCollection#toString()Ljava/lang/String; : call 0.java.util.Collections$SynchronizedCollection.c java.lang.Object#toString()Ljava/lang/String; -> result @ java.util.Collections$SynchronizedCollection#toString()Ljava/lang/String;@11",
                    "java.util.Collections$SynchronizedCollection#clear()V : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#clear()V @ java.util.Collections$SynchronizedCollection#clear()V@11",
                    "java.util.Collections$SynchronizedCollection#isEmpty()Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#isEmpty()Z @ java.util.Collections$SynchronizedCollection#isEmpty()Z@11",
                    "java.util.Collections$SynchronizedCollection#add(Ljava/lang/Object;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#add(Ljava/lang/Object;)Z 1 @ java.util.Collections$SynchronizedCollection#add(Ljava/lang/Object;)Z@12",
                    "java.util.Collections$SynchronizedCollection#toArray([Ljava/lang/Object;)[Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#toArray([Ljava/lang/Object;)[Ljava/lang/Object; 1 -> result @ java.util.Collections$SynchronizedCollection#toArray([Ljava/lang/Object;)[Ljava/lang/Object;@12",
                    "java.util.Collections$SynchronizedCollection#toArray()[Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#toArray()[Ljava/lang/Object; -> result @ java.util.Collections$SynchronizedCollection#toArray()[Ljava/lang/Object;@11",
                    "java.util.Collections$SynchronizedCollection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object; 1 -> result @ java.util.Collections$SynchronizedCollection#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object;@12",
                    "java.util.Collections$SynchronizedCollection#iterator()Ljava/util/Iterator; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#iterator()Ljava/util/Iterator; -> result @ java.util.Collections$SynchronizedCollection#iterator()Ljava/util/Iterator;@4",
                    "java.util.Collections$SynchronizedCollection#stream()Ljava/util/stream/Stream; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#stream()Ljava/util/stream/Stream; -> result @ java.util.Collections$SynchronizedCollection#stream()Ljava/util/stream/Stream;@4",
                    "java.util.Collections$SynchronizedCollection#contains(Ljava/lang/Object;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#contains(Ljava/lang/Object;)Z 1 @ java.util.Collections$SynchronizedCollection#contains(Ljava/lang/Object;)Z@12",
                    "java.util.Collections$SynchronizedCollection#spliterator()Ljava/util/Spliterator; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#spliterator()Ljava/util/Spliterator; -> result @ java.util.Collections$SynchronizedCollection#spliterator()Ljava/util/Spliterator;@4",
                    "java.util.Collections$SynchronizedCollection#addAll(Ljava/util/Collection;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#addAll(Ljava/util/Collection;)Z 1 @ java.util.Collections$SynchronizedCollection#addAll(Ljava/util/Collection;)Z@12",
                    "java.util.Collections$SynchronizedCollection#forEach(Ljava/util/function/Consumer;)V : call 0.java.util.Collections$SynchronizedCollection.c java.lang.Iterable#forEach(Ljava/util/function/Consumer;)V 1 @ java.util.Collections$SynchronizedCollection#forEach(Ljava/util/function/Consumer;)V@12",
                    "java.util.Collections$SynchronizedCollection#removeIf(Ljava/util/function/Predicate;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#removeIf(Ljava/util/function/Predicate;)Z 1 @ java.util.Collections$SynchronizedCollection#removeIf(Ljava/util/function/Predicate;)Z@12",
                    "java.util.Collections$SynchronizedCollection#removeAll(Ljava/util/Collection;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#removeAll(Ljava/util/Collection;)Z 1 @ java.util.Collections$SynchronizedCollection#removeAll(Ljava/util/Collection;)Z@12",
                    "java.util.Collections$SynchronizedCollection#retainAll(Ljava/util/Collection;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#retainAll(Ljava/util/Collection;)Z 1 @ java.util.Collections$SynchronizedCollection#retainAll(Ljava/util/Collection;)Z@12",
                    "java.util.Collections$SynchronizedCollection#containsAll(Ljava/util/Collection;)Z : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#containsAll(Ljava/util/Collection;)Z 1 @ java.util.Collections$SynchronizedCollection#containsAll(Ljava/util/Collection;)Z@12",
                    "java.util.Collections$SynchronizedCollection#parallelStream()Ljava/util/stream/Stream; : call 0.java.util.Collections$SynchronizedCollection.c java.util.Collection#parallelStream()Ljava/util/stream/Stream; -> result @ java.util.Collections$SynchronizedCollection#parallelStream()Ljava/util/stream/Stream;@4",
                    "java.util.Collections$SynchronizedList#<init>(Ljava/util/List;Ljava/lang/Object;Ljava/util/Collections$SynchronizedList;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 2 ; store 0 java.util.Collections$SynchronizedList.list 1 ; store 0 java.util.Collections$SynchronizedList.reversedView 3",
                    "java.util.Collections$SynchronizedList#<init>(Ljava/util/List;Ljava/lang/Object;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 2 ; store 0 java.util.Collections$SynchronizedList.list 1",
                    "java.util.Collections$SynchronizedList#<init>(Ljava/util/List;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 0 ; store 0 java.util.Collections$SynchronizedList.list 1",
                    "java.util.Collections$SynchronizedList#remove(I)Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#remove(I)Ljava/lang/Object; _ -> result @ java.util.Collections$SynchronizedList#remove(I)Ljava/lang/Object;@12",
                    "java.util.Collections$SynchronizedList#get(I)Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#get(I)Ljava/lang/Object; _ -> result @ java.util.Collections$SynchronizedList#get(I)Ljava/lang/Object;@12",
                    "java.util.Collections$SynchronizedList#equals(Ljava/lang/Object;)Z : call 0.java.util.Collections$SynchronizedList.list java.util.List#equals(Ljava/lang/Object;)Z 1 @ java.util.Collections$SynchronizedList#equals(Ljava/lang/Object;)Z@19",
                    "java.util.Collections$SynchronizedList#hashCode()I : call 0.java.util.Collections$SynchronizedList.list java.util.List#hashCode()I @ java.util.Collections$SynchronizedList#hashCode()I@11",
                    "java.util.Collections$SynchronizedList#sort(Ljava/util/Comparator;)V : call 0.java.util.Collections$SynchronizedList.list java.util.List#sort(Ljava/util/Comparator;)V 1 @ java.util.Collections$SynchronizedList#sort(Ljava/util/Comparator;)V@12",
                    "java.util.Collections$SynchronizedList#indexOf(Ljava/lang/Object;)I : call 0.java.util.Collections$SynchronizedList.list java.util.List#indexOf(Ljava/lang/Object;)I 1 @ java.util.Collections$SynchronizedList#indexOf(Ljava/lang/Object;)I@12",
                    "java.util.Collections$SynchronizedList#lastIndexOf(Ljava/lang/Object;)I : call 0.java.util.Collections$SynchronizedList.list java.util.List#lastIndexOf(Ljava/lang/Object;)I 1 @ java.util.Collections$SynchronizedList#lastIndexOf(Ljava/lang/Object;)I@12",
                    "java.util.Collections$SynchronizedList#replaceAll(Ljava/util/function/UnaryOperator;)V : call 0.java.util.Collections$SynchronizedList.list java.util.List#replaceAll(Ljava/util/function/UnaryOperator;)V 1 @ java.util.Collections$SynchronizedList#replaceAll(Ljava/util/function/UnaryOperator;)V@12",
                    "java.util.Collections$SynchronizedList#add(ILjava/lang/Object;)V : call 0.java.util.Collections$SynchronizedList.list java.util.List#add(ILjava/lang/Object;)V _ 2 @ java.util.Collections$SynchronizedList#add(ILjava/lang/Object;)V@13",
                    "java.util.Collections$SynchronizedList#subList(II)Ljava/util/List; : call 0.java.util.Collections$SynchronizedList.list java.util.List#subList(II)Ljava/util/List; _ _ -> $ @ java.util.Collections$SynchronizedList#subList(II)Ljava/util/List;@17 ; fresh java.util.Collections$SynchronizedList ; store R java.util.Collections$SynchronizedCollection.c $ ; store R java.util.Collections$SynchronizedCollection.mutex 0.java.util.Collections$SynchronizedCollection.mutex ; store R java.util.Collections$SynchronizedList.list $",
                    "java.util.Collections$SynchronizedList#addAll(ILjava/util/Collection;)Z : call 0.java.util.Collections$SynchronizedList.list java.util.List#addAll(ILjava/util/Collection;)Z _ 2 @ java.util.Collections$SynchronizedList#addAll(ILjava/util/Collection;)Z@13",
                    "java.util.Collections$SynchronizedList#set(ILjava/lang/Object;)Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#set(ILjava/lang/Object;)Ljava/lang/Object; _ 2 -> result @ java.util.Collections$SynchronizedList#set(ILjava/lang/Object;)Ljava/lang/Object;@13",
                    "java.util.Collections$SynchronizedList#getFirst()Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#getFirst()Ljava/lang/Object; -> result @ java.util.Collections$SynchronizedList#getFirst()Ljava/lang/Object;@11",
                    "java.util.Collections$SynchronizedList#getLast()Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#getLast()Ljava/lang/Object; -> result @ java.util.Collections$SynchronizedList#getLast()Ljava/lang/Object;@11",
                    "java.util.Collections$SynchronizedList#addFirst(Ljava/lang/Object;)V : call 0.java.util.Collections$SynchronizedList.list java.util.List#addFirst(Ljava/lang/Object;)V 1 @ java.util.Collections$SynchronizedList#addFirst(Ljava/lang/Object;)V@12",
                    "java.util.Collections$SynchronizedList#addLast(Ljava/lang/Object;)V : call 0.java.util.Collections$SynchronizedList.list java.util.List#addLast(Ljava/lang/Object;)V 1 @ java.util.Collections$SynchronizedList#addLast(Ljava/lang/Object;)V@12",
                    "java.util.Collections$SynchronizedList#removeFirst()Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#removeFirst()Ljava/lang/Object; -> result @ java.util.Collections$SynchronizedList#removeFirst()Ljava/lang/Object;@11",
                    "java.util.Collections$SynchronizedList#removeLast()Ljava/lang/Object; : call 0.java.util.Collections$SynchronizedList.list java.util.List#removeLast()Ljava/lang/Object; -> result @ java.util.Collections$SynchronizedList#removeLast()Ljava/lang/Object;@11",
                    "java.util.Collections$SynchronizedList#listIterator()Ljava/util/ListIterator; : call 0.java.util.Collections$SynchronizedList.list java.util.List#listIterator()Ljava/util/ListIterator; -> result @ java.util.Collections$SynchronizedList#listIterator()Ljava/util/ListIterator;@4",
                    "java.util.Collections$SynchronizedList#listIterator(I)Ljava/util/ListIterator; : call 0.java.util.Collections$SynchronizedList.list java.util.List#listIterator(I)Ljava/util/ListIterator; _ -> result @ java.util.Collections$SynchronizedList#listIterator(I)Ljava/util/ListIterator;@5",
                    "java.util.Collections$SynchronizedRandomAccessList#<init>(Ljava/util/List;Ljava/lang/Object;Ljava/util/Collections$SynchronizedList;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 2 ; store 0 java.util.Collections$SynchronizedList.list 1 ; store 0 java.util.Collections$SynchronizedList.reversedView 3",
                    "java.util.Collections$SynchronizedRandomAccessList#<init>(Ljava/util/List;Ljava/lang/Object;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 2 ; store 0 java.util.Collections$SynchronizedList.list 1",
                    "java.util.Collections$SynchronizedRandomAccessList#<init>(Ljava/util/List;)V : store 0 java.util.Collections$SynchronizedCollection.c 1 ; store 0 java.util.Collections$SynchronizedCollection.mutex 0 ; store 0 java.util.Collections$SynchronizedList.list 1",
                    "java.util.Collections$SynchronizedRandomAccessList#subList(II)Ljava/util/List; : call 0.java.util.Collections$SynchronizedList.list java.util.List#subList(II)Ljava/util/List; _ _ -> $ @ java.util.Collections$SynchronizedRandomAccessList#subList(II)Ljava/util/List;@17 ; fresh java.util.Collections$SynchronizedRandomAccessList ; store R java.util.Collections$SynchronizedCollection.c $ ; store R java.util.Collections$SynchronizedCollection.mutex 0.java.util.Collections$SynchronizedCollection.mutex ; store R java.util.Collections$SynchronizedList.list $");

    /** Is class {@code cls} closed by {@code f} (its closed set, or a closed prefix that no open prefix excepts)? */
    static boolean closedBy(Family f, String cls) {
        if (f.closed.contains(cls)) {
            return true;
        }
        for (String p : f.closedPrefixes) {
            if (cls.startsWith(p)) {
                for (String o : f.openPrefixes) {
                    if (cls.startsWith(o)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

    /**
     * F4, streams: {@code java.util.stream} pipelines as a lazy family. A stage is a fresh object of the real stage class
     * whose slot {@code <elem>} holds its elements: a head's are what its source spliterator's traversal hands to the op's
     * sink {@code S} (F1 / F3's spliterator models re-dispatch into it); a stateless stage's are its upstream's
     * ({@code filter}, {@code peek}, {@code limit}/{@code skip}) or its callback's results ({@code map}; {@code flatMap}:
     * what the mapped streams' {@code forEach} hands to S). A stage's callbacks (run by the JDK when the terminal
     * operation pulls) are applied at the stage's call, on the upstream's elements. Sound for data flow: a slot has no
     * per-node pool access (a model load connects to every store), so the elements are read whatever the order; parallel
     * evaluation is treated as sequential (the same elements reach the same callbacks; the combiners are applied once, on
     * the supplier states). Terminal operations read the elements ({@code forEach}, {@code collect} with the collector's
     * functions as callbacks at the ReduceOps sink sites, the matches, {@code findFirst}/{@code findAny}/{@code min}/
     * {@code max} as a fresh {@code Optional}, {@code reduce} through a fresh accumulator box, {@code toArray},
     * {@code toList}, {@code iterator}/{@code spliterator} as views over the stage). Every {@code java.util.stream} class
     * is closed except the collectors ({@code Collector}, {@code Collectors}: IR, their lambdas call the modelled
     * collections); {@code AbstractPipeline}'s links are abstracted, so a stage the IR would allocate refuses by the field
     * rule and never reaches a model with an empty slot. Requires F1 and F3. Not modelled (refused by name): primitive
     * streams, {@code sorted}, {@code distinct}, {@code mapMulti}, {@code gather}, {@code takeWhile}/{@code dropWhile},
     * {@code onClose}/{@code Stream.concat}, {@code StreamSupport.stream(Supplier, ...)},
     * {@code Stream.iterate/generate/builder}; a user Spliterator (the traversed object refuses by name, {@code sink-ir}).
     * JDK citations: jdk:java/util/stream/.
     */
    static final Family F4 = lazy(new Family("f4", true, Set.of(), Map.of(
                    "java.util.stream.AbstractPipeline.sourceStage", "-", "java.util.stream.AbstractPipeline.previousStage", "-", "java.util.stream.AbstractPipeline.nextStage", "-",
                    "java.util.stream.AbstractPipeline.sourceSpliterator", "-", "java.util.stream.AbstractPipeline.sourceSupplier", "-"),
                    Set.of(), Set.of(), Set.of("f1", "f3"),
                    // ---- sources (Collection.java:747 `StreamSupport.stream(spliterator(), false)`; StreamSupport.java:67-71 a Head whose
                    // characteristics are read at once, StreamOpFlag.fromCharacteristics, and whose spliterator is traversed at the terminal)
                    "java.util.Collection#stream()Ljava/util/stream/Stream; : call 0 java.util.Collection#spliterator()Ljava/util/Spliterator; -> $1 @ java.util.Collection#stream()Ljava/util/stream/Stream;@1 ; call $1 java.util.Spliterator#characteristics()I @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@1 ; call $1 java.util.Spliterator#getComparator()Ljava/util/Comparator; @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@14 ; fresh java.util.stream.ReferencePipeline$Head ; call $1 java.util.Spliterator#getExactSizeIfKnown()J @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@20 @ java.util.stream.AbstractPipeline#copyIntoWithCancel(Ljava/util/stream/Sink;Ljava/util/Spliterator;)Z@19 ; call $1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@32 ; call $1 java.util.Spliterator#tryAdvance(Ljava/util/function/Consumer;)Z S @ java.util.stream.ReferencePipeline#forEachWithCancel(Ljava/util/Spliterator;Ljava/util/stream/Sink;)Z@13 ; store R <elem> S",
                    "java.util.Collection#parallelStream()Ljava/util/stream/Stream; : call 0 java.util.Collection#spliterator()Ljava/util/Spliterator; -> $1 @ java.util.Collection#parallelStream()Ljava/util/stream/Stream;@1 ; call $1 java.util.Spliterator#characteristics()I @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@1 ; call $1 java.util.Spliterator#getComparator()Ljava/util/Comparator; @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@14 ; fresh java.util.stream.ReferencePipeline$Head ; call $1 java.util.Spliterator#getExactSizeIfKnown()J @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@20 @ java.util.stream.AbstractPipeline#copyIntoWithCancel(Ljava/util/stream/Sink;Ljava/util/Spliterator;)Z@19 ; call $1 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@32 ; call $1 java.util.Spliterator#tryAdvance(Ljava/util/function/Consumer;)Z S @ java.util.stream.ReferencePipeline#forEachWithCancel(Ljava/util/Spliterator;Ljava/util/stream/Sink;)Z@13 ; store R <elem> S",
                    "java.util.stream.StreamSupport#stream(Ljava/util/Spliterator;Z)Ljava/util/stream/Stream; : call 0 java.util.Spliterator#characteristics()I @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@1 ; call 0 java.util.Spliterator#getComparator()Ljava/util/Comparator; @ java.util.stream.StreamOpFlag#fromCharacteristics(Ljava/util/Spliterator;)I@14 ; fresh java.util.stream.ReferencePipeline$Head ; call 0 java.util.Spliterator#getExactSizeIfKnown()J @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@20 @ java.util.stream.AbstractPipeline#copyIntoWithCancel(Ljava/util/stream/Sink;Ljava/util/Spliterator;)Z@19 ; call 0 java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V S @ java.util.stream.AbstractPipeline#copyInto(Ljava/util/stream/Sink;Ljava/util/Spliterator;)V@32 ; call 0 java.util.Spliterator#tryAdvance(Ljava/util/function/Consumer;)Z S @ java.util.stream.ReferencePipeline#forEachWithCancel(Ljava/util/Spliterator;Ljava/util/stream/Sink;)Z@13 ; store R <elem> S",
                    // Arrays.java stream(T[], int, int) = StreamSupport.stream(spliterator(array, s, e), false): the ArraySpliterator's elements
                    "java.util.Arrays#stream([Ljava/lang/Object;)Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head ; store R <elem> 0.[]",
                    "java.util.Arrays#stream([Ljava/lang/Object;II)Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head ; store R <elem> 0.[]",
                    // Stream.java: of(t) = StreamSupport.stream(new Streams.StreamBuilderImpl<>(t), false); of(T...) = Arrays.stream(values)
                    "java.util.stream.Stream#of(Ljava/lang/Object;)Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head ; store R <elem> 0",
                    "java.util.stream.Stream#of([Ljava/lang/Object;)Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head ; store R <elem> 0.[]",
                    "java.util.stream.Stream#ofNullable(Ljava/lang/Object;)Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head ; store R <elem> 0",
                    "java.util.stream.Stream#empty()Ljava/util/stream/Stream; : fresh java.util.stream.ReferencePipeline$Head",
                    // ---- stateless stages (ReferencePipeline.java: each an anonymous StatelessOp whose sink runs the callback per element)
                    "java.util.stream.ReferencePipeline#filter(Ljava/util/function/Predicate;)Ljava/util/stream/Stream; : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.stream.ReferencePipeline$2$1#accept(Ljava/lang/Object;)V@5 ; fresh java.util.stream.ReferencePipeline$2 ; store R <elem> 0.<elem>",
                    "java.util.stream.ReferencePipeline#map(Ljava/util/function/Function;)Ljava/util/stream/Stream; : call 1 java.util.function.Function#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.<elem> -> $1 @ java.util.stream.ReferencePipeline$3$1#accept(Ljava/lang/Object;)V@9 ; fresh java.util.stream.ReferencePipeline$3 ; store R <elem> $1",
                    "java.util.stream.ReferencePipeline#peek(Ljava/util/function/Consumer;)Ljava/util/stream/Stream; : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.stream.ReferencePipeline$15$1#accept(Ljava/lang/Object;)V@5 ; fresh java.util.stream.ReferencePipeline$15 ; store R <elem> 0.<elem>",
                    // flatMap: `try (Stream result = mapper.apply(u)) { result.sequential().forEach(downstream) }` (its allMatch with a lambda
                    // over the same elements when short-circuiting)
                    "java.util.stream.ReferencePipeline#flatMap(Ljava/util/function/Function;)Ljava/util/stream/Stream; : call 1 java.util.function.Function#apply(Ljava/lang/Object;)Ljava/lang/Object; 0.<elem> -> $1 @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@5 ; call $1 java.util.stream.Stream#sequential()Ljava/util/stream/BaseStream; -> $2 @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@26 @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@45 ; call $2 java.util.stream.Stream#forEach(Ljava/util/function/Consumer;)V S @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@57 ; call $1 java.util.stream.Stream#close()V @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@67 @ java.util.stream.ReferencePipeline$7$1FlatMap#accept(Ljava/lang/Object;)V@81 ; fresh java.util.stream.ReferencePipeline$7 ; store R <elem> S",
                    "java.util.stream.ReferencePipeline#unordered()Ljava/util/stream/Stream; : alias 0 ; fresh java.util.stream.ReferencePipeline$1 ; store R <elem> 0.<elem>",
                    "java.util.stream.ReferencePipeline#limit(J)Ljava/util/stream/Stream; : fresh java.util.stream.SliceOps$1 ; store R <elem> 0.<elem>",
                    "java.util.stream.ReferencePipeline#skip(J)Ljava/util/stream/Stream; : alias 0 ; fresh java.util.stream.SliceOps$1 ; store R <elem> 0.<elem>",
                    "java.util.stream.AbstractPipeline#sequential()Ljava/util/stream/BaseStream; : alias 0",
                    "java.util.stream.AbstractPipeline#parallel()Ljava/util/stream/BaseStream; : alias 0",
                    "java.util.stream.AbstractPipeline#isParallel()Z : observe 0",
                    "java.util.stream.AbstractPipeline#close()V : observe 0",
                    // ---- views of a stage: spliterator() (AbstractPipeline.java: a WrappingSpliterator over the stage), iterator()
                    // (ReferencePipeline.java `Spliterators.iterator(spliterator())`: the adapter, F3)
                    "java.util.stream.AbstractPipeline#spliterator()Ljava/util/Spliterator; : fresh java.util.stream.StreamSpliterators$WrappingSpliterator ; store R java.util.stream.StreamSpliterators$AbstractWrappingSpliterator.ph 0",
                    "java.util.stream.ReferencePipeline#iterator()Ljava/util/Iterator; : call 0 java.util.stream.AbstractPipeline#spliterator()Ljava/util/Spliterator; -> $1 @ java.util.stream.ReferencePipeline#iterator()Ljava/util/Iterator;@1 ; fresh java.util.Spliterators$1Adapter ; store R java.util.Spliterators$1Adapter.val$spliterator $1",
                    "java.util.stream.StreamSpliterators$WrappingSpliterator#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.stream.StreamSpliterators$AbstractWrappingSpliterator.ph/<elem> @ java.util.stream.StreamSpliterators$WrappingSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@29",
                    "java.util.stream.StreamSpliterators$WrappingSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.stream.StreamSpliterators$AbstractWrappingSpliterator.ph/<elem> @ java.util.stream.StreamSpliterators$WrappingSpliterator#tryAdvance(Ljava/util/function/Consumer;)Z@29",
                    "java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#trySplit()Ljava/util/Spliterator; : fresh java.util.stream.StreamSpliterators$WrappingSpliterator ; store R java.util.stream.StreamSpliterators$AbstractWrappingSpliterator.ph 0.java.util.stream.StreamSpliterators$AbstractWrappingSpliterator.ph",
                    "java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#estimateSize()J : observe 0",
                    "java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#getExactSizeIfKnown()J : observe 0",
                    "java.util.stream.StreamSpliterators$AbstractWrappingSpliterator#characteristics()I : observe 0",
                    // the adapter (Spliterators.java iterator(Spliterator): a local class that is its spliterator's consumer: `accept(t)` sets
                    // `nextElement`, the sink S here), over any spliterator (a stage's WrappingSpliterator, a user's: the IR refuses at the sink)
                    "java.util.Spliterators#iterator(Ljava/util/Spliterator;)Ljava/util/Iterator; : fresh java.util.Spliterators$1Adapter ; store R java.util.Spliterators$1Adapter.val$spliterator 0",
                    "java.util.Spliterators$1Adapter#<init>(Ljava/util/Spliterator;)V : store 0 java.util.Spliterators$1Adapter.val$spliterator 1",
                    "java.util.Spliterators$1Adapter#accept(Ljava/lang/Object;)V : store 0 java.util.Spliterators$1Adapter.nextElement 1",
                    "java.util.Spliterators$1Adapter#hasNext()Z : call 0.java.util.Spliterators$1Adapter.val$spliterator java.util.Spliterator#tryAdvance(Ljava/util/function/Consumer;)Z S @ java.util.Spliterators$1Adapter#hasNext()Z@12 ; store 0 java.util.Spliterators$1Adapter.nextElement S",
                    "java.util.Spliterators$1Adapter#next()Ljava/lang/Object; : call 0 java.util.Spliterators$1Adapter#hasNext()Z @ java.util.Spliterators$1Adapter#next()Ljava/lang/Object;@8 ; load 0 java.util.Spliterators$1Adapter.nextElement",
                    "java.util.Spliterators$1Adapter#forEachRemaining(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.java.util.Spliterators$1Adapter.nextElement @ java.util.Spliterators$1Adapter#forEachRemaining(Ljava/util/function/Consumer;)V@29 ; call 0.java.util.Spliterators$1Adapter.val$spliterator java.util.Spliterator#forEachRemaining(Ljava/util/function/Consumer;)V 1 @ java.util.Spliterators$1Adapter#forEachRemaining(Ljava/util/function/Consumer;)V@39",
                    // ---- terminals (ForEachOps / ReduceOps / MatchOps / FindOps: the sinks' per-element callbacks)
                    "java.util.stream.ReferencePipeline#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.stream.ForEachOps$ForEachOp$OfRef#accept(Ljava/lang/Object;)V@5",
                    "java.util.stream.ReferencePipeline#forEachOrdered(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.stream.ForEachOps$ForEachOp$OfRef#accept(Ljava/lang/Object;)V@5",
                    "java.util.stream.ReferencePipeline$Head#forEach(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.stream.ForEachOps$ForEachOp$OfRef#accept(Ljava/lang/Object;)V@5",
                    "java.util.stream.ReferencePipeline$Head#forEachOrdered(Ljava/util/function/Consumer;)V : call 1 java.util.function.Consumer#accept(Ljava/lang/Object;)V 0.<elem> @ java.util.stream.ForEachOps$ForEachOp$OfRef#accept(Ljava/lang/Object;)V@5",
                    // collect(Collector) (ReferencePipeline.java collect; ReduceOps.makeRef(Collector) and its ReducingSink $3; the op's
                    // getOpFlags reads the characteristics too: a site the lazy premise found). The container state is a fresh box $7
                    // (as reduce's): the sink's `state` holds the supplier's result and every combiner result (ReducingSink.combine:
                    // state = combiner.apply(state, other.state), a parallel reduction's tree combines combined states), so the
                    // accumulator, the combiner and the finisher receive either (the lazy premise found the combiner-result flow)
                    "java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object; : call 1 java.util.stream.Collector#characteristics()Ljava/util/Set; -> $8 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@8 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@32 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@91 @ java.util.stream.ReduceOps$3#getOpFlags()I@4" +
                                    " ; call $8 java.util.Set#contains(Ljava/lang/Object;)Z _ @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@16 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@40 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@99 @ java.util.stream.ReduceOps$3#getOpFlags()I@12" +
                                    " ; call 1 java.util.stream.Collector#supplier()Ljava/util/function/Supplier; -> $1 @ java.util.stream.ReduceOps#makeRef(Ljava/util/stream/Collector;)Ljava/util/stream/TerminalOp;@7 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@49" +
                                    " ; call $1 java.util.function.Supplier#get()Ljava/lang/Object; -> $2 @ java.util.stream.ReduceOps$3ReducingSink#begin(J)V@5 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@54" +
                                    " ; fresh java.lang.Object -> $7 ; store $7 <elem> $2" +
                                    " ; call 1 java.util.stream.Collector#accumulator()Ljava/util/function/BiConsumer; -> $3 @ java.util.stream.ReduceOps#makeRef(Ljava/util/stream/Collector;)Ljava/util/stream/TerminalOp;@14 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@61" +
                                    " ; call $3 java.util.function.BiConsumer#accept(Ljava/lang/Object;Ljava/lang/Object;)V $7.<elem> 0.<elem> @ java.util.stream.ReduceOps$3ReducingSink#accept(Ljava/lang/Object;)V@9 @ java.util.stream.ReferencePipeline#lambda$collect$0(Ljava/util/function/BiConsumer;Ljava/lang/Object;Ljava/lang/Object;)V@3" +
                                    " ; call 1 java.util.stream.Collector#combiner()Ljava/util/function/BinaryOperator; -> $4 @ java.util.stream.ReduceOps#makeRef(Ljava/util/stream/Collector;)Ljava/util/stream/TerminalOp;@21" +
                                    " ; call $4 java.util.function.BinaryOperator#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $7.<elem> $7.<elem> -> $5 @ java.util.stream.ReduceOps$3ReducingSink#combine(Ljava/util/stream/ReduceOps$3ReducingSink;)V@13" +
                                    " ; store $7 <elem> $5" +
                                    " ; call 1 java.util.stream.Collector#finisher()Ljava/util/function/Function; -> $6 @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@112" +
                                    " ; call $6 java.util.function.Function#apply(Ljava/lang/Object;)Ljava/lang/Object; $7.<elem> -> result @ java.util.stream.ReferencePipeline#collect(Ljava/util/stream/Collector;)Ljava/lang/Object;@118 ; alias $7.<elem>",
                    "java.util.stream.ReferencePipeline#collect(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BiConsumer;)Ljava/lang/Object; : call 1 java.util.function.Supplier#get()Ljava/lang/Object; -> $1 @ java.util.stream.ReduceOps$4ReducingSink#begin(J)V@5" +
                                    " ; call 2 java.util.function.BiConsumer#accept(Ljava/lang/Object;Ljava/lang/Object;)V $1 0.<elem> @ java.util.stream.ReduceOps$4ReducingSink#accept(Ljava/lang/Object;)V@9" +
                                    " ; call 3 java.util.function.BiConsumer#accept(Ljava/lang/Object;Ljava/lang/Object;)V $1 $1 @ java.util.stream.ReduceOps$4ReducingSink#combine(Ljava/util/stream/ReduceOps$4ReducingSink;)V@12 ; alias $1",
                    "java.util.stream.ReferencePipeline#toArray()[Ljava/lang/Object; : fresh [Ljava.lang.Object; ; store R [] 0.<elem>",
                    "java.util.stream.ReferencePipeline#toArray(Ljava/util/function/IntFunction;)[Ljava/lang/Object; : call 1 java.util.function.IntFunction#apply(I)Ljava/lang/Object; _ -> $1 @ java.util.stream.Nodes#flatten(Ljava/util/stream/Node;Ljava/util/function/IntFunction;)Ljava/util/stream/Node;@37 ; store $1 [] 0.<elem> ; alias $1",
                    // toList(): listFromTrustedArrayNullsAllowed(toArray()): a ListN over the array, or a List12 of its elements
                    "java.util.stream.ReferencePipeline#toList()Ljava/util/List; : fresh [Ljava.lang.Object; -> $1 ; store $1 [] 0.<elem> ; fresh java.util.ImmutableCollections$ListN -> $2 ; store $2 java.util.ImmutableCollections$ListN.elements $1" +
                                    " ; fresh java.util.ImmutableCollections$List12 -> $3 ; store $3 java.util.ImmutableCollections$List12.e0 $1.[] ; store $3 java.util.ImmutableCollections$List12.e1 $1.[] ; alias $2 ; alias $3",
                    "java.util.stream.ReferencePipeline#anyMatch(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.stream.MatchOps$1MatchSink#accept(Ljava/lang/Object;)V@12",
                    "java.util.stream.ReferencePipeline#allMatch(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.stream.MatchOps$1MatchSink#accept(Ljava/lang/Object;)V@12",
                    "java.util.stream.ReferencePipeline#noneMatch(Ljava/util/function/Predicate;)Z : call 1 java.util.function.Predicate#test(Ljava/lang/Object;)Z 0.<elem> @ java.util.stream.MatchOps$1MatchSink#accept(Ljava/lang/Object;)V@12",
                    "java.util.stream.ReferencePipeline#findFirst()Ljava/util/Optional; : fresh java.util.Optional ; store R java.util.Optional.value 0.<elem>",
                    "java.util.stream.ReferencePipeline#findAny()Ljava/util/Optional; : fresh java.util.Optional ; store R java.util.Optional.value 0.<elem>",
                    "java.util.stream.ReferencePipeline#count()J : observe 0",
                    // reduce: the accumulated state lives in a fresh box (a named intermediate value) whose slot holds the identity and every result
                    "java.util.stream.ReferencePipeline#reduce(Ljava/lang/Object;Ljava/util/function/BinaryOperator;)Ljava/lang/Object; : fresh java.lang.Object -> $1 ; store $1 <elem> 1" +
                                    " ; call 2 java.util.function.BiFunction#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $1.<elem> 0.<elem> -> $2 @ java.util.stream.ReduceOps$1ReducingSink#accept(Ljava/lang/Object;)V@10" +
                                    " ; call 2 java.util.function.BinaryOperator#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $1.<elem> $1.<elem> -> $3 @ java.util.stream.ReduceOps$1ReducingSink#combine(Ljava/util/stream/ReduceOps$1ReducingSink;)V@13" +
                                    " ; store $1 <elem> $2 ; store $1 <elem> $3 ; alias $1.<elem>",
                    "java.util.stream.ReferencePipeline#reduce(Ljava/lang/Object;Ljava/util/function/BiFunction;Ljava/util/function/BinaryOperator;)Ljava/lang/Object; : fresh java.lang.Object -> $1 ; store $1 <elem> 1" +
                                    " ; call 2 java.util.function.BiFunction#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $1.<elem> 0.<elem> -> $2 @ java.util.stream.ReduceOps$1ReducingSink#accept(Ljava/lang/Object;)V@10" +
                                    " ; call 3 java.util.function.BinaryOperator#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $1.<elem> $1.<elem> -> $3 @ java.util.stream.ReduceOps$1ReducingSink#combine(Ljava/util/stream/ReduceOps$1ReducingSink;)V@13" +
                                    " ; store $1 <elem> $2 ; store $1 <elem> $3 ; alias $1.<elem>",
                    "java.util.stream.ReferencePipeline#reduce(Ljava/util/function/BinaryOperator;)Ljava/util/Optional; : fresh java.lang.Object -> $1 ; store $1 <elem> 0.<elem>" +
                                    " ; call 1 java.util.function.BinaryOperator#apply(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object; $1.<elem> $1.<elem> -> $2 @ java.util.stream.ReduceOps$2ReducingSink#accept(Ljava/lang/Object;)V@30" +
                                    " ; store $1 <elem> $2 ; fresh java.util.Optional ; store R java.util.Optional.value $1.<elem>",
                    "java.util.stream.ReferencePipeline#min(Ljava/util/Comparator;)Ljava/util/Optional; : call 1 java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 0.<elem> 0.<elem> @ java.util.function.BinaryOperator#lambda$minBy$0(Ljava/util/Comparator;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;@3 ; fresh java.util.Optional ; store R java.util.Optional.value 0.<elem>",
                    "java.util.stream.ReferencePipeline#max(Ljava/util/Comparator;)Ljava/util/Optional; : call 1 java.util.Comparator#compare(Ljava/lang/Object;Ljava/lang/Object;)I 0.<elem> 0.<elem> @ java.util.function.BinaryOperator#lambda$maxBy$0(Ljava/util/Comparator;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;@3 ; fresh java.util.Optional ; store R java.util.Optional.value 0.<elem>"),
                    Set.of("java.util.stream."), Set.of("java.util.stream.Collector"));

    /** The tree-bin class checks of the hash maps (jdk:java/util/HashMap.java comparableClassFor, compareComparables, TreeNode.tieBreakOrder). */
    static final Set<String> TREE_BIN_CLASS_CHECKS = Set.of(
                    "java.util.HashMap#comparableClassFor(Ljava/lang/Object;)Ljava/lang/Class;@8",
                    "java.util.HashMap#compareComparables(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;)I@5",
                    "java.util.HashMap$TreeNode#tieBreakOrder(Ljava/lang/Object;Ljava/lang/Object;)I@9",
                    "java.util.HashMap$TreeNode#tieBreakOrder(Ljava/lang/Object;Ljava/lang/Object;)I@16");

    /** The tree bin's guarded {@code k.compareTo(x)} (jdk:java/util/HashMap.java compareComparables). */
    static final Set<String> TREE_BIN_SAME_CLASS_CALLBACKS = Set.of("java.util.HashMap#compareComparables(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;)I@21");

    /**
     * F2, maps and sets: the hash maps ({@code HashMap}, {@code LinkedHashMap}) as storage over two slots, {@code <keys>}
     * and {@code <vals>}, for their node representation (the {@code table} array, each node's {@code key} /
     * {@code value}, the {@code next} and tree-bin links, LinkedHashMap's order links, the iterators' / spliterators'
     * links). A node handed to user code (an {@code entrySet()} entry, the eldest entry of {@code removeEldestEntry}) is a
     * fresh {@code HashMap$Node} whose slot {@code <map>} is the map. The key protocol is the JDK's, at its real sites:
     * {@code k.hashCode()} ({@code HashMap.hash}), {@code k.equals(k')} against the stored keys (both directions where
     * the JDK compares two stored keys), and on a tree bin {@code comparableClassFor(k)} (a class check: a String key's
     * {@code getClass()} usage), {@code compareComparables} ({@code k.compareTo(k')}) and {@code tieBreakOrder} (class
     * checks). The hash sets are wrappers over their real field {@code map} (every operation a callback on it, as F3),
     * whose constructors make a fresh map. Views ({@code keySet}, {@code values}, {@code entrySet}), their iterators and
     * spliterators are fresh views over the map; the view caches hold fresh views only (premise data). Not modelled
     * (refused by name): {@code clone}, serialization, {@code LinkedHashMap}'s reversed views, the tree bins' internals
     * beyond their callback sites. JDK citations: jdk:java/util/HashMap.java, LinkedHashMap.java, HashSet.java.
     */
    static final Family F2 = repInsensitiveClassChecks(premise(new Family("f2", true,
                    Set.of("java.util.HashMap", "java.util.HashMap$Node", "java.util.HashMap$TreeNode", "java.util.HashMap$KeySet", "java.util.HashMap$Values", "java.util.HashMap$EntrySet",
                                    "java.util.HashMap$HashIterator", "java.util.HashMap$KeyIterator", "java.util.HashMap$ValueIterator", "java.util.HashMap$EntryIterator",
                                    "java.util.HashMap$HashMapSpliterator", "java.util.HashMap$KeySpliterator", "java.util.HashMap$ValueSpliterator", "java.util.HashMap$EntrySpliterator",
                                    "java.util.LinkedHashMap", "java.util.LinkedHashMap$Entry", "java.util.LinkedHashMap$LinkedKeySet", "java.util.LinkedHashMap$LinkedValues",
                                    "java.util.LinkedHashMap$LinkedEntrySet", "java.util.LinkedHashMap$LinkedHashIterator", "java.util.LinkedHashMap$LinkedKeyIterator",
                                    "java.util.LinkedHashMap$LinkedValueIterator", "java.util.LinkedHashMap$LinkedEntryIterator",
                                    // the sorted map (its navigable sub-map views are open: their IR calls TreeMap's unlisted methods, refused by name)
                                    "java.util.TreeMap", "java.util.TreeMap$Entry", "java.util.TreeMap$Values", "java.util.TreeMap$EntrySet",
                                    "java.util.TreeMap$PrivateEntryIterator", "java.util.TreeMap$EntryIterator", "java.util.TreeMap$ValueIterator", "java.util.TreeMap$KeyIterator",
                                    "java.util.TreeMap$DescendingKeyIterator", "java.util.TreeMap$TreeMapSpliterator", "java.util.TreeMap$KeySpliterator", "java.util.TreeMap$ValueSpliterator",
                                    "java.util.TreeMap$EntrySpliterator", "java.util.TreeMap$DescendingKeySpliterator"),
                    Map.ofEntries(Map.entry("java.util.HashMap.table", "-"), Map.entry("java.util.HashMap$Node.key", "<keys>"), Map.entry("java.util.HashMap$Node.value", "<vals>"),
                                    Map.entry("java.util.HashMap$Node.next", "-"), Map.entry("java.util.HashMap$TreeNode.parent", "-"), Map.entry("java.util.HashMap$TreeNode.left", "-"),
                                    Map.entry("java.util.HashMap$TreeNode.right", "-"), Map.entry("java.util.HashMap$TreeNode.prev", "-"), Map.entry("java.util.LinkedHashMap.head", "-"),
                                    Map.entry("java.util.LinkedHashMap.tail", "-"), Map.entry("java.util.LinkedHashMap$Entry.before", "-"), Map.entry("java.util.LinkedHashMap$Entry.after", "-"),
                                    Map.entry("java.util.HashMap$HashIterator.next", "-@java.util.HashMap$HashIterator.this$0"),
                                    Map.entry("java.util.HashMap$HashIterator.current", "-@java.util.HashMap$HashIterator.this$0"),
                                    Map.entry("java.util.LinkedHashMap$LinkedHashIterator.next", "-@java.util.LinkedHashMap$LinkedHashIterator.this$0"),
                                    Map.entry("java.util.LinkedHashMap$LinkedHashIterator.current", "-@java.util.LinkedHashMap$LinkedHashIterator.this$0"),
                                    Map.entry("java.util.HashMap$HashMapSpliterator.current", "-@java.util.HashMap$HashMapSpliterator.map"),
                                    Map.entry("java.util.TreeMap.root", "-"), Map.entry("java.util.TreeMap$Entry.key", "<keys>"), Map.entry("java.util.TreeMap$Entry.value", "<vals>"),
                                    Map.entry("java.util.TreeMap$Entry.left", "-"), Map.entry("java.util.TreeMap$Entry.right", "-"), Map.entry("java.util.TreeMap$Entry.parent", "-"),
                                    Map.entry("java.util.TreeMap$PrivateEntryIterator.next", "-@java.util.TreeMap$PrivateEntryIterator.this$0"),
                                    Map.entry("java.util.TreeMap$PrivateEntryIterator.lastReturned", "-@java.util.TreeMap$PrivateEntryIterator.this$0"),
                                    Map.entry("java.util.TreeMap$TreeMapSpliterator.current", "-@java.util.TreeMap$TreeMapSpliterator.tree"),
                                    Map.entry("java.util.TreeMap$TreeMapSpliterator.fence", "-@java.util.TreeMap$TreeMapSpliterator.tree")),
                    Set.of(), Set.of(), Set.of(),
                    JdkModelsF2.TABLE),
                    Map.of("java.util.HashMap", "java.util.HashMap$Node", "java.util.TreeMap", "java.util.TreeMap$Entry"),
                    Set.of("java.util.AbstractMap.keySet", "java.util.AbstractMap.values", "java.util.HashMap.entrySet", "java.util.TreeMap.entrySet", "java.util.TreeMap.navigableKeySet",
                                    "java.util.TreeMap.descendingMap")),
                    TREE_BIN_CLASS_CHECKS, TREE_BIN_SAME_CLASS_CALLBACKS);

    /** The sites of the BufferedWriter path every PrintStream print takes ({@code textOut.write(s)}: Writer.write(String) -> write(String,II)). */
    private static final String PS_LENGTH = " ; call $1 java.lang.String#length()I @ java.io.Writer#write(Ljava/lang/String;)V@4";
    private static final String PS_CHARS = " ; call $1 java.lang.String#getChars(II[CI)V _ _ _ _ @ java.io.BufferedWriter#write(Ljava/lang/String;II)V@68";
    private static final String VALUE_OF = "java.lang.String#valueOf(Ljava/lang/Object;)Ljava/lang/String;";

    /**
     * F6, string sinks: the string is an argument that the JDK code reads and never stores. Each entry states the usages
     * the JDK code makes of it at their real sites (callbacks on the string: the walk's terminal usages) and the calls
     * that pass it on (re-dispatch: a subclass override receives it). {@code PrintStream.print/println}:
     * {@code String.valueOf(x)} (a static callback: its Phase-A parameter usage, then its model / IR), then the exact
     * class's path ({@code textOut}, always a {@code BufferedWriter}: {@code length()} in {@code Writer.write(String)},
     * {@code getChars} in {@code BufferedWriter.write(String,int,int)}, {@code indexOf('\n')} on the {@code print} path)
     * and the subclass path ({@code getClass() != PrintStream.class}: {@code print(x)} re-dispatched): both branches,
     * since the class test is not evaluated. The receiver slot is the IR's ({@code ir 0}). Open classes, except the
     * collectors' record {@code Collectors$CollectorImpl} (closed: its {@code equals/hashCode/toString} read the fields
     * through {@code ObjectMethods} and refuse by name): its constructors store and its accessors load five slots instead
     * of the reflection-registered fields, so every JDK collector and {@code Collector.of} reach F4's
     * {@code collect(Collector)} callbacks with their real functions. Not modelled (walked as IR): {@code printf/format},
     * {@code PrintStream} {@code append}/{@code write(char[])}, the number producers, {@code StringBuilder}'s own wrappers
     * (their {@code super} calls are the modelled {@code AbstractStringBuilder} ones), {@code append(CharSequence)}/
     * {@code insert}, {@code StringJoiner}, {@code String.join}. JDK citations: jdk:java/io/, jdk:java/lang/String.java.
     */
    static final Family F6 = sinks(new Family("f6", true, Set.of("java.util.stream.Collectors$CollectorImpl"), Map.of(),
                    // ---- PrintStream (PrintStream.java:837-1035): print = write(String.valueOf(s)); println = writeln(String.valueOf(x)) on the
                    // exact class, else print(x) + newLine() (the subclass path, re-dispatched)
                    "java.io.PrintStream#print(Ljava/lang/String;)V : ir 0 ; call 1 " + VALUE_OF + " -> $1 @ java.io.PrintStream#print(Ljava/lang/String;)V@2" +
                                    " ; call $1 java.lang.String#indexOf(I)I _ @ java.io.PrintStream#write(Ljava/lang/String;)V@40" + PS_LENGTH + PS_CHARS,
                    "java.io.PrintStream#print(Ljava/lang/Object;)V : ir 0 ; call 1 " + VALUE_OF + " -> $1 @ java.io.PrintStream#print(Ljava/lang/Object;)V@2" +
                                    " ; call $1 java.lang.String#indexOf(I)I _ @ java.io.PrintStream#write(Ljava/lang/String;)V@40" + PS_LENGTH + PS_CHARS,
                    "java.io.PrintStream#println(Ljava/lang/String;)V : ir 0 ; call 1 " + VALUE_OF + " -> $1 @ java.io.PrintStream#println(Ljava/lang/String;)V@11" + PS_LENGTH + PS_CHARS +
                                    " ; call 0 java.io.PrintStream#print(Ljava/lang/String;)V 1 @ java.io.PrintStream#println(Ljava/lang/String;)V@26",
                    "java.io.PrintStream#println(Ljava/lang/Object;)V : ir 0 ; call 1 " + VALUE_OF + " -> $2 @ java.io.PrintStream#println(Ljava/lang/Object;)V@1 ; call $2 " + VALUE_OF +
                                    " -> $1 @ java.io.PrintStream#println(Ljava/lang/Object;)V@16" + PS_LENGTH + PS_CHARS +
                                    " ; call 0 java.io.PrintStream#print(Ljava/lang/String;)V $2 @ java.io.PrintStream#println(Ljava/lang/Object;)V@31",
                    // ---- PrintWriter (PrintWriter.java): print = write(String.valueOf(s)) (public: re-dispatched), println = print(x) + println();
                    // write(String) = write(s, 0, s.length()) (re-dispatched; PrintWriter's own is out.write(s, off, len): the IR)
                    "java.io.PrintWriter#print(Ljava/lang/String;)V : ir 0 ; call 1 " + VALUE_OF +
                                    " -> $1 @ java.io.PrintWriter#print(Ljava/lang/String;)V@2 ; call 0 java.io.PrintWriter#write(Ljava/lang/String;)V $1 @ java.io.PrintWriter#print(Ljava/lang/String;)V@5",
                    "java.io.PrintWriter#print(Ljava/lang/Object;)V : ir 0 ; call 1 " + VALUE_OF +
                                    " -> $1 @ java.io.PrintWriter#print(Ljava/lang/Object;)V@2 ; call 0 java.io.PrintWriter#write(Ljava/lang/String;)V $1 @ java.io.PrintWriter#print(Ljava/lang/Object;)V@5",
                    "java.io.PrintWriter#println(Ljava/lang/String;)V : ir 0 ; call 0 java.io.PrintWriter#print(Ljava/lang/String;)V 1 @ java.io.PrintWriter#println(Ljava/lang/String;)V@9",
                    "java.io.PrintWriter#println(Ljava/lang/Object;)V : ir 0 ; call 1 " + VALUE_OF +
                                    " -> $1 @ java.io.PrintWriter#println(Ljava/lang/Object;)V@1 ; call 0 java.io.PrintWriter#print(Ljava/lang/String;)V $1 @ java.io.PrintWriter#println(Ljava/lang/Object;)V@14",
                    "java.io.PrintWriter#write(Ljava/lang/String;)V : ir 0 ; call 1 java.lang.String#length()I @ java.io.PrintWriter#write(Ljava/lang/String;)V@4 ; call 0 java.io.PrintWriter#write(Ljava/lang/String;II)V 1 _ _ @ java.io.PrintWriter#write(Ljava/lang/String;)V@7",
                    // ---- Writer (Writer.java:247-249, 322-325), BufferedWriter (BufferedWriter.java:271-284)
                    "java.io.Writer#write(Ljava/lang/String;)V : ir 0 ; call 1 java.lang.String#length()I @ java.io.Writer#write(Ljava/lang/String;)V@4 ; call 0 java.io.Writer#write(Ljava/lang/String;II)V 1 _ _ @ java.io.Writer#write(Ljava/lang/String;)V@7",
                    "java.io.Writer#append(Ljava/lang/CharSequence;)Ljava/io/Writer; : ir 0 ; call 1 " + VALUE_OF +
                                    " -> $1 @ java.io.Writer#append(Ljava/lang/CharSequence;)Ljava/io/Writer;@2 ; call 0 java.io.Writer#write(Ljava/lang/String;)V $1 @ java.io.Writer#append(Ljava/lang/CharSequence;)Ljava/io/Writer;@5 ; alias 0",
                    "java.io.BufferedWriter#write(Ljava/lang/String;II)V : ir 0 ; call 1 java.lang.String#getChars(II[CI)V _ _ _ _ @ java.io.BufferedWriter#write(Ljava/lang/String;II)V@68",
                    // ---- String.valueOf(Object) (String.java:4900-4901 `obj == null ? "null" : obj.toString()`; the literal is the IR's)
                    VALUE_OF + " : call 0 java.lang.Object#toString()Ljava/lang/String; -> result @ " + VALUE_OF + "@11 ; result ir",
                    // ---- AbstractStringBuilder.append(String) (the string as the argument; the builder is the IR's: StringBuilder.append(String) is
                    // `super.append(str); return this`, walked as IR, whose super call is this entry): length, coder, getBytes into the builder's array
                    "java.lang.AbstractStringBuilder#append(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder; : ir 0 ; call 1 java.lang.String#length()I @ java.lang.AbstractStringBuilder#append(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder;@26" +
                                    " ; call 1 java.lang.String#coder()B @ java.lang.AbstractStringBuilder#append(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder;@33" +
                                    " ; call 1 java.lang.String#getBytes([BIB)V _ _ _ @ java.lang.AbstractStringBuilder#append(Ljava/lang/String;)Ljava/lang/AbstractStringBuilder;@87 ; result ir",
                    // ---- the collectors' record (Collectors.java:197-210): its components as slots
                    "java.util.stream.Collectors$CollectorImpl#<init>(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BinaryOperator;Ljava/util/function/Function;Ljava/util/Set;)V : store 0 <supplier> 1" +
                                    " ; store 0 <accumulator> 2 ; store 0 <combiner> 3 ; store 0 <finisher> 4 ; store 0 <characteristics> 5",
                    // the 4-argument constructor: `this(supplier, accumulator, combiner, castingIdentity(), characteristics)` (a static call, no argument)
                    "java.util.stream.Collectors$CollectorImpl#<init>(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BinaryOperator;Ljava/util/Set;)V : store 0 <supplier> 1" +
                                    " ; store 0 <accumulator> 2 ; store 0 <combiner> 3 ; call _ java.util.stream.Collectors#castingIdentity()Ljava/util/function/Function; -> $1 @ java.util.stream.Collectors$CollectorImpl" +
                                    "#<init>(Ljava/util/function/Supplier;Ljava/util/function/BiConsumer;Ljava/util/function/BinaryOperator;Ljava/util/Set;)V@4 ; store 0 <finisher> $1 ; store 0 <characteristics> 4",
                    "java.util.stream.Collectors$CollectorImpl#supplier()Ljava/util/function/Supplier; : load 0 <supplier>",
                    "java.util.stream.Collectors$CollectorImpl#accumulator()Ljava/util/function/BiConsumer; : load 0 <accumulator>",
                    "java.util.stream.Collectors$CollectorImpl#combiner()Ljava/util/function/BinaryOperator; : load 0 <combiner>",
                    "java.util.stream.Collectors$CollectorImpl#finisher()Ljava/util/function/Function; : load 0 <finisher>",
                    "java.util.stream.Collectors$CollectorImpl#characteristics()Ljava/util/Set; : load 0 <characteristics>"),
                    Map.of("java.io.PrintStream.textOut", "java.io.BufferedWriter", "java.io.PrintStream.charOut", "java.io.OutputStreamWriter"),
                    Map.of("java.util.stream.Collectors$CollectorImpl.supplier", "<supplier>", "java.util.stream.Collectors$CollectorImpl.accumulator", "<accumulator>",
                                    "java.util.stream.Collectors$CollectorImpl.combiner", "<combiner>", "java.util.stream.Collectors$CollectorImpl.finisher", "<finisher>",
                                    "java.util.stream.Collectors$CollectorImpl.characteristics", "<characteristics>"));

    private static Family sinks(Family f, Map<String, String> exactFields, Map<String, String> recordSlots) {
        f.stringSinks = true;
        f.exactFields = exactFields;
        f.recordSlots = recordSlots;
        return f;
    }

    /** Declares {@code sites} the representation-insensitive class checks of {@code f} (see {@link Family#repInsensitiveClassChecks}). */
    private static Family repInsensitiveClassChecks(Family f, Set<String> sites, Set<String> sameClassCallbacks) {
        f.repInsensitiveClassChecks = sites;
        f.sameClassCallbacks = sameClassCallbacks;
        return f;
    }

    private static Family premise(Family f, Map<String, String> entryClasses, Set<String> viewCaches) {
        f.entryClasses = entryClasses;
        f.viewCaches = viewCaches;
        f.explicitClassChecks = true;
        return f;
    }

    /** Marks {@code f} a lazy family that closes the class-name prefixes {@code closed} except {@code open}. */
    private static Family lazy(Family f, Set<String> closed, Set<String> open) {
        f.closedPrefixes = closed;
        f.openPrefixes = open;
        f.lazy = true;
        return f;
    }

    /** Every family (the census and the JUnit iterate this list). */
    static final List<Family> FAMILIES = List.of(F7, F1, F3, F2, F4, F6);

    static {
        validate(FAMILIES); // the cross-family parser rules
    }

    /** The family with id {@code id}, or null. */
    static Family family(String id) {
        for (Family f : FAMILIES) {
            if (f.id.equals(id)) {
                return f;
            }
        }
        return null;
    }

    static String methodId(ResolvedJavaMethod m) {
        return m.getDeclaringClass().toJavaName() + "#" + m.getName() + m.getSignature().toMethodDescriptor();
    }

    /** The op of a resolved method in an enabled family, or null (identity key: declaring class + name + descriptor). */
    static Op lookup(ResolvedJavaMethod m) {
        if (m == null) {
            return null;
        }
        String id;
        try {
            id = methodId(m);
        } catch (Throwable t) {
            return null;
        }
        for (Family f : FAMILIES) {
            if (f.enabled) {
                Op op = f.table.get(id);
                if (op != null) {
                    return op;
                }
            }
        }
        return null;
    }

    /** The enabled family whose closed class declares {@code m} (an unlisted method there refuses), or null. */
    static Family closedFamilyOf(ResolvedJavaMethod m) {
        if (m == null) {
            return null;
        }
        String cls;
        try {
            cls = m.getDeclaringClass().toJavaName();
        } catch (Throwable t) {
            cls = null; // fail closed (a name that cannot be derived refuses when any family closes a class)
        }
        for (Family f : FAMILIES) {
            if (f.enabled && (cls == null ? !f.closed.isEmpty() || !f.closedPrefixes.isEmpty() : closedBy(f, cls))) {
                return f;
            }
        }
        return null;
    }

    /** The enabled family that abstracts field {@code f}, or null. */
    static Family abstractingFamily(ResolvedJavaField f) {
        if (f == null) {
            return null;
        }
        String id;
        try {
            id = f.getDeclaringClass().toJavaName() + "." + f.getName();
        } catch (Throwable t) {
            id = null; // fail closed (a name that cannot be derived refuses when any family abstracts a field)
        }
        for (Family fam : FAMILIES) {
            if (fam.enabled && (id == null ? !fam.abstracted.isEmpty() : fam.abstracted.containsKey(id))) {
                return fam;
            }
        }
        return null;
    }

    /**
     * The enabled family whose record slots stand for field {@code f}, or null; a name that cannot be derived fails closed
     * when any family has record slots (as {@link #abstractingFamily}).
     */
    static Family recordFamily(ResolvedJavaField f) {
        if (f == null) {
            return null;
        }
        String id;
        try {
            id = f.getDeclaringClass().toJavaName() + "." + f.getName();
        } catch (Throwable t) {
            id = null;
        }
        for (Family fam : FAMILIES) {
            if (fam.enabled && (id == null ? !fam.recordSlots.isEmpty() : fam.recordSlots.containsKey(id))) {
                return fam;
            }
        }
        return null;
    }

    /** The slot that stands for the elements of the representation field {@code f} (null if {@code f} is not abstracted). */
    static Slot representationSlot(ResolvedJavaField f) {
        Family fam = abstractingFamily(f);
        try {
            String s = fam == null ? null : fam.abstracted.get(f.getDeclaringClass().toJavaName() + "." + f.getName());
            return arrayRepSlot(s);
        } catch (Throwable t) {
            return null; // no slot = the store stays a store of the field, which the field rule refuses
        }
    }

    /** Does {@code e} name argument slot {@code s} (as an operand's root: the slot it reads, a stored value or a callback argument)? */
    static boolean namesSlot(Effect e, int s) {
        for (Ref r : e.operands()) {
            if (r.slot() == s) {
                return true;
            }
        }
        return false;
    }

    /**
     * The model hook runs before the terminal rule, so an entry for a terminal target
     * ({@code StringAtoms.isTerminalTarget}: an instance method of a stringy-declared class) whose effects name the receiver
     * slot would replace a String receiver's terminal usage (an {@code observe 0} would drop it). Such an entry is
     * forbidden (pinned by JUnit); the engine does not apply it (the terminal rule keeps the usage). An entry that leaves slot 0 uncovered is sound: the slot
     * refuses by name.
     */
    static boolean hidesStringReceiver(Op op, boolean isStatic, boolean isConstructor, String declaringClass) {
        if (!StringAtoms.isTerminalTarget(isStatic, isConstructor, declaringClass)) {
            return false;
        }
        for (Effect e : op.effects) {
            if (namesSlot(e, 0) && !(e instanceof Ir)) {
                // `ir 0` is the IR for the receiver (no model applies to a terminal target's receiver at all)
                return true;
            }
        }
        return false;
    }

    /**
     * The classes some family (enabled or not) takes responsibility for: the declaring classes of its entries, its closed
     * classes and its templates. The implementor rule never applies to them (another family's knob decides about them).
     */
    static final Set<String> MENTIONED;

    /**
     * A method whose body the walk does not walk for a modelled value: an entry of some family (enabled or not), or a
     * method of a closed class. Its type checks of a modelled value are not observed (the premise checker treats a
     * non-exact {@code checkcast}/{@code instanceof} as a plain observation), so such a site gets no {@code TYPE_CHECK}
     * line. {@code methodId} = {@link #methodId}'s form.
     */
    static boolean modelBodyMethod(String cls, String methodId) {
        for (Family f : FAMILIES) {
            if (f.table.containsKey(methodId) || f.closed.contains(cls)) {
                return true;
            }
            for (String p : f.closedPrefixes) {
                if (cls.startsWith(p)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** A class some family takes responsibility for ({@link #MENTIONED}, or inside a family's closed prefix). */
    static boolean mentioned(String cls) {
        if (MENTIONED.contains(cls)) {
            return true;
        }
        for (Family f : FAMILIES) {
            for (String p : f.closedPrefixes) {
                if (cls.startsWith(p)) {
                    return true;
                }
            }
        }
        return false;
    }

    static {
        Set<String> m = new java.util.HashSet<>();
        for (Family f : FAMILIES) {
            for (String id : f.table.keySet()) {
                m.add(id.substring(0, id.indexOf('#')));
            }
            m.addAll(f.closed);
            m.addAll(f.templates);
        }
        MENTIONED = Collections.unmodifiableSet(m);
    }

    /** Some enabled family abstracts a field (else the field rule never applies: F7 alone). */
    static boolean anyAbstracted() {
        for (Family f : FAMILIES) {
            if (f.enabled && (!f.abstracted.isEmpty() || !f.recordSlots.isEmpty())) {
                return true; // record slots are under the field rule too
            }
        }
        return false;
    }

    static boolean anyEnabled() {
        for (Family f : FAMILIES) {
            if (f.enabled) {
                return true;
            }
        }
        return false;
    }

    static List<String> enabledIds() {
        List<String> out = new ArrayList<>();
        for (Family f : FAMILIES) {
            if (f.enabled) {
                out.add(f.id);
            }
        }
        return Collections.unmodifiableList(out);
    }
}
