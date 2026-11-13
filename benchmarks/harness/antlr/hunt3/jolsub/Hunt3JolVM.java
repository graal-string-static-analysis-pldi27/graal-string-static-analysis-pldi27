package hunt3.jolsub;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import sun.misc.Unsafe;

/**
 * C98 hunt3 batch4 (#29 ANTLR TimeLexerSpeed): jol-core 0.16 refuses to run on non-HotSpot VMs
 * ("Only HotSpot/OpenJDK VMs are supported", VM.current() probes java.vm.name). The upstream benchmark
 * main calls GraphLayout.parseInstance for its printed *footprint* lines. This VirtualMachine
 * implementation (returned by the Target_org_openjdk_jol_vm_VM substitution in native images only)
 * provides the small surface jol needs over sun.misc.Unsafe with a conservative x64 layout model
 * (12b object header, 16b array header, 8b alignment, compressed refs). It affects ONLY the printed
 * footprint sizes; the measured load/lex times in TimeLexerSpeed do not go through jol.
 */
public class Hunt3JolVM implements org.openjdk.jol.vm.VirtualMachine {
    public static final Hunt3JolVM INSTANCE = new Hunt3JolVM();
    private static final Unsafe U;
    static {
        Unsafe u = null;
        try {
            Field f = Unsafe.class.getDeclaredField("theUnsafe");
            f.setAccessible(true);
            u = (Unsafe) f.get(null);
        } catch (Throwable t) { }
        U = u;
    }
    private static long align8(long l) { return (l + 7) & ~7L; }

    @Override public long sizeOf(Object o) {
        if (o == null) return 0;
        Class<?> c = o.getClass();
        if (c.isArray()) {
            int base = U.arrayBaseOffset(c), scale = U.arrayIndexScale(c);
            return align8((long) base + (long) scale * java.lang.reflect.Array.getLength(o));
        }
        long maxEnd = objectHeaderSize();
        for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass())
            for (Field f : k.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers())) continue;
                long off = U.objectFieldOffset(f);
                maxEnd = Math.max(maxEnd, off + sizeOfField(fieldTypeName(f)));
            }
        return align8(maxEnd);
    }
    private static String fieldTypeName(Field f) {
        Class<?> t = f.getType();
        if (!t.isPrimitive()) return "ref";
        if (t == boolean.class) return "boolean";
        if (t == byte.class) return "byte";
        if (t == char.class) return "char";
        if (t == short.class) return "short";
        if (t == int.class) return "int";
        if (t == long.class) return "long";
        if (t == float.class) return "float";
        return "double";
    }
    @Override public long sizeOfField(String type) {
        switch (type == null ? "ref" : type) {
            case "boolean": case "byte": return 1;
            case "char": case "short": return 2;
            case "int": case "float": return 4;
            case "long": case "double": return 8;
            default: return 4; // compressed reference
        }
    }
    @Override public long addressOf(Object o) { return ((long) System.identityHashCode(o)) * 8; } // identity dedup only
    @Override public long fieldOffset(Field f) { return U.objectFieldOffset(f); }
    private static Class<?> arrClass(String type) {
        switch (type) {
            case "[Z": return boolean[].class; case "[B": return byte[].class; case "[C": return char[].class;
            case "[S": return short[].class; case "[I": return int[].class; case "[J": return long[].class;
            case "[F": return float[].class; case "[D": return double[].class;
            default: return Object[].class;
        }
    }
    @Override public int arrayBaseOffset(String type) { return U.arrayBaseOffset(arrClass(type)); }
    @Override public int arrayIndexScale(String type) { return U.arrayIndexScale(arrClass(type)); }
    @Override public int objectAlignment() { return 8; }
    @Override public int objectHeaderSize() { return 12; }
    @Override public int arrayHeaderSize() { return 16; }
    @Override public int addressSize() { return 8; }
    @Override public int classPointerSize() { return 4; }
    @Override public boolean getBoolean(Object o, long off) { return U.getBoolean(o, off); }
    @Override public byte getByte(Object o, long off) { return U.getByte(o, off); }
    @Override public short getShort(Object o, long off) { return U.getShort(o, off); }
    @Override public char getChar(Object o, long off) { return U.getChar(o, off); }
    @Override public int getInt(Object o, long off) { return U.getInt(o, off); }
    @Override public float getFloat(Object o, long off) { return U.getFloat(o, off); }
    @Override public long getLong(Object o, long off) { return U.getLong(o, off); }
    @Override public double getDouble(Object o, long off) { return U.getDouble(o, off); }
    @Override public Object getObject(Object o, long off) { return U.getObject(o, off); }
    @Override public String details() { return "hunt3.jolsub.Hunt3JolVM (GraalVM native-image substitution; approximate layout model)"; }
}
