package hunt3.jolsub;

import com.oracle.svm.core.annotate.Substitute;
import com.oracle.svm.core.annotate.TargetClass;

/** Native-image-only substitution: jol 0.16 VM.current() refuses non-HotSpot VMs. See Hunt3JolVM. */
@TargetClass(className = "org.openjdk.jol.vm.VM")
final class Target_org_openjdk_jol_vm_VM {
    @Substitute
    public static org.openjdk.jol.vm.VirtualMachine current() {
        return Hunt3JolVM.INSTANCE;
    }
}
