# CtxtSwitchSpec

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import GenSem.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import RealParams.
Require Import GenSem.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import PrimSemantics.
Require Import CompatClightSem.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractMachine.Spec.
Require Import VCPUOps.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import VCPUOps.Layer.
Require Import BootOps.Spec.

Local Open Scope Z_scope.

Section CtxtSwitchSpec.

  Definition save_host_spec  (adt: RData) : option RData :=
    when adt1 == save_sysregs_spec adt;
    fpsimd_save_state_spec adt1.

  Definition restore_host_spec  (adt: RData) : option RData :=
    when adt1 == set_per_cpu_spec HOSTVISOR 0 adt;
    when adt2 == host_el2_restore_state_spec adt1;
    when adt3 == restore_sysregs_spec adt2;
    fpsimd_restore_state_spec adt3.

  Definition save_vm_spec  (adt: RData) : option RData :=
    when adt1 == save_sysregs_spec adt;
    when adt2 == fpsimd_save_state_spec adt1;
    when adt3 == deactivate_traps_spec adt2;
    when adt4 == timer_enable_traps_spec adt3;
    when adt5 == save_shadow_kvm_regs_spec adt4;
    when vmid == get_cur_vmid_spec adt5;
    when vcpuid == get_cur_vcpuid_spec adt5;
    set_vcpu_inactive_spec vmid vcpuid adt5.

  Definition restore_vm_spec  (adt: RData) : option RData :=
    when cur_vmid == get_cur_vmid_spec adt;
    when cur_vcpuid == get_cur_vcpuid_spec adt;
    when' vmid == get_shadow_ctxt_spec cur_vmid cur_vcpuid X0 adt;
    if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
      when' vcpuid, adt0 == get_int_run_vcpuid_spec vmid adt;
      if (0 <=? vcpuid) && (vcpuid <? VCPU_PER_VM) then
        when adt' == set_per_cpu_spec vmid vcpuid adt0;
        when adt1 == set_vcpu_active_spec vmid vcpuid adt';
        when adt2 == restore_shadow_kvm_regs_spec adt1;
        when adt3 == vm_el2_restore_state_spec adt2;
        when adt4 == timer_enable_traps_spec adt3;
        when adt5 == activate_traps_spec adt4;
        when adt6 == restore_sysregs_spec adt5;
        fpsimd_restore_state_spec adt6
      else
        panic_spec adt
    else
      panic_spec adt.

End CtxtSwitchSpec.

Section CtxtSwitchSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := VCPUOps_ops) LDATA).

  Inductive save_host_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | save_host_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: save_host_spec  labd = Some labd'):
      save_host_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive restore_host_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | restore_host_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: restore_host_spec  labd = Some labd'):
      restore_host_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive save_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | save_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: save_vm_spec  labd = Some labd'):
      save_vm_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive restore_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | restore_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: restore_vm_spec  labd = Some labd'):
      restore_vm_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition save_host_spec_low: compatsem LDATAOps :=
      csem save_host_spec_low_step (type_of_list_type nil) Tvoid.

    Definition restore_host_spec_low: compatsem LDATAOps :=
      csem restore_host_spec_low_step (type_of_list_type nil) Tvoid.

    Definition save_vm_spec_low: compatsem LDATAOps :=
      csem save_vm_spec_low_step (type_of_list_type nil) Tvoid.

    Definition restore_vm_spec_low: compatsem LDATAOps :=
      csem restore_vm_spec_low_step (type_of_list_type nil) Tvoid.

  End WITHMEM.

End CtxtSwitchSpecLow.

```
