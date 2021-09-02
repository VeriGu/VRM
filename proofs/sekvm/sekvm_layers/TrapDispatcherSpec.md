# Spec

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
Require Import FaultHandler.Layer.
Require Import FaultHandler.Spec.
Require Import MemHandler.Spec.
Require Import MmioOps.Spec.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section TrapDispatcherSpec.

  Definition host_hvc_dispatcher_spec  (adt: RData) : option RData :=
    when vmid == get_cur_vmid_spec adt;
    when vcpuid == get_cur_vcpuid_spec adt;
    when' arg == get_shadow_ctxt_spec vmid vcpuid X0 adt;
    when' arg1 == get_shadow_ctxt_spec vmid vcpuid X1 adt;
    when' arg2 == get_shadow_ctxt_spec vmid vcpuid X2 adt;
    when' arg3 == get_shadow_ctxt_spec vmid vcpuid X3 adt;
    when' arg4 == get_shadow_ctxt_spec vmid vcpuid X4 adt;
    when' arg5 == get_shadow_ctxt_spec vmid vcpuid X5 adt;
    rely is_vmid vmid; rely is_vcpu vcpuid; rely is_int64 arg; rely is_int64 arg1; rely is_int64 arg2;
    rely is_int64 arg3; rely is_int64 arg4; rely is_int64 arg5;
    if arg =? HVC_TIMER_SET_CNTVOFF then
        timer_set_cntvoff_spec adt
    else
    if arg =? HVC_CLEAR_VM_S2_RANGE then
      if (HOSTVISOR <? arg1) && (arg1 <? COREVISOR) && (0 <=? arg2) && (arg2 <? KVM_ADDR_SPACE) &&
         (0 <=? arg3) && (arg3 <? KVM_ADDR_SPACE)
      then clear_vm_stage2_range_spec arg1 (VZ64 arg2) (VZ64 arg3) adt
      else panic_spec adt
    else
    if arg =? HVC_SET_BOOT_INFO then
      if (HOSTVISOR <? arg1) && (arg1 <? COREVISOR) && (0 <=? arg2) && (arg2 <? KVM_PHYS_SIZE) &&
         (0 <=? arg3) && (arg3 <? KVM_PHYS_SIZE) && (arg2 + arg3 <? KVM_PHYS_SIZE)
      then when res,  adt' == set_boot_info_spec arg1 (VZ64 arg2) (VZ64 arg3) adt; Some adt'
      else panic_spec adt
    else
    if arg =? HVC_REMAP_VM_IMAGE then
      if (HOSTVISOR <? arg1) && (arg1 <? COREVISOR) && (0 <=? arg2) && (arg2 <? KVM_PFN_SPACE) && (0 <=? arg3) && (arg3 <? MAX_LOAD_INFO_NUM)
      then remap_vm_image_spec arg1 (VZ64 arg2) arg3 adt
      else panic_spec adt
    else
    if arg =? HVC_VERIFY_VM_IMAGE then
      if (HOSTVISOR <? arg1) && (arg1 <? COREVISOR)
      then verify_and_load_images_spec arg1 adt
      else panic_spec adt
    else
    if arg =? HVC_SMMU_FREE_PGD then
      if (0 <=? arg1) && (arg1 <? SMMU_NUM_CTXT_BANKS) && (0 <=? arg2) && (arg2 <? SMMU_NUM)
      then el2_free_smmu_pgd_spec arg1 arg2 adt
      else panic_spec adt
    else
    if arg =? HVC_SMMU_ALLOC_PGD then
      if (0 <=? arg1) && (arg1 <? SMMU_NUM_CTXT_BANKS) && (HOSTVISOR <=? arg2) && (arg2 <? COREVISOR) &&
         (0 <=? arg3) && (arg3 <? SMMU_NUM)
      then el2_alloc_smmu_pgd_spec arg1 arg2 arg3 adt
      else panic_spec adt
    else
    if arg =? HVC_SMMU_LPAE_MAP then
      if (0 <=? arg1) && (arg1 <? KVM_PHYS_SIZE) && (0 <=? arg2) && (arg2 <? KVM_PHYS_SIZE) && (0 <=? arg3) && (arg3 <? 9223372036854775807) &&
          (phys_page arg3 =? 0) && (0 <=? arg4) && (arg4 <? SMMU_NUM_CTXT_BANKS) && (0 <=? arg5) && (arg5 <? SMMU_NUM)
      then el2_arm_lpae_map_spec (VZ64 arg1) (VZ64 arg2) (VZ64 arg3) arg4 arg5 adt
      else panic_spec adt
    else
    if arg =? HVC_SMMU_LPAE_IOVA_TO_PHYS then
      if (0 <=? arg1) && (arg1 <? KVM_PHYS_SIZE) && (0 <=? arg2) && (arg2 <? SMMU_NUM_CTXT_BANKS) && (0 <=? arg3) && (arg3 <? SMMU_NUM)
      then
        when' ret64, adt' == el2_arm_lpae_iova_to_phys_spec (VZ64 arg1) arg2 arg3 adt;
        rely is_int64 ret64;
        set_shadow_ctxt_spec vmid vcpuid X0 (VZ64 ret64) adt'
      else panic_spec adt
    else
    if arg =? HVC_SMMU_CLEAR then
      if (0 <=? arg1) && (arg1 <? KVM_PHYS_SIZE) && (0 <=? arg2) && (arg2 <? SMMU_NUM_CTXT_BANKS) && (0 <=? arg3) && (arg3 <? SMMU_NUM)
      then  el2_arm_lpae_clear_spec (VZ64 arg1) arg2 arg3 adt
      else panic_spec adt
    else
    if arg =? HVC_REGISTER_KVM then
      when ret, adt' == register_kvm_spec adt;
      rely is_int ret;
      set_shadow_ctxt_spec vmid vcpuid X0 (VZ64 ret) adt'
    else
    if arg =? HVC_REGISTER_VCPU then
      if (HOSTVISOR <? arg1) && (arg1 <? COREVISOR) && (0 <=? arg2) && (arg2 <? VCPU_PER_VM) then
        register_vcpu_spec arg1 arg2 adt
      else panic_spec adt
    else
    if arg =? HVC_PHYS_ADDR_IOREMAP then
      if (HOSTVISOR <=? arg1) && (arg1 <=? COREVISOR) && (0 <=? arg2) && (0 <=? arg3) && (0 <=? arg4) &&
         (arg2 + arg4 <? KVM_ADDR_SPACE) && (arg3 + arg4 <? KVM_PHYS_SIZE)
      then kvm_phys_addr_ioremap_spec arg1 (VZ64 arg2) (VZ64 arg3) (VZ64 arg4) adt
      else panic_spec adt
    else Some adt.

  Definition vm_exit_dispatcher_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z) :=
    when' esr_el2 == get_shadow_ctxt_spec vmid vcpuid ESR_EL2 adt;
    rely is_int64 esr_el2;
    let exit_type := Z.land (esr_el2 / 67108864) 63 in
    if exit_type =? ESR_ELx_EC_SYS64 then
      when adt' == core_handle_sys64_spec adt;
      when ret == check_spec 0 adt';
      rely is_int ret;
      Some (adt', ret)
    else
      if exit_type =? ESR_ELx_EC_HVC64 then
        when res, adt' == core_handle_pvops_spec adt;
        rely is_int res;
        when ret == check_spec res adt';
        rely is_int ret;
        Some (adt', ret)
      else
        when adt' == panic_spec adt;
        when ret == check_spec 0 adt';
        rely is_int ret;
        Some (adt', ret).

End TrapDispatcherSpec.

Section TrapDispatcherSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := FaultHandler_ops) LDATA).

  Inductive host_hvc_dispatcher_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_hvc_dispatcher_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_hvc_dispatcher_spec  labd = Some labd'):
      host_hvc_dispatcher_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive vm_exit_dispatcher_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | vm_exit_dispatcher_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid res
      (Hinv: high_level_invariant labd)
      (Hspec: vm_exit_dispatcher_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some (labd', (Int.unsigned res))):
      vm_exit_dispatcher_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition host_hvc_dispatcher_spec_low: compatsem LDATAOps :=
      csem host_hvc_dispatcher_spec_low_step (type_of_list_type nil) Tvoid.

    Definition vm_exit_dispatcher_spec_low: compatsem LDATAOps :=
      csem vm_exit_dispatcher_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

  End WITHMEM.

End TrapDispatcherSpecLow.

```
