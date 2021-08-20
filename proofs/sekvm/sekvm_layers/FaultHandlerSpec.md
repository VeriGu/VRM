# FaultHandlerSpec

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
Require Import MemoryOps.Spec.
Require Import MemManager.Spec.
Require Import MemHandler.Layer.
Require Import MmioOps.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MemoryOps.Spec.

Local Open Scope Z_scope.

Section FaultHandlerSpec.

  Definition handle_host_stage2_fault_spec  (adt: RData) : option RData :=
    when' addr0 == read_hpfar_el2_spec adt;
    rely is_int64 addr0;
    let addr := (Z.land addr0 HPFAR_MASK) * 256 in
    when esr == read_esr_el2_spec adt;
    rely is_int esr;
    when ret, adt' == emulate_mmio_spec (VZ64 addr) esr adt;
    if ret =? INVALID then
      map_page_host_spec (VZ64 addr) adt'
    else
      Some adt'.

  Definition core_handle_pvops_spec (adt: RData) : option (RData * Z) :=
    when vmid == get_cur_vmid_spec adt;
    rely is_vmid vmid;
    when vcpuid == get_cur_vcpuid_spec adt;
    rely is_vcpu vcpuid;
    when' arg == get_shadow_ctxt_spec vmid vcpuid X0 adt;
    when' addr == get_shadow_ctxt_spec vmid vcpuid X2 adt;
    when' size == get_shadow_ctxt_spec vmid vcpuid X3 adt;
    if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
      if (arg =? HVC_KVM_SET_DESC_PFN) then
        when adt' == grant_stage2_sg_gpa_spec vmid (VZ64 addr) (VZ64 size) adt;
        when ret == check_spec 0 adt';
        Some (adt', ret)
      else if (arg =? HVC_KVM_UNSET_DESC_PFN) then
        when adt' == revoke_stage2_sg_gpa_spec vmid (VZ64 addr) (VZ64 size) adt;
        when ret == check_spec 0 adt';
        Some (adt', ret)
      else
        when ret == check_spec 1 adt;
        Some (adt, ret)
    else
      when adt' == panic_spec adt;
      when ret == check_spec 0 adt';
      Some (adt', ret).

End FaultHandlerSpec.

Section FaultHandlerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MemHandler_ops) LDATA).

  Inductive handle_host_stage2_fault_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_host_stage2_fault_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: handle_host_stage2_fault_spec  labd = Some labd'):
      handle_host_stage2_fault_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive core_handle_pvops_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | core_handle_pvops_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'  res
      (Hinv: high_level_invariant labd)
      (Hspec: core_handle_pvops_spec  labd = Some (labd', (Int.unsigned res))):
      core_handle_pvops_spec_low_step s WB nil (m'0, labd) (Vint res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition handle_host_stage2_fault_spec_low: compatsem LDATAOps :=
      csem handle_host_stage2_fault_spec_low_step (type_of_list_type nil) Tvoid.

    Definition core_handle_pvops_spec_low: compatsem LDATAOps :=
      csem core_handle_pvops_spec_low_step (type_of_list_type nil) Tint32.

  End WITHMEM.

End FaultHandlerSpecLow.

```
