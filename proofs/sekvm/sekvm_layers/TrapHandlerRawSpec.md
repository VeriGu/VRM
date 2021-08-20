# TrapHandlerRawSpec

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
Require Import FaultHandler.Spec.
Require Import TrapDispatcher.Spec.
Require Import CtxtSwitch.Spec.
Require Import RData.
Require Import TrapDispatcher.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section TrapHandlerRawSpec.

  Definition host_hvc_handler_raw_spec  (adt: RData) : option RData :=
    when adt1 == host_to_core_spec adt;
    when adt2 == host_hvc_dispatcher_spec adt1;
    core_to_host_spec adt2.

  Definition host_npt_handler_raw_spec  (adt: RData) : option RData :=
    when adt1 == host_to_core_spec adt;
    when adt2 == handle_host_stage2_fault_spec adt1;
    core_to_host_spec adt2.

  Definition host_vcpu_run_handler_raw_spec  (adt: RData) : option RData :=
    when adt1 == host_to_core_spec adt;
    when adt2 == save_host_spec adt1;
    when adt3 == restore_vm_spec adt2;
    core_to_vm_spec adt3.

  Definition vm_exit_handler_raw_spec  (adt: RData) : option RData :=
    when vmid == get_cur_vmid_spec adt;
    when vcpuid == get_cur_vcpuid_spec adt;
    rely is_vmid vmid; rely is_vcpu vcpuid;
    when adt1 == vm_to_core_spec adt;
    when adt2 == exit_populate_fault_spec adt1;
    when' ec == get_shadow_ctxt_spec vmid vcpuid EC adt2;
    if ec =? ARM_EXCEPTION_TRAP then
      when ret, adt3 == vm_exit_dispatcher_spec vmid vcpuid adt2;
      if ret =? 0 then
        core_to_vm_spec adt3
      else
        when adt4 == save_vm_spec adt3;
        when adt5 == restore_host_spec adt4;
        core_to_host_spec adt5
    else
    if ec =? ARM_EXCEPTION_INTERRUPT then
      when adt3 == save_vm_spec adt2;
      when adt4 == restore_host_spec adt3;
      core_to_host_spec adt4
    else
      panic_spec adt2.

End TrapHandlerRawSpec.

Section TrapHandlerRawSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := TrapDispatcher_ops) LDATA).

  Inductive host_hvc_handler_raw_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_hvc_handler_raw_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_hvc_handler_raw_spec  labd = Some labd'):
      host_hvc_handler_raw_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive host_npt_handler_raw_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_npt_handler_raw_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_npt_handler_raw_spec  labd = Some labd'):
      host_npt_handler_raw_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive host_vcpu_run_handler_raw_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_vcpu_run_handler_raw_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_vcpu_run_handler_raw_spec  labd = Some labd'):
      host_vcpu_run_handler_raw_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive vm_exit_handler_raw_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | vm_exit_handler_raw_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: vm_exit_handler_raw_spec  labd = Some labd'):
      vm_exit_handler_raw_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition host_hvc_handler_raw_spec_low: compatsem LDATAOps :=
      csem host_hvc_handler_raw_spec_low_step (type_of_list_type nil) Tvoid.

    Definition host_npt_handler_raw_spec_low: compatsem LDATAOps :=
      csem host_npt_handler_raw_spec_low_step (type_of_list_type nil) Tvoid.

    Definition host_vcpu_run_handler_raw_spec_low: compatsem LDATAOps :=
      csem host_vcpu_run_handler_raw_spec_low_step (type_of_list_type nil) Tvoid.

    Definition vm_exit_handler_raw_spec_low: compatsem LDATAOps :=
      csem vm_exit_handler_raw_spec_low_step (type_of_list_type nil) Tvoid.

  End WITHMEM.

End TrapHandlerRawSpecLow.

```
