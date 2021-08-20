# TrapDispatcher

```coq
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import XOmega.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractMachine.Spec.
Require Import MmioSPTWalk.Spec.
Require Import RData.
Require Import HypsecCommLib.
Require Import TrapDispatcher.Spec.
Require Import NPTWalk.Spec.
Require Import Constants.
Require Import Ident.
Require Import CtxtSwitch.Spec.
Require Import FaultHandler.Spec.

Local Open Scope Z_scope.

Section TrapDispatcherLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TrapDispatcher_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TrapDispatcher_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance host_hvc_dispatcher_inv: PreservesInvariants host_hvc_dispatcher_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_exit_dispatcher_inv: PreservesInvariants vm_exit_dispatcher_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_to_host_inv: PreservesInvariants core_to_host_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_store_ref_inv: PreservesInvariants mem_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_to_core_inv: PreservesInvariants host_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vmid_inv: PreservesInvariants get_cur_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_load_ref_inv: PreservesInvariants dev_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance restore_vm_inv: PreservesInvariants restore_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance exit_populate_fault_inv: PreservesInvariants exit_populate_fault_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_host_inv: PreservesInvariants save_host_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_load_ref_inv: PreservesInvariants mem_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance handle_host_stage2_fault_inv: PreservesInvariants handle_host_stage2_fault_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_to_vm_inv: PreservesInvariants core_to_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance restore_host_inv: PreservesInvariants restore_host_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_store_ref_inv: PreservesInvariants dev_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_to_core_inv: PreservesInvariants vm_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance panic_inv: PreservesInvariants panic_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_ctxt_inv: PreservesInvariants get_shadow_ctxt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_vm_inv: PreservesInvariants save_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vcpuid_inv: PreservesInvariants get_cur_vcpuid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition TrapDispatcher_fresh : compatlayer (cdata RData) :=
      host_hvc_dispatcher ↦ gensem host_hvc_dispatcher_spec
          ⊕ vm_exit_dispatcher ↦ gensem vm_exit_dispatcher_spec.

    Definition TrapDispatcher_passthrough : compatlayer (cdata RData) :=
      core_to_host ↦ gensem core_to_host_spec
          ⊕ mem_store_ref ↦ gensem mem_store_ref_spec
          ⊕ host_to_core ↦ gensem host_to_core_spec
          ⊕ get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ dev_load_ref ↦ gensem dev_load_ref_spec
          ⊕ restore_vm ↦ gensem restore_vm_spec
          ⊕ exit_populate_fault ↦ gensem exit_populate_fault_spec
          ⊕ save_host ↦ gensem save_host_spec
          ⊕ mem_load_ref ↦ gensem mem_load_ref_spec
          ⊕ handle_host_stage2_fault ↦ gensem handle_host_stage2_fault_spec
          ⊕ core_to_vm ↦ gensem core_to_vm_spec
          ⊕ restore_host ↦ gensem restore_host_spec
          ⊕ dev_store_ref ↦ gensem dev_store_ref_spec
          ⊕ vm_to_core ↦ gensem vm_to_core_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ save_vm ↦ gensem save_vm_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec.

    Definition TrapDispatcher := TrapDispatcher_fresh ⊕ TrapDispatcher_passthrough.

  End LayerDef.

End TrapDispatcherLayer.
```
