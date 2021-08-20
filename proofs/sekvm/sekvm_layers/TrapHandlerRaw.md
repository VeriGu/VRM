# TrapHandlerRaw

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

Require Import MmioSPTWalk.Spec.
Require Import TrapHandlerRaw.Spec.
Require Import RData.
Require Import HypsecCommLib.
Require Import NPTWalk.Spec.
Require Import Constants.
Require Import Ident.

Local Open Scope Z_scope.

Section TrapHandlerRawLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TrapHandlerRaw_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TrapHandlerRaw_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance host_hvc_handler_raw_inv: PreservesInvariants host_hvc_handler_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_exit_handler_raw_inv: PreservesInvariants vm_exit_handler_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_vcpu_run_handler_raw_inv: PreservesInvariants host_vcpu_run_handler_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_npt_handler_raw_inv: PreservesInvariants host_npt_handler_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_store_ref_inv: PreservesInvariants mem_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_load_ref_inv: PreservesInvariants mem_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_load_ref_inv: PreservesInvariants dev_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_store_ref_inv: PreservesInvariants dev_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition TrapHandlerRaw_fresh : compatlayer (cdata RData) :=
      host_hvc_handler_raw ↦ gensem host_hvc_handler_raw_spec
          ⊕ vm_exit_handler_raw ↦ gensem vm_exit_handler_raw_spec
          ⊕ host_vcpu_run_handler_raw ↦ gensem host_vcpu_run_handler_raw_spec
          ⊕ host_npt_handler_raw ↦ gensem host_npt_handler_raw_spec.

    Definition TrapHandlerRaw_passthrough : compatlayer (cdata RData) :=
      mem_store_ref ↦ gensem mem_store_ref_spec
          ⊕ mem_load_ref ↦ gensem mem_load_ref_spec
          ⊕ dev_load_ref ↦ gensem dev_load_ref_spec
          ⊕ dev_store_ref ↦ gensem dev_store_ref_spec.

    Definition TrapHandlerRaw := TrapHandlerRaw_fresh ⊕ TrapHandlerRaw_passthrough.

  End LayerDef.

End TrapHandlerRawLayer.
```
