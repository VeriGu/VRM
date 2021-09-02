# Layer

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

Require Import RData.
Require Import HypsecCommLib.
Require Import TrapHandler.Spec.
Require Import Constants.
Require Import Ident.

Local Open Scope Z_scope.

Section TrapHandlerLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TrapHandler_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TrapHandler_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance vm_exit_handler_inv: PreservesInvariants vm_exit_handler_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_store_inv: PreservesInvariants dev_store_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_hvc_handler_inv: PreservesInvariants host_hvc_handler_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_store_inv: PreservesInvariants mem_store_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_npt_handler_inv: PreservesInvariants host_npt_handler_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_load_inv: PreservesInvariants dev_load_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_load_inv: PreservesInvariants mem_load_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_vcpu_run_handler_inv: PreservesInvariants host_vcpu_run_handler_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition TrapHandler_fresh : compatlayer (cdata RData) :=
      vm_exit_handler ↦ gensem vm_exit_handler_spec
          ⊕ dev_store ↦ gensem dev_store_spec
          ⊕ host_hvc_handler ↦ gensem host_hvc_handler_spec
          ⊕ mem_store ↦ gensem mem_store_spec
          ⊕ host_npt_handler ↦ gensem host_npt_handler_spec
          ⊕ dev_load ↦ gensem dev_load_spec
          ⊕ mem_load ↦ gensem mem_load_spec
          ⊕ host_vcpu_run_handler ↦ gensem host_vcpu_run_handler_spec.

    Definition TrapHandler_passthrough : compatlayer (cdata RData) :=
      ∅.

    Definition TrapHandler := TrapHandler_fresh ⊕ TrapHandler_passthrough.

  End LayerDef.

End TrapHandlerLayer.
```
