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
Require Import Constants.
Require Import Ident.
Require Import HypsecCommLib.
Require Import Locks.Spec.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.

Section LocksLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance Locks_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance Locks_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance acquire_lock_core_inv: PreservesInvariants acquire_lock_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_vm_inv: PreservesInvariants acquire_lock_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_spt_inv: PreservesInvariants acquire_lock_spt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_pt_inv: PreservesInvariants release_lock_pt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_s2page_inv: PreservesInvariants release_lock_s2page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_smmu_inv: PreservesInvariants acquire_lock_smmu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_core_inv: PreservesInvariants release_lock_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_smmu_inv: PreservesInvariants release_lock_smmu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_pt_inv: PreservesInvariants acquire_lock_pt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_s2page_inv: PreservesInvariants acquire_lock_s2page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_spt_inv: PreservesInvariants release_lock_spt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_vm_inv: PreservesInvariants release_lock_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance panic_inv: PreservesInvariants panic_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition Locks_fresh : compatlayer (cdata RData) :=
      acquire_lock_core ↦ gensem acquire_lock_core_spec
    ⊕ acquire_lock_vm ↦ gensem acquire_lock_vm_spec
    ⊕ acquire_lock_spt ↦ gensem acquire_lock_spt_spec
    ⊕ release_lock_pt ↦ gensem release_lock_pt_spec
    ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
    ⊕ acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
    ⊕ release_lock_core ↦ gensem release_lock_core_spec
    ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
    ⊕ acquire_lock_pt ↦ gensem acquire_lock_pt_spec
    ⊕ acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
    ⊕ release_lock_spt ↦ gensem release_lock_spt_spec
    ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
    .

    Definition Locks_passthrough : compatlayer (cdata RData) :=
      panic ↦ gensem panic_spec
    .

    Definition Locks := Locks_fresh ⊕ Locks_passthrough.

  End LayerDef.

End LocksLayer.
```
