# LocksRefine

```coq
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import ZSet.
Require Import ListLemma2.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import RealParams.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import LayerCalculusLemma.
Require Import TacticsForTesting.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalLock.
Require Import RData.
Require Import Constants.
Require Import Locks.Layer.
Require Import HypsecCommLib.
Require Import Locks.Spec.
Require Import LockOpsH.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LocksProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := Locks_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := LockOpsH_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_rel: hadt = ladt
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    Section MetaPrim.

      Lemma acquire_lock_spec_exists:
        forall habd habd' labd lk f
               (Hspec: acquire_lock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_spec0 lk labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold acquire_lock_spec, acquire_lock_spec0.
        unfold Spec.acquire_shared_spec, Spec.wait_hlock_spec.
        intros. inv Hrel.
        subdestruct; inv Hspec.

        rewrite ZMap.gss. rewrite ZMap.gss.

        simpl (H_CalLock ((TEVENT _ (TTICKET (WAIT_LOCK _))) :: _)).
        prename (H_CalLock _ = Some _) into HCal.
        rewrite HCal.

        prename (negb (zeq _ _) = false) into Hcpucheck.
        rewrite Hcpucheck.

        simpl (CalState _ (TEVENT _ (TTICKET (WAIT_LOCK _)) :: _) _).

        eexists; split; [reflexivity|].

        constructor.
        rewrite ZMap.set2. rewrite ZMap.set2.
        reflexivity.
      Qed.

      Lemma release_lock_spec_exists:
        forall habd habd' labd lk f e
               (Hspec: release_lock_spec e lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_spec0 e lk labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold release_lock_spec, release_lock_spec0.
        unfold Spec.release_shared_spec, Spec.pass_hlock_spec.
        intros. inv Hrel.
        subdestruct; inv Hspec.

        rewrite ZMap.gss. rewrite ZMap.gss.

        simpl (H_CalLock (TEVENT _ (TSHARED _) :: _)).
        prename (H_CalLock _ = Some _) into HCal.
        rewrite HCal.

        prename (negb (zeq _ _) = false) into Hcpucheck.
        rewrite Hcpucheck.
        rewrite Hcpucheck.

        eexists; split; [reflexivity|].

        constructor.
        rewrite ZMap.set2. rewrite ZMap.set2.
        reflexivity.
      Qed.

    End MetaPrim.

    Section FreshPrim.

      Lemma acquire_lock_pt_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: acquire_lock_pt_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_pt_spec0 vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_pt_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_pt_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_pt_spec) acquire_lock_pt_spec_low.
      Proof.
        Opaque acquire_lock_pt_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma acquire_lock_spt_spec_exists:
        forall habd habd' labd  f
               (Hspec: acquire_lock_spt_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_spt_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_spt_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_spt_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_spt_spec) acquire_lock_spt_spec_low.
      Proof.
        Opaque acquire_lock_spt_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma acquire_lock_s2page_spec_exists:
        forall habd habd' labd  f
               (Hspec: acquire_lock_s2page_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_s2page_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_s2page_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_s2page_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_s2page_spec) acquire_lock_s2page_spec_low.
      Proof.
        Opaque acquire_lock_s2page_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_s2page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma acquire_lock_core_spec_exists:
        forall habd habd' labd  f
               (Hspec: acquire_lock_core_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_core_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_core_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_core_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_core_spec) acquire_lock_core_spec_low.
      Proof.
        Opaque acquire_lock_core_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_core_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma acquire_lock_vm_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: acquire_lock_vm_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_vm_spec0 vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_vm_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_vm_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_vm_spec) acquire_lock_vm_spec_low.
      Proof.
        Opaque acquire_lock_vm_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_vm_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma acquire_lock_smmu_spec_exists:
        forall habd habd' labd  f
               (Hspec: acquire_lock_smmu_spec habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', acquire_lock_smmu_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold acquire_lock_smmu_spec, Assertion.
          intros. subdestruct.
          eapply acquire_lock_spec_exists; eauto.
        Qed.

      Lemma acquire_lock_smmu_spec_ref:
        compatsim (crel RData RData) (gensem acquire_lock_smmu_spec) acquire_lock_smmu_spec_low.
      Proof.
        Opaque acquire_lock_smmu_spec.
        compatsim_simpl (@match_RData).
        exploit acquire_lock_smmu_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_pt_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: release_lock_pt_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_pt_spec0 vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_pt_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_pt_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_pt_spec) release_lock_pt_spec_low.
      Proof.
        Opaque release_lock_pt_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_spt_spec_exists:
        forall habd habd' labd  f
               (Hspec: release_lock_spt_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_spt_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_spt_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_spt_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_spt_spec) release_lock_spt_spec_low.
      Proof.
        Opaque release_lock_spt_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_s2page_spec_exists:
        forall habd habd' labd  f
               (Hspec: release_lock_s2page_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_s2page_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_s2page_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_s2page_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_s2page_spec) release_lock_s2page_spec_low.
      Proof.
        Opaque release_lock_s2page_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_s2page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_core_spec_exists:
        forall habd habd' labd  f
               (Hspec: release_lock_core_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_core_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_core_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_core_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_core_spec) release_lock_core_spec_low.
      Proof.
        Opaque release_lock_core_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_core_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_vm_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: release_lock_vm_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_vm_spec0 vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_vm_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_vm_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_vm_spec) release_lock_vm_spec_low.
      Proof.
        Opaque release_lock_vm_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_vm_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma release_lock_smmu_spec_exists:
        forall habd habd' labd  f
               (Hspec: release_lock_smmu_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', release_lock_smmu_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold release_lock_smmu_spec, Assertion.
          intros; subdestruct.
          eapply release_lock_spec_exists; [inv Hrel|]; eauto.
        Qed.

      Lemma release_lock_smmu_spec_ref:
        compatsim (crel RData RData) (gensem release_lock_smmu_spec) release_lock_smmu_spec_low.
      Proof.
        Opaque release_lock_smmu_spec.
        compatsim_simpl (@match_RData).
        exploit release_lock_smmu_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) Locks_passthrough LockOpsH.
      Proof.
        sim_oplus; layer_sim_simpl; compatsim_simpl (@match_AbData);
        match_external_states_simpl; destruct match_related; srewrite;
        reflexivity.
      Qed.

    End PassthroughPrim.

  End WITHMEM.

End LocksProofHigh.
```
