# ProofHigh

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

Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioCoreAux.Spec.
Require Import MmioRaw.Layer.
Require Import MmioCoreAux.Layer.
Require Import AbstractMachine.Spec.
Require Import MmioRaw.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioCoreAuxProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioCoreAux_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioRaw_ops) HDATA).

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

    Section FreshPrim.

      Hint Unfold
           writel_relaxed_spec
           get_cur_vcpuid_spec
           check_spec
           __handle_smmu_read_spec0
           get_smmu_cfg_vmid_spec
           host_dabt_get_rd_spec
           panic_spec
           handle_smmu_global_access_spec0
           __handle_smmu_read_spec
           handle_smmu_cb_access_spec
           handle_smmu_global_access_spec
           handle_smmu_cb_access_spec0
           __handle_smmu_write_spec
           __handle_smmu_write_spec0
           readl_relaxed_spec
           writeq_relaxed_spec
           host_get_mmio_data_spec
           readq_relaxed_spec.

      Lemma handle_smmu_global_access_spec_exists:
        forall habd labd hsr offset smmu_index res f
               (Hspec: handle_smmu_global_access_spec hsr offset smmu_index habd = Some res)
               (Hrel: relate_RData f habd labd),
          handle_smmu_global_access_spec0 hsr offset smmu_index labd = Some res.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite; try reflexivity.
          simpl; repeat destruct_if; reflexivity.
        Qed.

      Lemma handle_smmu_global_access_spec_ref:
        compatsim (crel RData RData) (gensem handle_smmu_global_access_spec) handle_smmu_global_access_spec_low.
      Proof.
        Opaque handle_smmu_global_access_spec.
        compatsim_simpl (@match_RData).
        exploit handle_smmu_global_access_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent handle_smmu_global_access_spec.
      Qed.

      Lemma handle_smmu_cb_access_spec_exists:
        forall habd labd offset res f
               (Hspec: handle_smmu_cb_access_spec offset habd = Some res)
               (Hrel: relate_RData f habd labd),
          handle_smmu_cb_access_spec0 offset labd = Some res.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite; try reflexivity.
          simpl; repeat destruct_if; reflexivity.
        Qed.

      Lemma handle_smmu_cb_access_spec_ref:
        compatsim (crel RData RData) (gensem handle_smmu_cb_access_spec) handle_smmu_cb_access_spec_low.
      Proof.
        Opaque handle_smmu_cb_access_spec.
        compatsim_simpl (@match_RData).
        exploit handle_smmu_cb_access_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent handle_smmu_cb_access_spec.
      Qed.

      Lemma __handle_smmu_write_spec_exists:
        forall habd habd' labd hsr fault_ipa len val write_val f
               (Hspec: __handle_smmu_write_spec hsr fault_ipa len val write_val habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', __handle_smmu_write_spec0 hsr fault_ipa len val write_val labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite;
            try (eexists; split; [reflexivity|constructor;reflexivity]).
          repeat destruct_if; eexists; (split; [reflexivity|constructor;destruct habd'; simpl in *; srewrite; reflexivity]).
        Qed.

      Lemma __handle_smmu_write_spec_ref:
        compatsim (crel RData RData) (gensem __handle_smmu_write_spec) __handle_smmu_write_spec_low.
      Proof.
        Opaque __handle_smmu_write_spec.
        compatsim_simpl (@match_RData).
        exploit __handle_smmu_write_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent __handle_smmu_write_spec.
      Qed.

      Lemma __handle_smmu_read_spec_exists:
        forall habd habd' labd hsr fault_ipa len f
               (Hspec: __handle_smmu_read_spec hsr fault_ipa len habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', __handle_smmu_read_spec0 hsr fault_ipa len labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite;
            try (eexists; split; [reflexivity|constructor;reflexivity]).
          extract_if. autounfold in *; apply andb_true_iff; split; bool_rel_all; somega. rewrite Cond.
          simpl. unfold set_shadow_ctxt_spec; srewrite.
          repeat destruct_if; eexists; (split; [reflexivity|constructor;destruct habd'; simpl in *; srewrite; reflexivity]).
          extract_if. autounfold in *; apply andb_true_iff; split; bool_rel_all; somega. rewrite Cond.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma __handle_smmu_read_spec_ref:
        compatsim (crel RData RData) (gensem __handle_smmu_read_spec) __handle_smmu_read_spec_low.
      Proof.
        Opaque __handle_smmu_read_spec.
        compatsim_simpl (@match_RData).
        exploit __handle_smmu_read_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent __handle_smmu_read_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MmioCoreAuxProofHigh.
```
