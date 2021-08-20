# MmioCoreRefine

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
Require Import MmioCore.Layer.
Require Import HypsecCommLib.
Require Import MmioCoreAux.Layer.
Require Import MmioCore.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioRaw.Spec.
Require Import MmioCoreAux.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioCoreProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioCore_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioCoreAux_ops) HDATA).

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
           handle_smmu_read_spec0
           panic_spec
           handle_smmu_read_spec
           smmu_get_cbndx_spec
           __handle_smmu_read_spec
           handle_smmu_write_spec
           handle_smmu_cb_access_spec
           __handle_smmu_write_spec
           handle_smmu_write_spec0
           handle_smmu_global_access_spec
           get_smmu_cfg_hw_ttbr_spec.

      Lemma handle_smmu_write_spec_exists:
        forall habd habd' labd hsr fault_ipa len index f
               (Hspec: handle_smmu_write_spec hsr fault_ipa len index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', handle_smmu_write_spec0 hsr fault_ipa len index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite; simpl in *.
          destruct_if. eexists; split. reflexivity. constructor; destruct habd'; simpl in *; srewrite; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          eexists; split. reflexivity. constructor; destruct habd'; simpl in *; srewrite; reflexivity.
          bool_rel; srewrite. simpl.
          eexists; split. reflexivity. constructor; destruct labd; simpl in *; srewrite; reflexivity.
          extract_if. repeat simpl_hyp C12; contra; inv C12; reflexivity. rewrite Cond.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. repeat simpl_hyp C12; contra; inv C12; reflexivity. rewrite Cond.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. repeat simpl_hyp C12; contra; inv C12; reflexivity. rewrite Cond.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond0.
          srewrite; simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond1.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond0.
          srewrite; simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond1.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond0.
          srewrite; simpl.
          extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond1.
          eexists; split. reflexivity. constructor; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          eexists; split. reflexivity. constructor; destruct labd; simpl in *; srewrite; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          eexists; split. reflexivity. constructor; destruct habd'; simpl in *; srewrite; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          eexists; split. reflexivity. constructor; destruct habd'; simpl in *; srewrite; reflexivity.
          extract_if. bool_rel; omega. rewrite Cond. simpl.
          eexists; split. reflexivity. constructor; destruct labd; simpl in *; srewrite; reflexivity.
        Qed.

      Lemma handle_smmu_write_spec_ref:
        compatsim (crel RData RData) (gensem handle_smmu_write_spec) handle_smmu_write_spec_low.
      Proof.
        Opaque handle_smmu_write_spec.
        compatsim_simpl (@match_RData).
        exploit handle_smmu_write_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent handle_smmu_write_spec.
      Qed.

      Lemma handle_smmu_read_spec_exists:
        forall habd habd' labd hsr fault_ipa len f
               (Hspec: handle_smmu_read_spec hsr fault_ipa len habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', handle_smmu_read_spec hsr fault_ipa len labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *. simpl_hyp Hspec. rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

    End FreshPrim.

  End WITHMEM.

End MmioCoreProofHigh.

```
