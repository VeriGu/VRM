# MmioOpsAuxRefine

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
Require Import MmioOpsAux.Layer.
Require Import Constants.
Require Import MmioCore.Layer.
Require Import MmioOpsAux.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioCore.Spec.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioOpsAuxProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioOpsAux_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioCore_ops) HDATA).

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
           get_smmu_size_spec
           is_smmu_range_spec0
           get_smmu_base_spec
           host_get_fault_ipa_spec
           host_skip_instr_spec
           get_smmu_num_spec
           handle_smmu_read_spec
           handle_host_mmio_spec0
           is_smmu_range_spec
           host_dabt_is_write_spec
           handle_host_mmio_spec
           host_dabt_get_as_spec
           handle_smmu_write_spec
           get_shadow_ctxt_spec
           set_shadow_ctxt_spec.

      Lemma is_smmu_range_spec_exists:
        forall habd labd addr res f
               (Hspec: is_smmu_range_spec addr habd = Some res)
               (Hrel: relate_RData f habd labd),
          is_smmu_range_spec0 addr labd = Some res.
        Proof.
          intros; inv Hrel. unfold is_smmu_range_spec, is_smmu_range_spec0 in *.
          repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          simpl. assumption.
          match goal with
          | [H: is_smmu_range_loop _ z 0 ?c ?v = _ |- context[is_smmu_range_loop0 _ z 0 ?c ?ad]] =>
            assert(forall n t r (nrange: 0 <= Z.of_nat n < 2)
                     (loopH: is_smmu_range_loop n z 0 c v = Some (t, r)),
                      is_smmu_range_loop0 n z 0 c ad = Some (t, r) /\ t = (Z.of_nat n) /\ valid_int r)
          end.
          induction n. intros. simpl in *.  inv loopH. split_and; try reflexivity. autounfold; omega.
          intros. rewrite Nat2Z.inj_succ, succ_plus_1 in nrange.
          assert(range: 0 <= Z.of_nat n < 2) by omega.
          simpl in *. repeat autounfold in *. simpl_hyp loopH. destruct p0.
          exploit (IHn z2 z3 range). reflexivity. intros (loop0 & t0 & r0). rewrite loop0. srewrite.
          simpl in *. bool_rel_all.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          repeat simpl_hyp loopH; contra; inv loopH; split_and;
            first[reflexivity|rewrite Zpos_P_of_succ_nat; rewrite succ_plus_1; reflexivity|bool_rel_all; omega].
          bool_rel_all; clear_hyp.
          exploit H; try apply C3; rewrite Z2Nat.id; try omega. intros (H1 & H2 & H3). autounfold in *.
          rewrite H1. extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
          inv Hspec. eexists; split.
        Qed.

      Lemma is_smmu_range_spec_ref:
        compatsim (crel RData RData) (gensem is_smmu_range_spec) is_smmu_range_spec_low.
      Proof.
        Opaque is_smmu_range_spec.
        compatsim_simpl (@match_RData).
        exploit is_smmu_range_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent is_smmu_range_spec.
      Qed.

      Lemma handle_host_mmio_spec_exists:
        forall habd habd' labd addr index hsr f
               (Hspec: handle_host_mmio_spec addr index hsr habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', handle_host_mmio_spec0 addr index hsr labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite; simpl in *.
          srewrite. destruct_if; eexists; (split; [reflexivity| constructor; reflexivity]).
          unfold handle_host_mmio_specx in C11; autounfold in C11.
          extract_if. apply andb_true_iff; split; bool_rel_all0. reflexivity. omega. srewrite.
          destruct_if.
          repeat (simpl_hyp C11; contra); inv C11; repeat (srewrite; simpl).
          destruct_if. bool_rel_all; omega. eexists; split. reflexivity.
          constructor; destruct labd; simpl in *; srewrite. reflexivity.
          destruct_if. bool_rel_all; omega. eexists; split. reflexivity.
          constructor; destruct labd; simpl in *; srewrite. reflexivity.
          simpl_bool_eq. eexists; split. reflexivity.
          constructor; destruct labd; destruct regs; simpl in *; srewrite; reflexivity.
          repeat (simpl_hyp C11; contra); inv C11; repeat (srewrite; simpl);
            simpl_bool_eq; eexists; (split; [reflexivity| constructor; destruct labd; destruct regs; simpl in *; srewrite; reflexivity]).
        Qed.

      Lemma handle_host_mmio_spec_ref:
        compatsim (crel RData RData) (gensem handle_host_mmio_spec) handle_host_mmio_spec_low.
      Proof.
        Opaque handle_host_mmio_spec.
        compatsim_simpl (@match_RData).
        exploit handle_host_mmio_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent handle_host_mmio_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) MmioOpsAux_passthrough MmioCore.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End MmioOpsAuxProofHigh.

```
