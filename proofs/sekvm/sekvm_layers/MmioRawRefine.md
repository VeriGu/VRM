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

Require Import MmioRaw.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioRaw.Layer.
Require Import BootOps.Layer.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioRawProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioRaw_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := BootOps_ops) HDATA).

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
           smmu_get_cbndx_spec0
           smmu_get_cbndx_spec
           get_cur_vcpuid_spec
           host_get_mmio_data_spec0
           host_dabt_get_rd_spec
           smmu_init_pte_spec
           get_shadow_ctxt_spec
           host_get_mmio_data_spec
           smmu_init_pte_spec0.

      Lemma host_get_mmio_data_spec_exists:
        forall habd labd hsr res f
               (Hspec: host_get_mmio_data_spec hsr habd = Some (VZ64 res))
               (Hrel: relate_RData f habd labd),
          host_get_mmio_data_spec0 hsr labd = Some (VZ64 res).
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra.
          simpl. extract_if. apply andb_true_iff; split; bool_rel_all; somega.
          rewrite Cond. assumption.
          assumption.
        Qed.

      Lemma host_get_mmio_data_spec_ref:
        compatsim (crel RData RData) (gensem host_get_mmio_data_spec) host_get_mmio_data_spec_low.
      Proof.
        Opaque host_get_mmio_data_spec.
        compatsim_simpl (@match_RData).
        exploit host_get_mmio_data_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent host_get_mmio_data_spec.
      Qed.

      Lemma smmu_init_pte_spec_exists:
        forall habd labd prot addr res f
               (Hspec: smmu_init_pte_spec prot addr habd = Some (VZ64 res))
               (Hrel: relate_RData f habd labd),
          smmu_init_pte_spec0 prot addr labd = Some (VZ64 res).
        Proof.
          intros; inv Hrel; repeat autounfold in *; srewrite. reflexivity.
        Qed.

      Lemma smmu_init_pte_spec_ref:
        compatsim (crel RData RData) (gensem smmu_init_pte_spec) smmu_init_pte_spec_low.
      Proof.
        Opaque smmu_init_pte_spec.
        compatsim_simpl (@match_RData).
        exploit smmu_init_pte_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent smmu_init_pte_spec.
      Qed.

      Lemma smmu_get_cbndx_spec_exists:
        forall habd labd offset res f
               (Hspec: smmu_get_cbndx_spec offset habd = Some res)
               (Hrel: relate_RData f habd labd),
          smmu_get_cbndx_spec0 offset labd = Some res.
        Proof.
          intros; inv Hrel; repeat autounfold in *; srewrite. reflexivity.
        Qed.

      Lemma smmu_get_cbndx_spec_ref:
        compatsim (crel RData RData) (gensem smmu_get_cbndx_spec) smmu_get_cbndx_spec_low.
      Proof.
        Opaque smmu_get_cbndx_spec.
        compatsim_simpl (@match_RData).
        exploit smmu_get_cbndx_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent smmu_get_cbndx_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MmioRawProofHigh.

```
