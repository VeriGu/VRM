# MmioPTAllocRefine

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

Require Import NPTOps.Layer.
Require Import HypsecCommLib.
Require Import MmioPTAlloc.Layer.
Require Import Constants.
Require Import RData.
Require Import MmioPTAlloc.Spec.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioPTAllocProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioPTAlloc_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := NPTOps_ops) HDATA).

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
           alloc_smmu_pgd_page_spec
           alloc_smmu_pgd_page_spec0
           alloc_smmu_pmd_page_spec
           alloc_smmu_pmd_page_spec0
           get_smmu_pgd_next_spec
           set_smmu_pgd_next_spec
           get_smmu_pmd_next_spec
           set_smmu_pmd_next_spec
           check64_spec
           panic_spec.

      Lemma alloc_smmu_pgd_page_spec_exists:
        forall habd habd' labd  res f
               (Hspec: alloc_smmu_pgd_page_spec  habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_smmu_pgd_page_spec0  labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat (srewrite; simpl); bool_rel_all.
          destruct_if. simpl. eexists; split. reflexivity. constructor. reflexivity.
          eexists; split. reflexivity.
          constructor. rewrite <- C. destruct habd'; destruct shared; simpl; reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
        Qed.

      Lemma alloc_smmu_pgd_page_spec_ref:
        compatsim (crel RData RData) (gensem alloc_smmu_pgd_page_spec) alloc_smmu_pgd_page_spec_low.
      Proof.
        Opaque alloc_smmu_pgd_page_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_smmu_pgd_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_smmu_pgd_page_spec.
      Qed.

      Lemma alloc_smmu_pmd_page_spec_exists:
        forall habd habd' labd  res f
               (Hspec: alloc_smmu_pmd_page_spec  habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_smmu_pmd_page_spec0  labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat (srewrite; simpl); bool_rel_all.
          destruct_if. simpl. eexists; split. reflexivity. constructor. reflexivity.
          eexists; split. reflexivity.
          constructor. rewrite <- C. destruct habd'; destruct shared; simpl; reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
        Qed.

      Lemma alloc_smmu_pmd_page_spec_ref:
        compatsim (crel RData RData) (gensem alloc_smmu_pmd_page_spec) alloc_smmu_pmd_page_spec_low.
      Proof.
        Opaque alloc_smmu_pmd_page_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_smmu_pmd_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Opaque alloc_smmu_pmd_page_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) MmioPTAlloc_passthrough NPTOps.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End MmioPTAllocProofHigh.

```
