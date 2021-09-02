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

Require Import AbstractMachine.Layer.
Require Import AbstractMachine.Spec.
Require Import HypsecCommLib.
Require Import Constants.
Require Import PTAlloc.Spec.
Require Import PTAlloc.Layer.
Require Import RData.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PTAllocProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := PTAlloc_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := AbstractMachine_ops) LDATA).

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
           alloc_pgd_page_spec
           alloc_pgd_page_spec0
           alloc_pud_page_spec
           alloc_pud_page_spec0
           alloc_pmd_page_spec
           alloc_pmd_page_spec0
           get_pgd_next_spec
           set_pgd_next_spec
           get_pud_next_spec
           set_pud_next_spec
           get_pmd_next_spec
           set_pmd_next_spec
           check64_spec
           panic_spec.

      Lemma alloc_pgd_page_spec_exists:
        forall habd habd' labd vmid res f
               (Hspec: alloc_pgd_page_spec vmid habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_pgd_page_spec0 vmid labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat (srewrite; simpl); bool_rel_all.
          destruct_if. eexists; split. reflexivity. constructor. reflexivity.
          eexists; split. reflexivity.
          constructor. rewrite <- C0. destruct habd'; destruct shared; simpl; reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
        Qed.

      Lemma alloc_pgd_page_spec_ref:
        compatsim (crel HDATA LDATA) (gensem alloc_pgd_page_spec) alloc_pgd_page_spec_low.
      Proof.
        Opaque alloc_pgd_page_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_pgd_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_pgd_page_spec.
      Qed.

      Lemma alloc_pud_page_spec_exists:
        forall habd habd' labd vmid res f
               (Hspec: alloc_pud_page_spec vmid habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_pud_page_spec0 vmid labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat (srewrite; simpl); bool_rel_all.
          destruct_if. eexists; split. reflexivity. constructor. reflexivity.
          eexists; split. reflexivity.
          constructor. rewrite <- C0. destruct habd'; destruct shared; simpl; reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
        Qed.

      Lemma alloc_pud_page_spec_ref:
        compatsim (crel HDATA LDATA) (gensem alloc_pud_page_spec) alloc_pud_page_spec_low.
      Proof.
        Opaque alloc_pud_page_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_pud_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_pud_page_spec.
      Qed.

      Lemma alloc_pmd_page_spec_exists:
        forall habd habd' labd vmid res f
               (Hspec: alloc_pmd_page_spec vmid habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_pmd_page_spec0 vmid labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat (srewrite; simpl); bool_rel_all.
          destruct_if. eexists; split. reflexivity. constructor. reflexivity.
          eexists; split. reflexivity.
          constructor. rewrite <- C0. destruct habd'; destruct shared; simpl; reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          eexists; split. reflexivity. constructor. reflexivity.
        Qed.

      Lemma alloc_pmd_page_spec_ref:
        compatsim (crel HDATA LDATA) (gensem alloc_pmd_page_spec) alloc_pmd_page_spec_low.
      Proof.
        Opaque alloc_pmd_page_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_pmd_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_pmd_page_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End PTAllocProofHigh.
```
