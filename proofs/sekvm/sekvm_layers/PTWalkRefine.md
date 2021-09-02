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

Require Import HypsecCommLib.
Require Import Constants.
Require Import PTWalk.Layer.
Require Import PTAlloc.Layer.
Require Import RData.
Require Import PTWalk.Spec.
Require Import PTAlloc.Spec.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PTWalkProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := PTWalk_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := PTAlloc_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Inductive relate_npt : NPT -> NPT -> Prop :=
    | RELATE_NPT:
        forall hnpt lnpt
          (vttbr_pool_rel: pt_vttbr_pool hnpt = pt_vttbr_pool lnpt)
          (pgd_next_rel: pt_pgd_next hnpt = pt_pgd_next lnpt)
          (pgd_pool_rel: pt_pgd_pool hnpt = pt_pgd_pool lnpt)
          (pud_next_rel: pt_pud_next hnpt = pt_pud_next lnpt)
          (pud_pool_rel: pt_pud_pool hnpt = pt_pud_pool lnpt)
          (pmd_next_rel: pt_pmd_next hnpt = pt_pmd_next lnpt)
          (pmd_pool_rel: pt_pmd_pool hnpt = pt_pmd_pool lnpt),
          relate_npt hnpt lnpt.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_halt: halt hadt = halt ladt;
          id_icore: icore hadt = icore ladt;
          id_ihost: ihost hadt = ihost ladt;
          id_tstate: tstate hadt = tstate ladt;
          id_curid: curid hadt = curid ladt;
          id_cur_vmid: cur_vmid hadt = cur_vmid ladt;
          id_cur_vcpuid: cur_vcpuid hadt = cur_vcpuid ladt;
          id_regs: regs hadt = regs ladt;
          id_lock: lock hadt = lock ladt;
          id_region_cnt: region_cnt hadt = region_cnt ladt;
          id_regions: regions hadt = regions ladt;
          id_shadow_ctxts: shadow_ctxts hadt = shadow_ctxts ladt;
          id_smmu_conf: smmu_conf hadt = smmu_conf ladt;
          id_log: log hadt = log ladt;
          id_oracle: oracle hadt = oracle ladt;
          id_doracle: doracle hadt = doracle ladt;
          id_core_doracle: core_doracle hadt = core_doracle ladt;
          id_data_log: data_log hadt = data_log ladt;
          id_core_data_log: core_data_log hadt = core_data_log ladt;
          id_flatmem: flatmem (shared hadt) = flatmem (shared ladt);
          id_s2page: s2page (shared hadt) = s2page (shared ladt);
          id_core_data: core_data (shared hadt) = core_data (shared ladt);
          id_vminfos: vminfos (shared hadt) = vminfos (shared ladt);
          id_spts: spts (shared hadt) = spts (shared ladt);
          id_smmu_vmid: smmu_vmid (shared hadt) = smmu_vmid (shared ladt);
          id_npts: forall i, relate_npt (i @ (npts (shared hadt))) (i @ (npts (shared ladt)))
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
           pt_store_spec
           pt_load_spec
           alloc_pgd_page_spec
           alloc_pud_page_spec
           alloc_pmd_page_spec
           walk_pgd_spec
           walk_pgd_spec0
           walk_pud_spec
           walk_pud_spec0
           walk_pmd_spec
           walk_pmd_spec0
           walk_pte_spec
           walk_pte_spec0
           set_pmd_spec
           set_pmd_spec0
           set_pte_spec
           set_pte_spec0
           check64_spec.

      Lemma walk_pgd_spec_exists:
        forall habd habd' labd vmid vttbr addr alloc res f
          (Hspec: walk_pgd_spec vmid vttbr addr alloc habd = Some (habd', (VZ64 res)))
          (Hrel: relate_RData f habd labd),
        exists labd', walk_pgd_spec0 vmid vttbr addr alloc labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - repeat (srewrite; simpl); bool_rel_all.
          destruct_if.
          srewrite. eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
          eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
        - repeat (srewrite; simpl in *); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          simpl. extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          rewrite ZMap.gss. simpl. srewrite. simpl. srewrite.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          intros. destruct_zmap. constructor; simpl; try assumption; srewrite; try reflexivity.
          apply id_npts0.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
      Qed.

      Lemma walk_pgd_spec_ref:
        compatsim (crel RData RData) (gensem walk_pgd_spec) walk_pgd_spec_low.
      Proof.
        Opaque walk_pgd_spec.
        compatsim_simpl (@match_RData).
        exploit walk_pgd_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_pgd_spec.
      Qed.

      Lemma walk_pud_spec_exists:
        forall habd habd' labd vmid pgd addr alloc res f
          (Hspec: walk_pud_spec vmid pgd addr alloc habd = Some (habd', (VZ64 res)))
          (Hrel: relate_RData f habd labd),
        exists labd', walk_pud_spec0 vmid pgd addr alloc labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - destruct_if.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          srewrite.
          destruct_if. eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
          eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
        - eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
        - repeat (srewrite; simpl in *); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          simpl. extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          rewrite ZMap.gss. simpl. srewrite. simpl. srewrite.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          intros. destruct_zmap. constructor; simpl; try assumption; srewrite; try reflexivity.
          apply id_npts0.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
      Qed.

      Lemma walk_pud_spec_ref:
        compatsim (crel RData RData) (gensem walk_pud_spec) walk_pud_spec_low.
      Proof.
        Opaque walk_pud_spec.
        compatsim_simpl (@match_RData).
        exploit walk_pud_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_pud_spec.
      Qed.

      Lemma walk_pmd_spec_exists:
        forall habd habd' labd vmid pud addr alloc res f
          (Hspec: walk_pmd_spec vmid pud addr alloc habd = Some (habd', (VZ64 res)))
          (Hrel: relate_RData f habd labd),
        exists labd', walk_pmd_spec0 vmid pud addr alloc labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - destruct_if.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          srewrite.
          destruct_if. eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
          eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
        - eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
        - repeat (srewrite; simpl in *); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          rewrite ZMap.gss. simpl. srewrite. simpl. srewrite.
          assert(same: forall n k, Z.land (Z.lor n k) k = k).
          { intros. Z.bitwise. rewrite andb_orb_distrib_l.
            now destruct (Z.testbit n m) eqn:H1; destruct (Z.testbit k m) eqn:H2. }
          rewrite same. simpl. srewrite.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          intros. destruct_zmap. constructor; simpl; try assumption; srewrite; try reflexivity.
          apply id_npts0.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
      Qed.

      Lemma walk_pmd_spec_ref:
        compatsim (crel RData RData) (gensem walk_pmd_spec) walk_pmd_spec_low.
      Proof.
        Opaque walk_pmd_spec.
        compatsim_simpl (@match_RData).
        exploit walk_pmd_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_pmd_spec.
      Qed.

      Lemma walk_pte_spec_exists:
        forall habd labd vmid pmd addr res f
          (Hspec: walk_pte_spec vmid pmd addr habd = Some (VZ64 res))
          (Hrel: relate_RData f habd labd),
          walk_pte_spec0 vmid pmd addr labd = Some (VZ64 res).
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - destruct_if. reflexivity. reflexivity.
        - reflexivity.
        - repeat (srewrite; simpl); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          reflexivity.
      Qed.

      Lemma walk_pte_spec_ref:
        compatsim (crel RData RData) (gensem walk_pte_spec) walk_pte_spec_low.
      Proof.
        Opaque walk_pte_spec.
        compatsim_simpl (@match_RData).
        exploit walk_pte_spec_exists; eauto 1;
          refine_split; repeat (try econstructor; eauto).
        Transparent walk_pte_spec.
      Qed.

      Lemma set_pmd_spec_exists:
        forall habd habd' labd vmid pud addr pmd f
          (Hspec: set_pmd_spec vmid pud addr pmd habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_pmd_spec0 vmid pud addr pmd labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - repeat (srewrite; simpl); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          intros. destruct_zmap. constructor; simpl; try assumption; srewrite; try reflexivity.
          apply id_npts0.
      Qed.

      Lemma set_pmd_spec_ref:
        compatsim (crel RData RData) (gensem set_pmd_spec) set_pmd_spec_low.
      Proof.
        Opaque set_pmd_spec.
        compatsim_simpl (@match_RData).
        exploit set_pmd_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_pmd_spec.
      Qed.

      Lemma set_pte_spec_exists:
        forall habd habd' labd vmid pmd addr pte f
          (Hspec: set_pte_spec vmid pmd addr pte habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_pte_spec0 vmid pmd addr pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel. repeat autounfold in *.
        pose proof (id_npts0 vmid). destruct H. srewrite.
        repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
        - eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        - repeat (srewrite; simpl); bool_rel_all.
          extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          destruct_if. bool_rel_all; omega.
          eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          intros. destruct_zmap. constructor; simpl; try assumption; srewrite; try reflexivity.
          apply id_npts0.
      Qed.

      Lemma set_pte_spec_ref:
        compatsim (crel RData RData) (gensem set_pte_spec) set_pte_spec_low.
      Proof.
        Opaque set_pte_spec.
        compatsim_simpl (@match_RData).
        exploit set_pte_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_pte_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End PTWalkProofHigh.

```
