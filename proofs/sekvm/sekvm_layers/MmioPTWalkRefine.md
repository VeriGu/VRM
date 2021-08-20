# MmioPTWalkRefine

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

Require Import MmioPTWalk.Layer.
Require Import HypsecCommLib.
Require Import MmioPTAlloc.Layer.
Require Import Constants.
Require Import RData.
Require Import MmioPTWalk.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioPTAlloc.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioPTWalkProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioPTWalk_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioPTAlloc_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_icore: icore hadt = icore ladt;
          id_ihost: ihost hadt = ihost ladt;
          id_halt: halt hadt = halt ladt;
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
          id_npts: npts (shared hadt) = npts (shared ladt);
          id_s2page: s2page (shared hadt) = s2page (shared ladt);
          id_core_data: core_data (shared hadt) = core_data (shared ladt);
          id_vminfos: vminfos (shared hadt) = vminfos (shared ladt);
          id_smmu_vmid: smmu_vmid (shared hadt) = smmu_vmid (shared ladt);
          id_spt_vttbr_pool: spt_vttbr_pool (spts (shared hadt)) = spt_vttbr_pool (spts (shared ladt));
          id_spt_pgd_pool: spt_pgd_pool (spts (shared hadt)) = spt_pgd_pool (spts (shared ladt));
          id_spt_pmd_pool: spt_pmd_pool (spts (shared hadt)) = spt_pmd_pool (spts (shared ladt));
          id_spt_pgd_next: spt_pgd_next (spts (shared hadt)) = spt_pgd_next (spts (shared ladt));
          id_spt_pmd_next: spt_pmd_next (spts (shared hadt)) = spt_pmd_next (spts (shared ladt))
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
           smmu_pt_store_spec
           smmu_pt_load_spec
           alloc_smmu_pgd_page_spec
           alloc_smmu_pmd_page_spec
           walk_smmu_pgd_spec
           walk_smmu_pgd_spec0
           walk_smmu_pmd_spec
           walk_smmu_pmd_spec0
           walk_smmu_pte_spec
           walk_smmu_pte_spec0
           set_smmu_pte_spec
           set_smmu_pte_spec0
           check64_spec
           observe_spt.

      Lemma walk_smmu_pgd_spec_exists:
        forall habd habd' labd ttbr addr alloc res f
               (Hspec: walk_smmu_pgd_spec ttbr addr alloc habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', walk_smmu_pgd_spec0 ttbr addr alloc labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *. srewrite.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
          - repeat (srewrite; simpl); bool_rel_all.
            destruct_if.
            srewrite. eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
            eexists; split. reflexivity. constructor; try assumption; srewrite; try reflexivity.
          - repeat (srewrite; simpl in *); bool_rel_all.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            simpl. extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            repeat (simpl; srewrite).
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          - repeat (srewrite; simpl in *); bool_rel_all.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            simpl. extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            simpl. eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        Qed.

      Lemma walk_smmu_pgd_spec_ref:
        compatsim (crel RData RData) (gensem walk_smmu_pgd_spec) walk_smmu_pgd_spec_low.
      Proof.
        Opaque walk_smmu_pgd_spec.
        compatsim_simpl (@match_RData).
        exploit walk_smmu_pgd_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_smmu_pgd_spec.
      Qed.

      Lemma walk_smmu_pmd_spec_exists:
        forall habd habd' labd pgd addr alloc res f
               (Hspec: walk_smmu_pmd_spec pgd addr alloc habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', walk_smmu_pmd_spec0 pgd addr alloc labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *. srewrite.
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
          - extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            destruct_if. bool_rel_all; omega.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        Qed.

      Lemma walk_smmu_pmd_spec_ref:
        compatsim (crel RData RData) (gensem walk_smmu_pmd_spec) walk_smmu_pmd_spec_low.
      Proof.
        Opaque walk_smmu_pmd_spec.
        compatsim_simpl (@match_RData).
        exploit walk_smmu_pmd_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_smmu_pmd_spec.
      Qed.

      Lemma walk_smmu_pte_spec_exists:
        forall habd labd pmd addr res f
               (Hspec: walk_smmu_pte_spec pmd addr habd = Some (VZ64 res))
               (Hrel: relate_RData f habd labd),
          walk_smmu_pte_spec0 pmd addr labd = Some (VZ64 res).
        Proof.
          intros. inv Hrel. repeat autounfold in *. srewrite.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
          - destruct_if. reflexivity. reflexivity.
          - reflexivity.
          - repeat (srewrite; simpl); bool_rel_all.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            destruct_if. bool_rel_all; omega.
            destruct_if. bool_rel_all; omega.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite].
            reflexivity.
        Qed.

      Lemma walk_smmu_pte_spec_ref:
        compatsim (crel RData RData) (gensem walk_smmu_pte_spec) walk_smmu_pte_spec_low.
      Proof.
        Opaque walk_smmu_pte_spec.
        compatsim_simpl (@match_RData).
        exploit walk_smmu_pte_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_smmu_pte_spec.
      Qed.

      Lemma set_smmu_pte_spec_exists:
        forall habd habd' labd pmd addr pte f
               (Hspec: set_smmu_pte_spec pmd addr pte habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_smmu_pte_spec0 pmd addr pte labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel. repeat autounfold in *. srewrite.
          repeat (simpl_hyp Hspec; contra); inv Hspec; repeat destruct_con0.
          - eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
          - repeat (srewrite; simpl); bool_rel_all.
            extract_if; [try (apply andb_true_iff; split); bool_rel; trivial; somega|srewrite]. simpl.
            destruct_if. bool_rel_all; omega.
            destruct_if. bool_rel_all; omega.
            eexists; split. reflexivity. constructor; simpl; try assumption; srewrite; try reflexivity.
        Qed.

      Lemma set_smmu_pte_spec_ref:
        compatsim (crel RData RData) (gensem set_smmu_pte_spec) set_smmu_pte_spec_low.
      Proof.
        Opaque set_smmu_pte_spec.
        compatsim_simpl (@match_RData).
        exploit set_smmu_pte_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_smmu_pte_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) MmioPTWalk_passthrough MmioPTAlloc.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End MmioPTWalkProofHigh.

```
