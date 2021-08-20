# NPTWalkRefine

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

Require Import AbstractMachine.Spec.
Require Import PTWalk.Spec.
Require Import NPTWalk.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import NPTWalk.Spec.
Require Import PTWalk.Layer.
Require Import RData.
Require Import NPTWalk.ProofHighAux.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section NPTWalkProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := NPTWalk_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := PTWalk_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
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
          id_halt: halt hadt = halt ladt;
          id_flatmem: flatmem (shared hadt) = flatmem (shared ladt);
          id_s2page: s2page (shared hadt) = s2page (shared ladt);
          id_core_data: core_data (shared hadt) = core_data (shared ladt);
          id_vminfos: vminfos (shared hadt) = vminfos (shared ladt);
          id_spts: spts (shared hadt) = spts (shared ladt);
          id_smmu_vmid: smmu_vmid (shared hadt) = smmu_vmid (shared ladt);
          id_npts: (halt ladt = false) -> forall i, relate_npt i (i @ (npts (shared hadt))) (i @ (npts (shared ladt)))
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

      Lemma local_mmap_loop_512:
        forall gfn_pmd pfn pte pt pt' gfn' pfn'
          (Hmap: local_mmap_loop (Z.to_nat 512) (gfn_pmd * 512) pfn 2 pte pt = Some (gfn', pfn', pt')),
        forall gfn' (Hvalid: valid_addr (gfn_pmd * 512 * PAGE_SIZE))
          (Hvalid': valid_addr (gfn' * PAGE_SIZE)),
          (gfn' / PTRS_PER_PMD = gfn_pmd -> gfn' @ pt' = (pfn + (gfn' - gfn_pmd * 512), 2, pte)) /\
          (gfn' / PTRS_PER_PMD <> gfn_pmd -> gfn' @ pt' = gfn' @ pt).
      Admitted.

      Hint Unfold
           get_pt_vttbr_spec
           walk_pgd_spec
           walk_pud_spec
           walk_pmd_spec
           walk_pte_spec
           set_pmd_spec
           set_pte_spec
           check64_spec
           check_spec
           panic_spec.

      Lemma get_npt_level_spec_exists:
        forall habd labd vmid addr res f
          (Hspec: get_npt_level_spec vmid addr habd = Some res)
          (Hrel: relate_RData f habd labd),
          get_npt_level_spec0 vmid addr labd = Some res.
      Proof.
        intros. unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
        destruct Hrel. unfold get_npt_level_spec0; repeat autounfold; srewrite; simpl.
        Local Transparent Z.land. simpl. reflexivity. Local Opaque Z.land.
        pose proof phys_page_or_not_change as phys_or.
        rename C2 into Hhalt.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        simpl_hyp Hspec; contra. destruct b; contra.
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        simpl_hyp Hspec. simpl_hyp Hspec.
        exploit (Hrelate0 z z1 z2 z0). autounfold; bool_rel_all; omega.
        assumption. intro T; destruct T.
        duplicate Hvalid. destruct D.
        destruct Hlevel as [Hlevel|Hlevel]; [|destruct Hlevel as [Hlevel|Hlevel]].
        rewrite Hlevel in Hspec. duplicate Hlevel. duplicate Hlevel. duplicate Hlevel.
        apply Hlevel0 in D. apply Hpfn0 in D0. apply Hpte0 in D1.
        clear Hlevel0 Hlevel1 Hlevel3.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. clear D. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. clear D. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct D. rewrite H. simpl.
        Local Transparent Z.land. simpl. Local Opaque Z.land.
        simpl_hyp Hspec; assumption.
        destruct H as (Hvt & D). destruct_if. bool_rel; contra.
        extract_if. clear D. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct D. rewrite H. simpl.
        Local Transparent Z.land. simpl. Local Opaque Z.land.
        simpl_hyp Hspec; assumption.
        destruct H as (Hpg & D). destruct_if. bool_rel; contra.
        extract_if. clear D. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        destruct D. rewrite H. Local Transparent Z.land. simpl. Local Opaque Z.land.
        simpl_hyp Hspec; assumption.
        destruct H as (D2 & D3 & D4). srewrite. simpl.
        destruct_if. bool_rel. rewrite Case1 in D3. inversion D3.
        extract_if. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
        destruct H. rewrite H in Case1. inversion Case1. destruct H. bool_rel; contra. destruct H as (? & ? & ?).
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H2 with _ <= _ < ?a => assert(a <= pt_pmd_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H0; assumption. omega. rewrite Cond3.
        Local Transparent Z.land. simpl. Local Opaque Z.land.
        simpl_hyp Hspec; assumption.
        rewrite Hlevel in Hspec. apply Hlevel1 in Hlevel.
        destruct Hlevel as (D1 & D2 & D3 & D4). clear Hlevel0 Hlevel1 Hlevel3 Hpfn0 Hpfn2.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        destruct_if. bool_rel; srewrite; contra. rewrite D3; assumption.
        rewrite Hlevel in Hspec. apply Hlevel3 in Hlevel.
        destruct Hlevel as (D1 & D2 & D3 & D4 & D5). simpl in D5.
        clear Hlevel0 Hlevel1 Hlevel3 Hpfn0 Hpfn2 Hpte0 Hpfn3.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        srewrite. simpl. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
        destruct H. rewrite H in Case1. inversion Case1. destruct H. bool_rel; contra. destruct H as (? & ? & ?).
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H2 with _ <= _ < ?a => assert(a <= pt_pmd_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H0; assumption. omega. rewrite Cond3.
        rewrite Hpmd_pool_range. rewrite Hpmd_pool_range. rewrite D5; assumption.
      Qed.

      Lemma walk_npt_spec_exists:
        forall habd labd vmid addr res f
          (Hspec: walk_npt_spec vmid addr habd = Some (VZ64 res))
          (Hrel: relate_RData f habd labd),
          walk_npt_spec0 vmid addr labd = Some (VZ64 res).
      Proof.
        intros. unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
        destruct Hrel. unfold walk_npt_spec0; repeat autounfold; srewrite; simpl.
        Local Transparent Z.land. simpl. inv Hspec. reflexivity. Local Opaque Z.land.
        pose proof phys_page_or_not_change as phys_or.
        rename C2 into Hhalt.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        simpl_hyp Hspec; contra. destruct b; contra.
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        simpl_hyp Hspec. simpl_hyp Hspec.
        exploit (Hrelate0 z z1 z2 z0). autounfold; bool_rel_all; omega.
        assumption. intro T; destruct T.
        duplicate Hvalid. destruct D.
        destruct Hlevel as [Hlevel|Hlevel]; [|destruct Hlevel as [Hlevel|Hlevel]].
        duplicate Hlevel. duplicate Hlevel. duplicate Hlevel.
        apply Hlevel0 in D. apply Hpfn0 in D0. apply Hpte0 in D1.
        clear Hlevel0 Hlevel1 Hlevel3.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. clear D. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. clear D. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct D. rewrite H. simpl.
        Local Transparent Z.land. simpl. Local Opaque Z.land.
        simpl_hyp Hspec; assumption.
        destruct H as (Hvt & D). destruct_if. bool_rel; contra.
        extract_if. clear D. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct D. rewrite H. simpl.
        Local Transparent Z.land. simpl. Local Opaque Z.land.
        assumption. destruct H as (Hpg & D). destruct_if. bool_rel; contra.
        extract_if. clear D. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        destruct D. rewrite H. Local Transparent Z.land. simpl. Local Opaque Z.land.
        assumption. destruct H as (D2 & D3 & D4). srewrite. simpl.
        destruct_if. bool_rel. rewrite Case1 in D3. inversion D3.
        extract_if. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
        destruct H. rewrite H in Case1. inversion Case1. destruct H. bool_rel; contra. destruct H as (? & ? & ?).
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H2 with _ <= _ < ?a => assert(a <= pt_pmd_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H0; assumption. omega. rewrite Cond3.
        Local Transparent Z.land. simpl. Local Opaque Z.land. assumption.
        apply Hlevel1 in Hlevel.
        destruct Hlevel as (D1 & D2 & D3 & D4). clear Hlevel0 Hlevel1 Hlevel3 Hpfn0 Hpfn2.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        destruct_if. bool_rel; srewrite; contra. rewrite D3; assumption.
        apply Hlevel3 in Hlevel.
        destruct Hlevel as (D1 & D2 & D3 & D4 & D5). simpl in D5.
        clear Hlevel0 Hlevel1 Hlevel3 Hpfn0 Hpfn2 Hpte0 Hpfn3.
        repeat autounfold in *; simpl in *; srewrite.
        clear_hyp. bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align. rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr0 PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        rewrite Hvttbr_pool_range.
        rewrite andb_comm. simpl. rewrite Hvttbr_pool_range.
        destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. srewrite; assumption.
        destruct H; srewrite; assumption. srewrite; omega. rewrite Cond1.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl.
        rewrite Hpgd_pool_range. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. rewrite Hpud_pool_range.
        srewrite. simpl. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
        destruct H. rewrite H in Case1. inversion Case1. destruct H. bool_rel; contra. destruct H as (? & ? & ?).
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H2 with _ <= _ < ?a => assert(a <= pt_pmd_next lnpt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H0; assumption. omega. rewrite Cond3. rewrite <- D5.
        rewrite Hpmd_pool_range. inv Hspec. rewrite <- H0.
        rewrite Hpmd_pool_range. reflexivity.
      Qed.

      Lemma set_npt_spec_1_pgd_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 2)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10. simpl_bool_eq. clear C8. rename C10 into Hspec.
        rewrite Hpgd in Hspec.
        assert (Hpud: (pud_index addr) @ ((pgd_index addr) @ (pud_t vmid @ (npts (shared habd)))) = false).
        { match goal with | |- ?x = false => destruct x eqn: Hpud end.
          apply Hpud_t in Hpud. destruct Hpud. apply Hpgd_t in H. contra.
          bool_rel_all; omega. bool_rel_all; omega. reflexivity. }
        rewrite Hpud in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0.
        repeat autounfold in *.
        autounfold. rewrite Hhaltl. rewrite Hlock. rewrite C1. rewrite C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond2.
        destruct_if.
        duplicate Cond2. rename D into Cond3.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond4.
        rewrite Hhaltl, Hlock.
        match goal with |- context [?c =? 0] => assert(c =? 0 = false) end.
        bool_rel. apply or3nz. rewrite H. clear H.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond5.
        rewrite ZMap.gss. simpl. extract_if. apply Hpgd_pool_range. rewrite Cond6.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond7.
        destruct_if.
        duplicate Cond7. rename D into Cond8.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond9.
        rewrite Hhaltl, Hlock, Htstate. simpl. destruct_if. bool_rel; contra.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond10.
        rewrite Hnext_pgd, Hnext_pud, Case0, Case2 in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec. destruct p. destruct p.
        pose proof (local_mmap_loop_512 _ _ _ _ _ _ _ C7) as hset_npt.
        inv Hspec. clear Cond3 Cond8.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + eapply phys_page_a_page. assumption. omega.
            + eapply phys_page_a_page. assumption. omega.
            + assumption.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + apply Hpmd_next. assumption.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hvttbr_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hpgd_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. left. assumption.
              pose proof (Hpud_pool addr0). destruct H. left; assumption.
              destruct H. right; left; assumption.
              destruct H as (? & ? & ?). right; right. split. assumption.
              split. omega. assumption.
          - reflexivity. - reflexivity. - assumption.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            pose proof (hset_npt (addr' / 4096)). autounfold in *.
            repeat (destruct_con; contra); bool_rel.
            destruct ((addr' / 4096 / 512 =? addr / 4096 / 512)) eqn:cases; bool_rel.
            apply H1 in cases. rewrite cases in Hpte'. inversion Hpte'. reflexivity.
            apply div_mul_pmd_addr. autounfold; omega.
            apply div_mul_page_addr. autounfold; omega.
            exploit (pmd_same_cond addr0 addr'); try (autounfold; assumption).
            autounfold; intro S. duplicate cases. destruct S as (S1 & S2).
            rewrite <- S1 in D; try (split_and; assumption).
            pose proof (hset_npt (addr0 / 4096)). autounfold in *.
            apply H2 in D. rewrite D in Hpte.
            apply H1 in cases. rewrite cases in Hpte'.
            eapply H0. eassumption. eassumption. assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss. split; try reflexivity. intro. apply or3nz.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). apply Hpgd_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. repeat rewrite ZMap.gss. split; try reflexivity.
            intros. split_and; try rewrite phys_or; try solve [assumption|omega].
            apply or3nz. apply or3nz.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). repeat rewrite phys_or; try solve [assumption|omega].
            split; intros. rewrite <- Hpgd_same in H. apply Hpud_t in H.
            destruct H as (? & ?). rewrite Hpgd_same in H. omega. assumption.
            destruct H as (? & ?). match type of H0 with ?c -> False => assert(c) end.
            rewrite Hpgd_next. reflexivity.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega.
            apply H0 in H1; inversion H1.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption. right. assumption.
            rewrite (ZMap.gso _ _ Hneq).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed. left.
            match goal with
            | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared labd)))]] =>
              pose proof (Hvttbr_pool a)
            end.
            destruct H. rewrite H. match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
            rewrite phys_page_or_not_change. omega. assumption. assumption.
            destruct H. rewrite phys_page_or_not_change. omega. assumption. assumption.
            rewrite (ZMap.gso _ _ Hneq0). apply Hpud_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split; intros; contra. destruct H as (? & ? & ? & ?); contra.
            repeat rewrite (ZMap.gso _ _ Hpmd_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            split; intro. rewrite <- Hpgd_same, <- Hpud_same in H; apply (Hpmd_t _ ge0) in H.
            destruct H as (? & ? & ?); rewrite Hpgd_same, Hpud_same in *; contra.
            destruct H as (? & ? & ? & ?).
            match type of H2 with
            | context[?a @ (pt_pud_pool vmid @ (npts (shared labd)))] =>
              assert(a @ (pt_pud_pool vmid @ (npts (shared labd))) = 0)
            end.
            eapply Hpud_next. rewrite phys_or; try assumption; try omega.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega. apply H2 in H3; inversion H3.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            assert_gso. repeat (rewrite phys_or; try assumption; try omega).
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0).
            split; intro. rewrite <- Hpgd_same in H; apply (Hpmd_t _ ge0) in H.
            destruct H as (? & ? & ?); rewrite Hpgd_same in *; contra.
            destruct H as (? & ? & ? & ?). rewrite Hpgd_next in H0. contra.
            rewrite phys_or; try assumption; try omega.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption.
            right. assumption. repeat rewrite (ZMap.gso _ _ Hneq).
            assert_gso. repeat rewrite phys_or; try assumption; try omega.
            eapply vttbr_pool_ne_pgd_next; try eassumption. autounfold; somega. autounfold; somega.
            repeat rewrite (ZMap.gso _ _ Hneq0).
            assert_gso. rewrite phys_or; try assumption; try omega.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq1). apply Hpmd_t. assumption.
          - intros. bool_rel_all. repeat autounfold in *.
            destruct (addr0 / 4096 / 512 =? addr / 4096 / 512) eqn:Hpmds; bool_rel.
            + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
              eapply hset_npt in D. rewrite Hhpt in D. inversion D.
              apply H in D0. destruct D0 as (? & ? & ?). repeat autounfold in *.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro; simpl; rewrite Hpmds. split_and. reflexivity.
              intro T; inversion T. intro T; inversion T. intro. simpl.
              srewrite; repeat rewrite ZMap.gss.
              split_and. apply or3nz. apply or3nz. reflexivity. assumption.
              intro T; inversion T. assumption. autounfold; split; assumption.
              apply div_mul_pmd_addr. autounfold; split; assumption.
              apply div_mul_page_addr. autounfold; assumption.
            + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
              eapply hset_npt in D. rewrite Hhpt in D.
              assert(valid_addr addr) by (autounfold; split; omega).
              pose proof (H Hvalid0 H0). clear H. symmetry in D.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 D). destruct H.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
                apply Hpfn0 in D1. apply Hpte0 in D2. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. right.
                split. apply or3nz.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. assert(addr0 / 4096 / 512 = addr / 4096 / 512) by
                    (apply H1; split_and; solve[assumption|reflexivity]). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or; try assumption. apply Hpud_next.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range. generalize Hcond3, Hpud_next_range.
                repeat match goal with [H: _ |- _] => clear H end; intros; omega. assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or; try assumption. apply Hpgd_next.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range. generalize Hcond3, Hpgd_next_range.
                repeat match goal with [H: _ |- _] => clear H end; intros; omega. assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assert_gso. apply or_index_ne_cond; try assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption.  eapply vttbr_pool_ne_pgd_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T4 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
              * simpl. intro T. duplicate T. apply Hlevel1 in T. apply Hpfn2 in D1. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. destruct T. contra.
                assert_gso. apply or_index_ne_cond; try assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T2 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply vttbr_pool_ne_pgd_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as (T3 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D1. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. destruct T. contra.
                assert_gso. apply or_index_ne_cond; try assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply vttbr_pool_ne_pgd_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
              * apply div_mul_pmd_addr. autounfold; split; assumption.
              * apply div_mul_page_addr. autounfold; assumption.
        }
        apply Hrelate. inversion C0.
        Local Transparent Z.land. simpl.
        srewrite. rewrite Case2 in Hspec. rewrite andb_comm in Hspec. simpl in Hspec.
        repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        erewrite Hpgd_next in Case1. inversion Case1.
        rewrite phys_or; try assumption.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. assumption. autounfold; somega. omega.
        simpl. srewrite. rewrite Case0 in Hspec. simpl in Hspec. inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        bool_rel. apply Hpgd_t in Case. contra. assumption.
        Local Opaque Z.land.
      Qed.

      Lemma set_npt_spec_1_pud_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 2)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = true end)
          (Hpud: match addr with VZ64 addr => (pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10. simpl_bool_eq. clear C8. rename C10 into Hspec.
        rewrite Hpgd in Hspec. rewrite Hpud in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0.
        repeat autounfold in *.
        autounfold. rewrite Hhaltl. rewrite Hlock. rewrite C1. rewrite C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        apply Hpgd_t in Hpgd; try omega. bool_rel; assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond3.
        destruct_if.
        duplicate Cond3. rename D into Cond4.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond5.
        rewrite Hhaltl, Hlock, Htstate. simpl. destruct_if. bool_rel; contra.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond6.
        rewrite Hnext_pgd, Hnext_pud, Case1 in Hspec.
        assert((pt_pgd_next vmid @ (npts (shared labd)) <=? 65536 + 33554432 * vmid + 1052672) = true).
        { bool_rel; omega. } rewrite H in Hspec. clear H.
        simpl_hyp Hspec. simpl_hyp Hspec. destruct p. destruct p.
        pose proof (local_mmap_loop_512 _ _ _ _ _ _ _ C7) as hset_npt.
        inv Hspec. clear Cond4.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + assumption.
            + eapply phys_page_a_page. assumption. omega.
            + assumption.
            + assert_gso. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity. reflexivity. autounfold; somega. omega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + apply Hpmd_next. assumption.
            + apply Hvttbr_pool.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hpgd_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. left. assumption.
              pose proof (Hpud_pool addr0). destruct H. left; assumption.
              destruct H. right; left; assumption.
              destruct H as (? & ? & ?). right; right. split. assumption.
              split. omega. assumption.
          - reflexivity. - reflexivity. - assumption.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            pose proof (hset_npt (addr' / 4096)). autounfold in *.
            repeat (destruct_con; contra); bool_rel.
            destruct ((addr' / 4096 / 512 =? addr / 4096 / 512)) eqn:cases; bool_rel.
            apply H1 in cases. rewrite cases in Hpte'. inversion Hpte'. reflexivity.
            apply div_mul_pmd_addr. autounfold; omega.
            apply div_mul_page_addr. autounfold; omega.
            exploit (pmd_same_cond addr0 addr'); try (autounfold; assumption).
            autounfold; intro S. duplicate cases. destruct S as (S1 & S2).
            rewrite <- S1 in D; try (split_and; assumption).
            pose proof (hset_npt (addr0 / 4096)). autounfold in *.
            apply H2 in D. rewrite D in Hpte.
            apply H1 in cases. rewrite cases in Hpte'.
            eapply H0. eassumption. eassumption. assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
          - intros; autounfold.
            match goal with |- context[?a @ (?b # ?c == true)] => assert(a @ (b # c == true) = a @ b) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. rewrite Hpgd; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same); reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. repeat rewrite ZMap.gss. split; try reflexivity.
            intros. split_and; try rewrite phys_or; try solve [assumption|omega]. apply or3nz.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            split; intros. rewrite <- Hpgd_same in H. apply Hpud_t in H. rewrite Hpgd_same in H. apply H.
            assumption. simpl.  rewrite <- Hpgd_same. apply Hpud_t. assumption.
            rewrite <- Hpgd_same in H. apply H. repeat rewrite (ZMap.gso _ _ Hpgd_same).
            split; intros. apply Hpud_t in H.
            destruct H as (? & ?).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq).
            split_and; assumption. assumption. destruct H as (? & ?).
            assert_gsoH H0. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq) in H0.
            apply Hpud_t. assumption. split_and; assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split. intro T; inversion T. intros (? & ? & ? & ?). contra.
            repeat rewrite (ZMap.gso _ _ Hpmd_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            split. intro T. rewrite <- Hpgd_same, <- Hpud_same in T. apply Hpmd_t in T.
            destruct T as (T1 & T2 & T3 & T4). rewrite Hpgd_same, Hpud_same in T2. contra. assumption.
            intros (? & ? & ? & ?).
            match type of H2 with
            | context[?a @ (pt_pud_pool vmid @ (npts (shared labd)))] => assert(a @ (pt_pud_pool vmid @ (npts (shared labd))) = 0)
            end.
            eapply Hpud_next. rewrite phys_or; try assumption; try omega.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega. contra.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            assert_gso. repeat (rewrite phys_or; try assumption; try omega).
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). rewrite <- Hpgd_same. apply Hpmd_t. assumption.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            split. intro T. apply Hpmd_t in T. destruct T as (T1 & T2 & T3 & T4).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq).
            assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
            autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). split_and; assumption. assumption.
            intros (T1 & T2 & T3 & T4).
            assert_gsoH T4. assert_gso.
            eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq).
            rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
            autounfold; somega. autounfold; somega. repeat rewrite (ZMap.gso _ _ Hneq) in T3, T4.
            assert_gsoH T4. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq0) in T2, T3, T4.
            apply Hpmd_t. assumption. try split_and; try assumption.
          - intros. bool_rel_all. repeat autounfold in *.
            destruct (addr0 / 4096 / 512 =? addr / 4096 / 512) eqn:Hpmds; bool_rel.
            + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
              eapply hset_npt in D. rewrite Hhpt in D. inversion D.
              apply H in D0. destruct D0 as (? & ? & ?). repeat autounfold in *.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro; simpl; rewrite Hpmds. split_and. reflexivity.
              intro T; inversion T. intro T; inversion T.
              intro. simpl. srewrite; repeat rewrite ZMap.gss.
              split_and. assumption. apply or3nz. reflexivity. assumption.
              intro T; inversion T. assumption. autounfold; split; assumption.
              apply div_mul_pmd_addr. autounfold; split; assumption.
              apply div_mul_page_addr. autounfold; assumption.
            + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
              eapply hset_npt in D. rewrite Hhpt in D.
              assert(valid_addr addr) by (autounfold; split; omega).
              pose proof (H Hvalid0 H0). clear H. symmetry in D.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 D). destruct H.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
                apply Hpfn0 in D1. apply Hpte0 in D2. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                assert(addr0 / 4096 / 512 = addr / 4096 / 512) by
                    (apply H1; split_and; solve[assumption|reflexivity]). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or; try assumption. unfold pmd_index.  eapply pud_pool_next_zero; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as [T|T]. left; assumption. right.
                destruct T as (T4 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                rewrite (ZMap.gso _ _ Hneq0). assumption.
                destruct T as [T|T]. left; assumption. right.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pgd_index_diff_res_diff; try eassumption. apply T.
                rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T3 & T); split; try assumption.
                destruct T as [T|T]. left; assumption. right.
                destruct T as (T4 & T). split; try assumption.
                assert_gso. rewrite phys_or; try assumption.  eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
              * simpl. intro T. duplicate T. apply Hlevel1 in T. apply Hpfn2 in D1. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                rewrite Hpgd_same, Hpud_same in *. destruct T as (T3 & T4 & T5). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pgd_index_diff_res_diff; try eassumption. apply T. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D1. simpl in T.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                rewrite Hpgd_same, Hpud_same in *. destruct T as (T3 & T4 & T5 & T6). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pgd_index_diff_res_diff; try eassumption. apply T. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
              * apply div_mul_pmd_addr. autounfold; split; assumption.
              * apply div_mul_page_addr. autounfold; assumption.
        }
        apply Hrelate. inversion C0.
        Local Transparent Z.land. rewrite Hnext_pud in Hspec.
        rewrite Case1 in Hspec. rewrite andb_comm in Hspec. simpl in Hspec. inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        bool_rel. assert((pud_index addr) @ ((pgd_index addr) @ (pud_t vmid @ (npts (shared habd)))) = true).
        apply Hpud_t. assumption. split; assumption. contra.
        Local Opaque Z.land.
      Qed.

      Lemma set_npt_spec_1_pmd_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 2)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = true end)
          (Hpud: match addr with VZ64 addr => (pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = true end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10. simpl_bool_eq. clear C8. rename C10 into Hspec.
        rewrite Hpgd, Hpud in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0. simpl.
        repeat autounfold in *.
        rewrite Hhaltl, Hlock, C1. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        apply Hpgd_t in Hpgd; try omega. bool_rel; assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        apply Hpud_t in Hpud; try omega. destruct Hpud; bool_rel; omega.
        rewrite Hpgd_pool_range. rewrite Htstate, Hhaltl, Hlock. simpl. destruct_if. bool_rel; contra.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond3.
        repeat simpl_hyp Hspec; inv Hspec.
        pose proof (local_mmap_loop_512 _ _ _ _ _ _ _ C7) as hset_npt.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + apply Hvttbr_pool_range.
            + apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + assumption. + assumption. + assumption.
            + apply Hpgd_next. assumption.
            + assert_gso. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity. reflexivity. autounfold; somega. omega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= pt_pud_next vmid @ (npts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + apply Hpmd_next. assumption.
            + apply Hvttbr_pool.
            + apply Hpgd_pool.
            + destruct_zmap. right. left. assumption.
              pose proof (Hpud_pool addr0). destruct H. left; assumption.
              destruct H. right; left; assumption.
              destruct H as (? & ? & ?). right; right. split. assumption.
              split. omega. assumption.
          - assumption. - assumption. - assumption.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            pose proof (hset_npt (addr' / 4096)). autounfold in *.
            repeat (destruct_con; contra); bool_rel.
            destruct ((addr' / 4096 / 512 =? addr / 4096 / 512)) eqn:cases; bool_rel.
            apply H1 in cases. rewrite cases in Hpte'. inversion Hpte'. reflexivity.
            apply div_mul_pmd_addr. autounfold; omega.
            apply div_mul_page_addr. autounfold; omega.
            exploit (pmd_same_cond addr0 addr'); try (autounfold; assumption).
            autounfold; intro S. duplicate cases. destruct S as (S1 & S2).
            rewrite <- S1 in D; try (split_and; assumption).
            pose proof (hset_npt (addr0 / 4096)). autounfold in *.
            apply H2 in D. rewrite D in Hpte.
            apply H1 in cases. rewrite cases in Hpte'.
            eapply H0. eassumption. eassumption. assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
            apply div_mul_pmd_addr. autounfold; split; assumption.
            apply div_mul_page_addr. autounfold; assumption.
          - intros; autounfold.
            match goal with |- context[?a @ (?b # ?c == true)] => assert(a @ (b # c == true) = a @ b) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. rewrite Hpgd; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same); reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = (pud_index addr0) @ ((pgd_index addr0) @ (pud_t vmid @ (npts (shared habd))))) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. rewrite ZMap.gss. rewrite Hpud. reflexivity.
            rewrite (ZMap.gso _ _ Hpud_same). reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). reflexivity.
            rewrite H. apply Hpud_t. assumption.
          - intros; autounfold.
            destruct ((pgd_index addr0) =? (pgd_index addr)) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct ((pud_index addr0) =? (pud_index addr)) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct ((pmd_index addr0) =? (pmd_index addr)) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split. intro T; inversion T.
            intros (? & ? & ? & ?). contra.
            repeat rewrite (ZMap.gso _ _ Hpmd_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. repeat rewrite (ZMap.gso _ _ Hneq).
            rewrite <- Hpgd_same, <- Hpud_same. apply Hpmd_t. assumption.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            split. intro T. rewrite <- Hpgd_same in T. apply Hpmd_t in T.
            destruct T as (? & ? & ? & ?).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. rewrite <- Hpgd_same at 1. autounfold. eapply pud_index_diff_res_diff; try eassumption. right; assumption.
            rewrite (ZMap.gso  _ _ Hneq). rewrite Hpgd_same in *. split_and; assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H2. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. autounfold. rewrite <- Hpgd_same at 1. autounfold in *.
            eapply pud_index_diff_res_diff; autounfold; try rewrite Hpgd_same; try eassumption.
            right; assumption. rewrite (ZMap.gso _ _ Hneq) in H1, H2.
            rewrite <- Hpgd_same; apply Hpmd_t. assumption. rewrite Hpgd_same in *; split_and; assumption.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            split. intro T. apply Hpmd_t in T. destruct T as (? & ? & ? & ?).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. autounfold. eapply pud_index_diff_res_diff; try eassumption. left; assumption.
            rewrite (ZMap.gso  _ _ Hneq). split_and; assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H2. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. autounfold. eapply pud_index_diff_res_diff; try eassumption.
            left; assumption. rewrite (ZMap.gso _ _ Hneq) in H1, H2. apply Hpmd_t. assumption.
            split_and; assumption.
          - intros. bool_rel_all. repeat autounfold in *.
            destruct (addr0 / 4096 / 512 =? addr / 4096 / 512) eqn:Hpmds; bool_rel.
            + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
              eapply hset_npt in D. rewrite Hhpt in D. inversion D.
              apply H in D0. destruct D0 as (? & ? & ?). repeat autounfold in *.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro; simpl; rewrite Hpmds. reflexivity.
              intro T; inversion T. intro T; inversion T.
              intro; simpl. srewrite. split_and; try assumption.
              rewrite ZMap.gss. reflexivity. intro T; inversion T. assumption.
              autounfold; split; assumption.
              apply div_mul_pmd_addr. autounfold; split; assumption.
              apply div_mul_page_addr. autounfold; assumption.
          + pose proof (pmd_same_cond addr0 addr). duplicate Hpmds. duplicate Hpmds.
            eapply hset_npt in D. rewrite Hhpt in D.
            assert(valid_addr addr) by (autounfold; split; omega).
            pose proof (H Hvalid0 H0). clear H. symmetry in D.
            pose proof (Hrelate0 _ _ _ _ Hvalid0 D). destruct H.
            constructor; try assumption.
            * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
              apply Hpfn0 in D1. apply Hpte0 in D2.
              simpl in T. destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T2 & T); split; try assumption.
              destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
              rewrite Hpgd_same in *. repeat rewrite ZMap.gss.
              destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T3 & T); split; try assumption.
              destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
              autounfold in *. repeat rewrite Hpud_same in *; repeat rewrite ZMap.gss.
              destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
              assert(addr0 / 4096 / 512 = addr / 4096 / 512) by
                  (apply H1; split_and; solve[assumption|reflexivity]).
              apply Hpmds in H; inversion H.
              assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
              right; assumption. repeat rewrite (ZMap.gso _ _ Hneq). assumption.
              assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
              left. rewrite <- Hpgd_same at 1.
              eapply pud_index_diff_res_diff; try rewrite Hpgd_same; try eassumption.
              right; assumption. repeat rewrite (ZMap.gso _ _ Hneq); assumption.
              destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T3 & T); split; try assumption.
              assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
              left. autounfold; eapply pud_index_diff_res_diff; try eassumption. left; assumption.
              repeat rewrite (ZMap.gso _ _ Hneq). assumption.
            * simpl. intro T. duplicate T. apply Hlevel1 in T. apply Hpfn2 in D1.
              simpl in T. autounfold in *. destruct T as (T1 & T2 & T3 & T4).
              split. assumption. split. assumption.
              assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
              destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
              left. autounfold; eapply pud_index_diff_res_diff; try eassumption.
              destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
              destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
              assert(addr0 / 4096 / 512 = addr / 4096 / 512) by
                  (apply H1; split_and; solve[assumption|reflexivity]).
              apply Hpmds in H; inversion H.
              right; assumption. left; assumption.
              right; assumption. repeat rewrite (ZMap.gso _ _ Hneq). split; assumption.
            * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D1.
              simpl in T. autounfold in *. destruct T as (T1 & T2 & T3 & T4 & T5).
              split. assumption. split. assumption.
              assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
              destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
              left. autounfold; eapply pud_index_diff_res_diff; try eassumption.
              destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
              destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
              assert(addr0 / 4096 / 512 = addr / 4096 / 512) by
                  (apply H1; split_and; solve[assumption|reflexivity]).
              apply Hpmds in H; inversion H. right; assumption. left; assumption.
              right; assumption. repeat rewrite (ZMap.gso _ _ Hneq). split_and; assumption.
            * apply div_mul_pmd_addr. autounfold; split; assumption.
            * apply div_mul_page_addr. autounfold; assumption.
        }
        apply Hrelate.
        bool_rel_all; try omega.
      Qed.

      Lemma set_npt_spec_2_pgd_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 3)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10; simpl in C10. clear C8. rename C10 into Hspec.
        rewrite Hpgd in Hspec.
        assert (Hpud: (pud_index addr) @ ((pgd_index addr) @ (pud_t vmid @ (npts (shared habd)))) = false).
        { match goal with | |- ?x = false => destruct x eqn: Hpud end.
          apply Hpud_t in Hpud. destruct Hpud. apply Hpgd_t in H. contra.
          bool_rel_all; omega. bool_rel_all; omega. reflexivity. }
        rewrite Hpud in Hspec.
        assert (Hpmd: (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t vmid @ (npts (shared habd))))) = false).
        { match goal with | |- ?x = false => destruct x eqn: Hpmd end.
          apply Hpmd_t in Hpmd. destruct Hpmd as (? & ? & ?). apply Hpgd_t in H. contra.
          bool_rel_all; omega. bool_rel_all; omega. reflexivity. }
        rewrite Hpmd in Hspec.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0.
        repeat autounfold in *.
        autounfold. rewrite Hhaltl. rewrite Hlock. rewrite C1. rewrite C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond2.
        destruct_if.
        duplicate Cond2. rename D into Cond3.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond4.
        rewrite Hhaltl, Hlock.
        match goal with |- context [?c =? 0] => assert(c =? 0 = false) end.
        bool_rel. apply or3nz. rewrite H. clear H.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond5.
        rewrite ZMap.gss. simpl. extract_if. apply Hpgd_pool_range. rewrite Cond6.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond7.
        destruct_if.
        duplicate Cond7. rename D into Cond8.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond9.
        rewrite Hhaltl, Hlock.
        match goal with |- context [?c =? 0] => assert(c =? 0 = false) end.
        bool_rel. apply or3nz. rewrite H. clear H.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond10.
        rewrite ZMap.gss. simpl. extract_if. apply Hpud_pool_range. rewrite Cond11.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond12.
        destruct_if.
        duplicate Cond12. rename D into Cond13.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond14.
        rewrite Hhaltl, Hlock. rewrite and_or_same. simpl. rewrite Htstate. simpl.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond15.
        rewrite Hnext_pgd, Hnext_pud, Hnext_pmd, Case0, Case2, Case4 in Hspec. simpl in Hspec.
        simpl_hyp Hspec. destruct p. simpl_hyp Hspec.
        exploit (Hrelate0 addr z0 z1 z); try assumption; try omega. intro T; destruct T.
        bool_rel. apply Hlevel1 in C0. simpl in C0. autounfold in C0.
        destruct C0 as (? & ?). contra.
        inv Hspec. clear Cond3 Cond8 Cond13.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + eapply phys_page_a_page. assumption. omega.
            + eapply phys_page_a_page. assumption. omega.
            + eapply phys_page_a_page. assumption. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. omega.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hvttbr_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hpgd_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. right.
              repeat rewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega. apply and_or_same.
              pose proof (Hpud_pool addr0).
              destruct H as [T|T]; try (left; assumption). right.
              destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T0 & T); split; try assumption.
              destruct T as (T1 & T); split; try omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
          - reflexivity.
          - reflexivity.
          - reflexivity.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            autounfold in *. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            rewrite Hsame in *. rewrite ZMap.gss in *. rewrite H in *. inversion Hpte.
            rewrite (ZMap.gso _ _ Hsame) in Hpte.
            destruct (addr' / 4096 =? addr / 4096) eqn:Hsame'; bool_rel.
            rewrite Hsame' in *. rewrite ZMap.gss in Hpte'. assert(z1 = 2) by (eapply H0; eassumption). contra.
            rewrite (ZMap.gso _ _ Hsame') in Hpte'. eapply H0; eassumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss. split; try reflexivity. intro; apply or3nz.
            rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption. right. assumption.
            rewrite (ZMap.gso _ _ Hneq). apply Hpgd_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. repeat rewrite ZMap.gss. split; try reflexivity.
            intros. split_and; try rewrite phys_or; try assumption. apply or3nz. apply or3nz.
            rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond; try apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). repeat rewrite phys_or; try assumption.
            split; intros. rewrite <- Hpgd_same in H. apply Hpud_t in H.
            destruct H as (? & ?). rewrite Hpgd_same in H. apply H in Case. inversion Case. assumption.
            destruct H as (? & ?). match type of H0 with ?c -> False => assert(c) end.
            rewrite Hpgd_next. reflexivity.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega. apply H0 in H1; inversion H1.
            repeat rewrite (ZMap.gso _ _ Hpgd_same). repeat rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). repeat rewrite phys_or; try assumption.
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. assumption.
            left. match goal with
                  | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared labd)))]] =>
                    pose proof (Hvttbr_pool a)
                  end.
            destruct H. rewrite H. match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
            omega. destruct H. omega. rewrite (ZMap.gso _ _ Hneq0). apply Hpud_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split; intros; try reflexivity. split_and; try apply or3nz. apply and_or_same.
            repeat rewrite (ZMap.gso _ _ Hpmd_same).
            split. intro T. rewrite <- Hpgd_same, <- Hpud_same in T. apply Hpmd_t in T.
            destruct T as (? & ? & ? & ?). rewrite Hpgd_same in H. apply H in Case. inversion Case. assumption.
            assert_gso. eapply or_index_ne_cond; try apply phys_page_fixed. right. assumption.
            rewrite (ZMap.gso _ _ Hneq). intros (? & ? & ? & ?).
            match type of H2 with
            | context[?a @ (pt_pud_pool vmid @ (npts (shared labd)))] => assert(a @ (pt_pud_pool vmid @ (npts (shared labd))) = 0)
            end.
            eapply Hpud_next.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. rewrite phys_or; try assumption. omega. apply phys_page_fixed.
            autounfold; somega. rewrite phys_or in H3; try assumption. rewrite phys_or; try assumption. omega.
            apply H2 in H3. inversion H3.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            split. intro T. rewrite <- Hpgd_same in T. apply Hpmd_t in T.
            destruct T as (? & ? & ?). rewrite Hpgd_same in H. apply H in Case. inversion Case. assumption.
            assert_gso. eapply or_index_ne_cond; try apply phys_page_fixed. right. assumption.
            rewrite (ZMap.gso _ _ Hneq). assert_gso. repeat rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0).
            intros (? & ? & ? & ?). rewrite Hpgd_next in H0.
            assert (T: False) by (apply H0; reflexivity); inversion T.
            rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            assert_gso. eapply or_index_ne_cond; try assumption.
            right. assumption. repeat rewrite (ZMap.gso _ _ Hneq).
            assert_gso. repeat rewrite phys_or; try assumption.
            eapply vttbr_pool_ne_pgd_next; try eassumption. autounfold; somega. autounfold; somega.
            repeat rewrite (ZMap.gso _ _ Hneq0).
            assert_gso. rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq1). apply Hpmd_t. assumption.
          - intros. repeat autounfold in *.
            exploit (pte_same_cond addr0 addr). assumption. autounfold; split; assumption.
            intro pte_same. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            + duplicate Hsame.
              apply pte_same in D. destruct D as (Hpgd_same & Hpud_same & Hpmd_same & Hpte_same).
              autounfold in *. rewrite Hsame in Hhpt. rewrite ZMap.gss in Hhpt. inversion Hhpt.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro T; inversion T.
              intro; reflexivity. intro T; inversion T. intro T; inversion T. intro; simpl.
              rewrite Hpgd_same, Hpud_same, Hpmd_same, Hpte_same. repeat rewrite ZMap.gss.
              split_and; try reflexivity; try assumption. apply or3nz. apply or3nz. apply or3nz.
              apply and_or_same.
            + rewrite (ZMap.gso _ _ Hsame) in Hhpt.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 Hhpt). destruct H. simpl in *.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
                apply Hpfn0 in D. apply Hpte0 in D0.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. right.
                split. apply or3nz.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. repeat rewrite Hpmd_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz. split. apply and_or_same.
                rewrite phys_or; try assumption.
                destruct (pte_index addr0 =? pte_index addr) eqn:Hpte_same; bool_rel.
                autounfold in *.
                assert(F: False). apply Hsame; apply pte_same; split_and; try reflexivity; assumption.
                inversion F.
                assert_gso. apply or_index_ne_cond; try assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                rewrite Hpmd_next. rewrite D0. reflexivity.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range.
                generalize Hcond3, Hpmd_next_range. repeat match goal with [H: _ |- _] => clear H end.
                intros. omega. assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or. rewrite Hpud_next. reflexivity.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range.
                generalize Hcond3, Hpud_next_range. repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega. assumption.
                assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or. rewrite Hpgd_next. reflexivity.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range.
                generalize Hcond3, Hpgd_next_range. repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega. assumption.
                assumption.
                assert_gso. apply or_index_ne_cond. assumption. assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                assert_gso. rewrite phys_or. eapply vttbr_pool_ne_pgd_next. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. assumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as [T|T]; try (left; assumption). right.
                assert_gso. rewrite phys_or. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq1).
                destruct T as (T4 & T); split; try assumption.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T5 & T6 & T); split_and; try assumption.
                assert_gso. rewrite phys_or. eapply pud_pool_ne_pmd_next.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                eapply Hcond3. assumption. assumption. assumption. assumption.
                rewrite (ZMap.gso _ _ Hneq2). assumption.
              * simpl. intro T. duplicate T. apply Hlevel1 in T. apply Hpfn2 in D.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. destruct T. apply H in Case. inversion Case.
                assert_gso. apply or_index_ne_cond. assumption. assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T2 & T); split; try assumption.
                assert_gso. rewrite phys_or. eapply vttbr_pool_ne_pgd_next. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. assumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as (T3 & T); split; try assumption.
                assert_gso. rewrite phys_or. eapply pgd_pool_ne_pud_next. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. eassumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss. destruct T. apply H in Case. inversion Case.
                assert_gso. apply or_index_ne_cond. assumption. assumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or. eapply vttbr_pool_ne_pgd_next. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. assumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq0).
                assert_gso. rewrite phys_or. eapply pgd_pool_ne_pud_next. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. assumption. assumption. repeat rewrite (ZMap.gso _ _ Hneq1).
                destruct T as (T2 & T); split; try assumption.
                destruct T as (T3 & T4 & T); split; try assumption.
                assert_gso. rewrite phys_or. eapply pud_pool_ne_pmd_next.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                eapply Hcond3. assumption.
                destruct T as (T5 & T); try assumption. assumption. assumption.
                repeat rewrite (ZMap.gso _ _ Hneq2). split; assumption.
        }
        apply Hrelate.
        Local Transparent Z.land. simpl.
        srewrite. rewrite Case4 in Hspec. rewrite andb_assoc, andb_comm, andb_assoc, andb_comm in Hspec.
        simpl in Hspec. repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        erewrite Hpud_next in Case3. inversion Case3.
        rewrite phys_or; try assumption.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. assumption. autounfold; somega. omega.
        simpl. srewrite. rewrite Case2 in Hspec. rewrite andb_assoc, andb_comm in Hspec. simpl in Hspec.
        repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        erewrite Hpgd_next in Case1. inversion Case1.
        rewrite phys_or; try assumption.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. assumption. autounfold; somega. omega.
        simpl. srewrite. rewrite Case0 in Hspec. simpl in Hspec. repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        bool_rel. apply Hpgd_t in Case. contra. assumption.
        Local Opaque Z.land.
      Qed.

      Lemma set_npt_spec_2_pud_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 3)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = true end)
          (Hpud: match addr with VZ64 addr => (pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10; simpl in C10. clear C8. rename C10 into Hspec.
        rewrite Hpgd in Hspec. rewrite Hpud in Hspec.
        assert (Hpmd: (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t vmid @ (npts (shared habd))))) = false).
        { match goal with | |- ?x = false => destruct x eqn: Hpmd end.
          apply Hpmd_t in Hpmd. destruct Hpmd as (? & ? & ?).
          assert((pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = true).
          apply Hpud_t. bool_rel_all; omega. split; assumption. contra. bool_rel_all; assumption. reflexivity. }
        rewrite Hpmd in Hspec.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0.
        repeat autounfold in *.
        autounfold. rewrite Hhaltl. rewrite Hlock. rewrite C1. rewrite C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        apply Hpgd_t in Hpgd; try omega. bool_rel; assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond3.
        destruct_if.
        duplicate Cond3. rename D into Cond4.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond5.
        rewrite Hhaltl, Hlock.
        match goal with |- context [?c =? 0] => assert(c =? 0 = false) end.
        bool_rel. apply or3nz. rewrite H. clear H.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond6.
        rewrite ZMap.gss. simpl. extract_if. apply Hpud_pool_range. rewrite Cond7.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond8.
        destruct_if.
        duplicate Cond8. rename D into Cond9.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond10.
        rewrite Hhaltl, Hlock. rewrite and_or_same. simpl. rewrite Htstate. simpl.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond11.
        rewrite Hnext_pgd, Hnext_pud, Hnext_pmd, Case1, Case3 in Hspec. simpl in Hspec.
        simpl_hyp Hspec. destruct p. simpl_hyp Hspec.
        exploit (Hrelate0 addr z0 z1 z); try assumption; try omega. intro T; destruct T.
        bool_rel. apply Hlevel1 in C0. simpl in C0. autounfold in C0.
        destruct C0 as (? & ? & ?).
        assert((pud_index addr) @ ((pgd_index addr) @ (pud_t vmid @ (npts (shared habd)))) = true).
        apply Hpud_t. assumption. split; assumption. contra.
        assert((pt_pgd_next vmid @ (npts (shared labd)) <=? 65536 + 33554432 * vmid + 1052672) = true).
        bool_rel; omega. rewrite H in Hspec. simpl in Hspec. clear H.
        inv Hspec. clear Cond4 Cond9.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + assumption.
            + eapply phys_page_a_page. assumption. omega.
            + eapply phys_page_a_page. assumption. omega.
            + assert_gso. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity. reflexivity. autounfold; somega. omega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. omega.
            + apply Hvttbr_pool.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hpgd_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
            + destruct_zmap. right. right.
              repeat rewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega. apply and_or_same.
              pose proof (Hpud_pool addr0).
              destruct H as [T|T]; try (left; assumption). right.
              destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T0 & T); split; try assumption.
              destruct T as (T1 & T); split; try omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
          - reflexivity. - reflexivity. - reflexivity.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            autounfold in *. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            rewrite Hsame in *. rewrite ZMap.gss in *. rewrite H in *. inversion Hpte.
            rewrite (ZMap.gso _ _ Hsame) in Hpte.
            destruct (addr' / 4096 =? addr / 4096) eqn:Hsame'; bool_rel.
            rewrite Hsame' in *. rewrite ZMap.gss in Hpte'. assert(z1 = 2) by (eapply H0; eassumption). contra.
            rewrite (ZMap.gso _ _ Hsame') in Hpte'. eapply H0; eassumption.
          - intros; autounfold.
            match goal with |- context[?a @ (?b # ?c == true)] => assert(a @ (b # c == true) = a @ b) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. rewrite Hpgd; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same); reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. repeat rewrite ZMap.gss. split; try reflexivity.
            intros. split_and; try rewrite phys_or; try solve [assumption|omega]. apply or3nz.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            split; intros. rewrite <- Hpgd_same in H. apply Hpud_t in H. rewrite Hpgd_same in H. apply H.
            assumption. simpl.  rewrite <- Hpgd_same. apply Hpud_t. assumption.
            rewrite <- Hpgd_same in H. apply H. repeat rewrite (ZMap.gso _ _ Hpgd_same).
            split; intros. apply Hpud_t in H. destruct H as (? & ?).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq).
            split_and; assumption. assumption. destruct H as (? & ?).
            assert_gsoH H0. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq) in H0.
            apply Hpud_t. assumption. split_and; assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split; intros; try reflexivity. split_and; try omega.
            apply or3nz. apply and_or_same. apply or3nz.
            repeat rewrite (ZMap.gso _ _ Hpmd_same).
            split. intro T. rewrite <- Hpgd_same, <- Hpud_same in T. apply Hpmd_t in T.
            destruct T as (? & ? & ? & ?). rewrite Hpgd_same, Hpud_same in H0. contra. assumption.
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq).
            intros (? & ? & ? & ?).
            match type of H2 with
            | context[?a @ (pt_pud_pool vmid @ (npts (shared labd)))] => assert(a @ (pt_pud_pool vmid @ (npts (shared labd))) = 0)
            end.
            eapply Hpud_next. rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. assumption. autounfold; somega. omega. contra.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            split. intro T. rewrite <- Hpgd_same in T. apply Hpmd_t in T.
            destruct T as (? & ? & ? & ?). split. assumption.
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). split. rewrite <- Hpgd_same. assumption.
            assert_gso. repeat rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). rewrite <- Hpgd_same. split; assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H0. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq) in H0, H1, H2.
            assert_gsoH H1. rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0) in H1, H2.
            rewrite <- Hpgd_same in *. apply Hpmd_t. assumption. split_and; assumption.
            repeat rewrite (ZMap.gso _ _ Hpgd_same).
            split. intro T. apply Hpmd_t in T.
            destruct T as (? & ? & ? & ?). split. assumption.
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq).
            split. assumption.
            assert_gso. repeat rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption.  autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). split; assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H0. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left; eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq) in H0, H1, H2.
            assert_gsoH H1. rewrite phys_or; try assumption.
            eapply pgd_pool_ne_pud_next; try eassumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0) in H1, H2. apply Hpmd_t. assumption. split_and; assumption.
          - intros. repeat autounfold in *.
            exploit (pte_same_cond addr0 addr). assumption. autounfold; split; assumption.
            intro pte_same. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            + duplicate Hsame.
              apply pte_same in D. destruct D as (Hpgd_same & Hpud_same & Hpmd_same & Hpte_same).
              autounfold in *. rewrite Hsame in Hhpt. rewrite ZMap.gss in Hhpt. inversion Hhpt.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro T; inversion T.
              intro; reflexivity. intro T; inversion T. intro T; inversion T. intro; simpl.
              rewrite Hpgd_same, Hpud_same, Hpmd_same, Hpte_same. repeat rewrite ZMap.gss.
              split_and; try reflexivity; try assumption. apply or3nz. apply or3nz. apply and_or_same.
            + rewrite (ZMap.gso _ _ Hsame) in Hhpt.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 Hhpt). destruct H. simpl in *.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T.
                apply Hlevel0 in T. apply Hpfn0 in D. apply Hpte0 in D0.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T2 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. repeat rewrite Hpmd_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz. split. apply and_or_same.
                destruct (pte_index addr0 =? pte_index addr) eqn:Hpte_same; bool_rel.
                assert(CT: False). apply Hsame; apply pte_same; split_and; try reflexivity; assumption.
                inversion CT.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                rewrite Hpmd_next. destruct D; auto.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range. rewrite phys_or; try assumption.
                generalize Hcond3, Hpmd_next_range; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                apply phys_page_fixed.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                rewrite phys_or in H; try assumption. rewrite phys_or; try assumption.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                left. rewrite phys_or. rewrite Hpud_next. reflexivity.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range.
                generalize Hcond3, Hpud_next_range; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega. assumption. assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as [T|T]. left; assumption. right. destruct T as (T4 & T). split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                rewrite (ZMap.gso _ _ Hneq0). destruct T as [T|T]. left; assumption. right.
                destruct T as (T5 & T). split. assumption. destruct T as (T6 & T). split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. assumption. rewrite (ZMap.gso _ _ Hneq1). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq).
                destruct T as [T|T]. left; assumption. right. destruct T as (T4 & T). split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try assumption. eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                assumption. rewrite (ZMap.gso _ _ Hneq0). destruct T as [T|T]. left; assumption. right.
                destruct T as (T5 & T6 & T). split. assumption. split. assumption.
                assert_gso. rewrite phys_or. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. assumption. assumption.
                rewrite (ZMap.gso _ _ Hneq1). assumption.
              * simpl. intro T. duplicate T. apply Hlevel1 in T. apply Hpfn2 in D.
                destruct T as (T2 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                rewrite Hpgd_same, Hpud_same in *. destruct T as (T3 & T4). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pgd_index_diff_res_diff; try eassumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D.
                destruct T as (T2 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                rewrite Hpgd_same, Hpud_same in *. destruct T as (T3 & T4). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as (T3 & T4 & T5 & T); split. assumption. split. assumption. split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left; eapply pgd_index_diff_res_diff; eassumption. rewrite (ZMap.gso _ _ Hneq).
                assert_gso. rewrite phys_or; try assumption. eapply pgd_pool_ne_pud_next; try eassumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                repeat rewrite (ZMap.gso _ _ Hneq0).
                destruct T as (T3 & T4 & T5 & T); split. assumption. split. assumption. split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. repeat rewrite (ZMap.gso _ _ Hneq1). assumption.
        }
        apply Hrelate.
        Local Transparent Z.land. simpl.
        srewrite. rewrite Case3 in Hspec. rewrite andb_assoc, andb_comm, andb_assoc, andb_comm in Hspec.
        simpl in Hspec. repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        erewrite Hpud_next in Case2. inversion Case2.
        rewrite phys_or; try assumption.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. assumption. autounfold; somega. omega.
        simpl. srewrite. rewrite Case1 in Hspec. rewrite andb_assoc, andb_comm in Hspec. simpl in Hspec.
        repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        assert((pud_index addr) @ ((pgd_index addr) @ (pud_t vmid @ (npts (shared habd)))) = true).
        apply Hpud_t. assumption. bool_rel_all; split; assumption. contra.
        Local Opaque Z.land.
      Qed.

      Lemma set_npt_spec_2_pmd_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 3)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = true end)
          (Hpud: match addr with VZ64 addr => (pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = true end)
          (Hpmd: match addr with VZ64 addr => (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t (vmid @ (npts (shared habd)))))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10; simpl in C10. clear C8. rename C10 into Hspec.
        rewrite Hpgd in Hspec. rewrite Hpud in Hspec. rewrite Hpmd in Hspec.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0.
        repeat autounfold in *.
        autounfold. rewrite Hhaltl. rewrite Hlock. rewrite C1. rewrite C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        apply Hpgd_t in Hpgd; try omega. bool_rel; assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        apply Hpud_t in Hpud; try omega. destruct Hpud; bool_rel; omega.
        rewrite Hpgd_pool_range. rewrite Hhaltl, Hlock. rewrite Case0.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond3.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond4.
        destruct_if.
        duplicate Cond4. rename D into Cond5.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond6.
        rewrite Hhaltl, Hlock. rewrite and_or_same. simpl. rewrite Htstate. simpl.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega.  assumption. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond7.
        rewrite Hnext_pgd, Hnext_pud, Hnext_pmd, Case2 in Hspec.
        assert((pt_pgd_next vmid @ (npts (shared labd)) <=? 65536 + 33554432 * vmid + 1052672) = true).
        bool_rel; omega. rewrite H in Hspec; clear H.
        assert((pt_pud_next vmid @ (npts (shared labd)) <=? 65536 + 33554432 * vmid + 9441280) = true).
        bool_rel; omega. rewrite H in Hspec; clear H. simpl in Hspec.
        simpl_hyp Hspec. destruct p. simpl_hyp Hspec.
        exploit (Hrelate0 addr z0 z1 z); try assumption; try omega. intro T; destruct T.
        bool_rel. duplicate C0. apply Hlevel1 in C0. simpl in C0. autounfold in C0.
        destruct C0 as (? & ? & ? & ?). rewrite Case1 in H1.
        assert (level = 0) by (apply Hpte0; rewrite H1; reflexivity). rewrite D in H3; inversion H3.
        inv Hspec. clear Cond5.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + apply Hvttbr_pool_range.
            + apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpud_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + assumption. + assumption.
            + eapply phys_page_a_page. assumption. omega.
            + apply Hpgd_next. assumption.
            + assert_gso. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity. omega. autounfold; somega. autounfold; somega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. apply phys_page_fixed. autounfold; somega. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= pt_pud_next vmid @ (npts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpud_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. assumption. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. omega.
            + apply Hvttbr_pool.
            + apply Hpgd_pool.
            + destruct_zmap. right. right.
              repeat rewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega. apply and_or_same.
              pose proof (Hpud_pool addr0).
              destruct H as [T|T]; try (left; assumption). right.
              destruct T as [T|T]; try (left; assumption). right.
              destruct T as (T0 & T); split; try assumption.
              destruct T as (T1 & T); split; try omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
          - reflexivity. - reflexivity. - reflexivity.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            autounfold in *. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            rewrite Hsame in *. rewrite ZMap.gss in *. rewrite H in *. inversion Hpte.
            rewrite (ZMap.gso _ _ Hsame) in Hpte.
            destruct (addr' / 4096 =? addr / 4096) eqn:Hsame'; bool_rel.
            rewrite Hsame' in *. rewrite ZMap.gss in Hpte'. assert(z1 = 2) by (eapply H0; eassumption). contra.
            rewrite (ZMap.gso _ _ Hsame') in Hpte'. eapply H0; eassumption.
          - intros; autounfold.
            match goal with |- context[?a @ (?b # ?c == true)] => assert(a @ (b # c == true) = a @ b) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. rewrite Hpgd; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same); reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = (pud_index addr0) @ ((pgd_index addr0) @ (pud_t vmid @ (npts (shared habd))))) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. rewrite ZMap.gss. rewrite Hpud. reflexivity.
            rewrite (ZMap.gso _ _ Hpud_same). reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). reflexivity.
            rewrite H. apply Hpud_t. assumption.
          - intros; autounfold.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            repeat rewrite Hpgd_same. repeat rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            repeat rewrite Hpud_same. repeat rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss.
            split; intros; try reflexivity. split_and; try assumption; try omega. apply and_or_same.
            apply or3nz. repeat rewrite (ZMap.gso _ _ Hpmd_same).
            split. intro T. rewrite <- Hpgd_same, <- Hpud_same in T. apply Hpmd_t in T.
            destruct T as (T1 & T2 & T3 & T4).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq). rewrite <- Hpgd_same, <- Hpud_same.
            split_and; try assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H1. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right. assumption. rewrite (ZMap.gso _ _ Hneq) in H1, H2.
            rewrite <- Hpgd_same in *; rewrite <- Hpud_same in *. apply Hpmd_t. assumption. split_and; assumption.
            repeat rewrite (ZMap.gso _ _ Hpud_same).
            split. intro T. rewrite <- Hpgd_same in T. apply Hpmd_t in T.
            destruct T as (T1 & T2 & T3 & T4).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. rewrite <- Hpgd_same at 1. eapply pud_index_diff_res_diff; try eassumption. auto.
            rewrite (ZMap.gso _ _ Hneq). rewrite <- Hpgd_same. split_and; try assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H1. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. rewrite <- Hpgd_same at 1. eapply pud_index_diff_res_diff; autounfold; try rewrite Hpgd_same; try eassumption.
            right; assumption. rewrite (ZMap.gso _ _ Hneq) in H1, H2.
            rewrite <- Hpgd_same. apply Hpmd_t. assumption. rewrite Hpgd_same; split_and; try assumption.
            rewrite (ZMap.gso _ _ Hpgd_same). split. intro T. apply Hpmd_t in T.
            destruct T as (T1 & T2 & T3 & T4).
            assert_gso. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pud_index_diff_res_diff; try eassumption. auto.
            rewrite (ZMap.gso _ _ Hneq). split_and; try assumption. assumption.
            intros (? & ? & ? & ?).
            assert_gsoH H1. eapply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. eapply pud_index_diff_res_diff; autounfold; try rewrite Hpgd_same; try eassumption.
            left; assumption. rewrite (ZMap.gso _ _ Hneq) in H1, H2.
            apply Hpmd_t; split_and; try assumption.
          - intros. repeat autounfold in *.
            exploit (pte_same_cond addr0 addr). assumption. autounfold; split; assumption.
            intro pte_same. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            + duplicate Hsame.
              apply pte_same in D. destruct D as (Hpgd_same & Hpud_same & Hpmd_same & Hpte_same).
              autounfold in *. rewrite Hsame in Hhpt. rewrite ZMap.gss in Hhpt. inversion Hhpt.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro T; inversion T.
              intro; reflexivity. intro T; inversion T. intro T; inversion T. intro; simpl.
              rewrite Hpgd_same, Hpud_same, Hpmd_same, Hpte_same. repeat rewrite ZMap.gss.
              split_and; try reflexivity; try assumption. apply or3nz. apply and_or_same.
            + rewrite (ZMap.gso _ _ Hsame) in Hhpt.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 Hhpt). destruct H. simpl in *.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
                apply Hpfn0 in D. apply Hpte0 in D0.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T2 & T); split; try assumption.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same; repeat rewrite ZMap.gss.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. repeat rewrite Hpmd_same; repeat rewrite ZMap.gss.
                right. split. apply or3nz. split. apply and_or_same.
                destruct (pte_index addr0 =? pte_index addr) eqn:Hpte_same; bool_rel.
                assert(CT: False). apply Hsame; apply pte_same; split_and; try reflexivity; assumption. inversion CT.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                rewrite Hpmd_next. rewrite D0; reflexivity.
                match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                apply or_index_range. rewrite phys_or; try assumption.
                generalize Hcond3, Hpmd_next_range. repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                apply phys_page_fixed.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                rewrite phys_or; try assumption. rewrite phys_or in H; try assumption.
                generalize H; repeat match goal with [H: _ |- _] => clear H end; intros; omega.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as[T|T]. rewrite <- Hpud_same. left; assumption. right.
                destruct T as (T5 & T). split. rewrite <- Hpud_same. assumption.
                destruct T as (T6 & T). split. rewrite <- Hpud_same. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. autounfold. rewrite <- Hpud_same; assumption.
                rewrite (ZMap.gso _ _ Hneq0). rewrite <- Hpud_same. assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. rewrite <- Hpgd_same at 1. autounfold in *.
                eapply pud_index_diff_res_diff; autounfold; try rewrite Hpgd_same; try eassumption.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as[T|T]. left; assumption. right.
                destruct T as (T5 & T). split. assumption. destruct T as (T6 & T). split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. autounfold in *. eapply pud_index_diff_res_diff; autounfold; try eassumption.
                left; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as[T|T]. left; assumption. right.
                destruct T as (T5 & T). split. assumption. destruct T as (T6 & T). split. assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. rewrite (ZMap.gso _ _ Hneq0). assumption.
              * simpl. intro T. duplicate T. apply Hlevel1 in T. simpl in T. autounfold in *.
                destruct T as (T0 & T); split; try assumption.
                destruct T as (T1 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel; autounfold in Hpmd_same.
                rewrite Hpgd_same, Hpud_same, Hpmd_same in *. rewrite ZMap.gss.
                destruct T as (T5 & T6). rewrite Case1 in T5. symmetry in T5. apply Hpte0 in T5.
                rewrite D in T5; inversion T5.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. rewrite (ZMap.gso _ _ Hneq). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pud_index_diff_res_diff; try eassumption.
                right. assumption. rewrite (ZMap.gso _ _ Hneq). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pud_index_diff_res_diff; try eassumption.
                left. assumption. rewrite (ZMap.gso _ _ Hneq). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. simpl in T. autounfold in *.
                destruct T as (T0 & T); split; try assumption. destruct T as (T1 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel; autounfold in Hpgd_same.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel; autounfold in Hpud_same.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel; autounfold in Hpmd_same.
                rewrite Hpgd_same, Hpud_same, Hpmd_same in *. rewrite ZMap.gss.
                split. apply or3nz. split. apply and_or_same.
                destruct T as (T5 & T6 & T7). rewrite Case1 in T5.
                assert(F: False) by (apply T5; reflexivity); inversion F.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T5 & T); split; try assumption. destruct T as (T6 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pud_index_diff_res_diff; try eassumption. right; assumption.
                rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T5 & T); split; try assumption. destruct T as (T6 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. rewrite (ZMap.gso _ _ Hneq0). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pud_index_diff_res_diff; try eassumption. left; assumption.
                rewrite (ZMap.gso _ _ Hneq).
                destruct T as (T5 & T); split; try assumption. destruct T as (T6 & T); split; try assumption.
                assert_gso. rewrite phys_or; try assumption. eapply pud_pool_ne_pmd_next; try assumption.
                generalize Hvalid0; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                generalize Hcond1; repeat match goal with [H: _ |- _] => clear H end; intros; autounfold; somega.
                apply Hcond3. assumption. rewrite (ZMap.gso _ _ Hneq0). assumption.
        }
        apply Hrelate.
        Local Transparent Z.land. simpl.
        srewrite. rewrite Case2 in Hspec. rewrite andb_assoc, andb_comm, andb_assoc, andb_comm in Hspec.
        simpl in Hspec. repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        rewrite Hpud_pool_range. destruct_if.
        assert((pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t (vmid @ (npts (shared habd)))))) = true).
        apply Hpmd_t. assumption. bool_rel_all; split_and; assumption. contra.
        simpl_hyp Hspec; destruct p; simpl_hyp Hspec. inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        bool_rel_all.
        exploit (Hrelate0 addr z0 z1 z); try assumption; try omega. intro T; destruct T.
        destruct Hlevel. apply Hlevel0 in H. simpl in H. autounfold in H. destruct H. contra.
        destruct H. destruct H0. contra. destruct H0. destruct H1. contra. destruct H1.
        destruct H2. contra. destruct H. contra. apply Hlevel3 in H. simpl in H.
        autounfold in H. destruct H as (? & ? & ? & ? & ?). contra.
      Qed.

      Lemma set_npt_spec_2_pte_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hlevel: level = 3)
          (Hpgd: match addr with VZ64 addr => (pgd_index addr) @ (pgd_t (vmid @ (npts (shared habd)))) = true end)
          (Hpud: match addr with VZ64 addr => (pud_index addr) @ ((pgd_index addr) @ (pud_t (vmid @ (npts (shared habd))))) = true end)
          (Hpmd: match addr with VZ64 addr => (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t (vmid @ (npts (shared habd)))))) = true end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert (Hrelate: forall i : Z, relate_npt i i @ (npts (shared habd)) i @ (npts (shared labd))).
        { destruct Hrel. rewrite id_halt0 in Hhalt. rewrite Hhalt in id_npts0.
          clear_hyp; simpl_local. assumption. }
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        pose proof (Hrelate vmid).
        remember (vmid @ (npts (shared habd))) as hnpt in *; symmetry in Heqhnpt.
        remember (vmid @ (npts (shared labd))) as lnpt in *; symmetry in Heqlnpt.
        destruct H; simpl in *.
        hsimpl_func Hspec.
        assert(Htstate: (tstate labd =? 0) = true).
        { destruct Hrel. srewrite. reflexivity. }
        assert(Hlock: (5 + vmid) @ (lock labd) = LockOwn true).
        { destruct Hrel. srewrite. reflexivity. }
        rename z into addr. rename z0 into pte.
        unfold local_mmap in C10; simpl in C10. clear C8. rename C10 into Hspec.
        rewrite Hpgd, Hpud, Hpmd in Hspec.
        duplicate Hvalid. destruct D.
        unfold set_npt_spec0. simpl.
        repeat autounfold in *.
        rewrite Hhaltl, Hlock, C1, C2. clear_hyp.
        bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val vmid) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. }
        autounfold in vttbr_align.
        rewrite Hvttbr; try omega.
        extract_if. unfold pgd_index.
        exploit (or_index_range (65536 + 33554432 * vmid) (Z.shiftr addr PGDIR_SHIFT)); try assumption; try omega.
        autounfold; somega. intro range. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        apply Hpgd_t in Hpgd; try omega. bool_rel; assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (pt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pgd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        apply Hpud_t in Hpud; try omega. destruct Hpud; bool_rel; omega.
        rewrite Hpgd_pool_range. rewrite Hhaltl, Hlock. rewrite Case0.
        extract_if. match goal with |- context[?a @ (pt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= pt_pud_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond3.
        rewrite Hpud_pool_range. rewrite andb_comm. simpl. destruct_if.
        apply Hpmd_t in Hpmd; try omega. destruct Hpmd; bool_rel; omega.
        rewrite Hpud_pool_range. rewrite Htstate, Hhaltl, Hlock. simpl.
        destruct_if.
        extract_if. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
        destruct H. rewrite H in Case1. inversion Case1. destruct H. bool_rel; contra. destruct H as (? & ? & ?).
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H2 with _ <= _ < ?a => assert(a <= pt_pmd_next vmid @ (npts (shared labd))) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H0; assumption. omega. rewrite Cond4.
        repeat simpl_hyp Hspec; inv Hspec.
        assert(R: 0 <= addr < 281474976710656) by omega.
        pose proof (Hrelate0 _ _ _ _ R C). destruct H. bool_rel; apply Hlevel1 in C7; simpl in C7.
        destruct C7 as (? & ? & ? & ?). rewrite <- H1 in H2. autounfold in H2. apply H2 in Case2. inversion Case2.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T. intro i.
        destruct_zmap. bool_rel_all. clear_hyp.
        {
          constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + omega.
            + apply Hvttbr_pool_range.
            + apply Hpgd_pool_range.
            + apply Hpud_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega. + omega.
            + assumption. + assumption. + assumption.
            + apply Hpgd_next. assumption.
            + apply Hpud_next. assumption.
            + assert_gso. match goal with |- context[?a @ (pt_pud_pool _)] => pose proof (Hpud_pool a) end.
              destruct H0. rewrite H0 in Case1. omega.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. apply phys_page_fixed. autounfold; somega.
              match type of H1 with _ <= _ < ?a => assert(a <= pt_pmd_next vmid @ (npts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. assumption.
            + apply Hvttbr_pool.
            + apply Hpgd_pool.
            + apply Hpud_pool.
          - assumption. - assumption. - assumption.
          - intros. pose proof (Hlevel2 addr0 addr' His_addr His_addr' Hpgd_same Hpud_same Hpmd_same).
            autounfold in *. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            rewrite Hsame in *. rewrite ZMap.gss in *. rewrite H in *. inversion Hpte.
            rewrite (ZMap.gso _ _ Hsame) in Hpte.
            destruct (addr' / 4096 =? addr / 4096) eqn:Hsame'; bool_rel.
            rewrite Hsame' in *. rewrite ZMap.gss in Hpte'. assert(z1 = 2) by (eapply H0; eassumption). contra.
            rewrite (ZMap.gso _ _ Hsame') in Hpte'. eapply H0; eassumption.
          - intros; autounfold.
            match goal with |- context[?a @ (?b # ?c == true)] => assert(a @ (b # c == true) = a @ b) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. rewrite Hpgd; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same); reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = (pud_index addr0) @ ((pgd_index addr0) @ (pud_t vmid @ (npts (shared habd))))) end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. rewrite ZMap.gss. rewrite Hpud. reflexivity.
            rewrite (ZMap.gso _ _ Hpud_same). reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). reflexivity.
            rewrite H. apply Hpud_t. assumption.
          - intros; autounfold.
            match goal with
            | |- ?c = true <-> _ => assert(c = (pmd_index addr0) @ ((pud_index addr0) @ ((pgd_index addr0) @ (pmd_t vmid @ (npts (shared habd))))))
            end.
            destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss.
            destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
            rewrite Hpud_same. rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            repeat rewrite Hpmd_same. repeat rewrite ZMap.gss. rewrite Hpmd. reflexivity.
            rewrite (ZMap.gso _ _ Hpmd_same). reflexivity.
            rewrite (ZMap.gso _ _ Hpud_same). reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). reflexivity.
            rewrite H. apply Hpmd_t. assumption.
          - intros. repeat autounfold in *.
            exploit (pte_same_cond addr0 addr). assumption. autounfold; split; assumption.
            intro pte_same. destruct (addr0 / 4096 =? addr / 4096) eqn:Hsame; bool_rel.
            + duplicate Hsame.
              apply pte_same in D. destruct D as (Hpgd_same & Hpud_same & Hpmd_same & Hpte_same).
              autounfold in *. rewrite Hsame in Hhpt. rewrite ZMap.gss in Hhpt. inversion Hhpt.
              constructor; autounfold. auto. split; intro T; [inversion T|inv T; contra].
              intro T; inversion T. intro T; inversion T. intro; reflexivity.
              intro T; inversion T. intro T; inversion T. intro; simpl.
              rewrite Hpgd_same, Hpud_same, Hpmd_same, Hpte_same. repeat rewrite ZMap.gss.
              split_and; try reflexivity; try assumption.
            + rewrite (ZMap.gso _ _ Hsame) in Hhpt.
              pose proof (Hrelate0 _ _ _ _ Hvalid0 Hhpt). destruct H.
              constructor; try assumption.
              * simpl. intro T. duplicate T. duplicate T. apply Hlevel0 in T.
                apply Hpfn0 in D. apply Hpte0 in D0.
                simpl in T. destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T2 & T); split; try assumption.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                rewrite Hpgd_same in *. repeat rewrite ZMap.gss.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                autounfold in *. repeat rewrite Hpud_same in *; repeat rewrite ZMap.gss.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T4 & T); split; try assumption.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. repeat rewrite Hpmd_same in *; repeat rewrite ZMap.gss.
                destruct T as (T5 & T); split; try assumption.
                destruct (pte_index addr0 =? pte_index addr) eqn:Hpte_same; bool_rel.
                autounfold in *. repeat rewrite Hpte_same in *; repeat rewrite ZMap.gss.
                assert(addr0 / 4096 = addr / 4096) by
                    (apply pte_same; split_and; solve[assumption|reflexivity]). contra.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right; assumption. repeat rewrite (ZMap.gso _ _ Hneq). assumption.
                destruct T as (T5 & T); split; try assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. rewrite <- Hpgd_same at 1; rewrite <- Hpud_same at 1; eapply pmd_index_diff_res_diff;
                        autounfold; try rewrite Hpgd_same; try rewrite Hpud_same; try eassumption. auto.
                rewrite (ZMap.gso _ _ Hneq). assumption.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T4 & T); split; try assumption.
                destruct T as (T5 & T); split; try assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. rewrite <- Hpgd_same at 1; eapply pmd_index_diff_res_diff;
                        autounfold in *; try rewrite Hpgd_same;  try eassumption. auto.
                rewrite (ZMap.gso _ _ Hneq). assumption.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T3 & T); split; try assumption.
                destruct T as [T|T]; try (left; assumption). right.
                destruct T as (T4 & T); split; try assumption.
                destruct T as (T5 & T); split; try assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pmd_index_diff_res_diff; autounfold in *; try eassumption. auto.
                rewrite (ZMap.gso _ _ Hneq). assumption.
              * simpl. intro T. duplicate T. apply Hlevel3 in T. apply Hpfn3 in D. simpl in T. autounfold in *.
                destruct T as (T1 & T2 & T3 & T4 & T5).
                split_and; try assumption.
                destruct (pte_index addr0 =? pte_index addr) eqn:Hpte_same; bool_rel; autounfold in Hpte_same.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                left. eapply pmd_index_diff_res_diff; autounfold in *; try eassumption. destruct pte_same.
                match type of H with
                  ?x -> _ => assert(x -> False) by (intro T; apply H in T; apply Hsame; assumption)
                end.
                destruct (pgd_index addr0 =? pgd_index addr) eqn:Hpgd_same; bool_rel.
                destruct (pud_index addr0 =? pud_index addr) eqn:Hpud_same; bool_rel.
                destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
                autounfold in *. assert(False) by (apply H1; split_and; assumption). inversion H2.
                right; right; apply Hpmd_same. right; left; apply Hpud_same. left; apply Hpgd_same.
                rewrite (ZMap.gso _ _ Hneq). assumption.
                assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
                right. assumption.  rewrite (ZMap.gso _ _ Hneq). assumption.
        }
        apply Hrelate.
        bool_rel_all; try omega.
        repeat simpl_hyp Hspec; inv Hspec.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
        assert(R: 0 <= addr < 281474976710656) by omega.
        pose proof (Hrelate0 _ _ _ _ R C). destruct H. repeat autounfold in *. bool_rel_all.
        destruct Hlevel. apply Hlevel0 in H. destruct H. contra. destruct H as [H1 H].
        destruct H. contra.  destruct H as [H2 H]. destruct H. contra. destruct H as (? & ? & ?). contra.
        destruct H. contra. apply Hlevel3 in H. destruct H as (? & ? & ? & ? & ?). contra.
        eexists; split. reflexivity. destruct Hrel. constructor; try assumption. simpl. omega. intro T; inversion T.
      Qed.

      Lemma set_npt_spec_exists:
        forall habd habd' labd vmid addr level pte f
          (Hspec: set_npt_spec vmid addr level pte habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_npt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. duplicate Hspec. unfold_spec D; autounfold in D; repeat simpl_hyp D; contra.
        assert(halt labd = true) by (destruct Hrel; srewrite; reflexivity).
        unfold set_npt_spec0; repeat autounfold. repeat srewrite. simpl. inv D.
        destruct_if. eexists; split. reflexivity. assumption.
        eexists; split. reflexivity. rewrite <- H.
        assert (labd {halt : halt labd} = labd).
        destruct labd. simpl. destruct shared. simpl. reflexivity.
        rewrite H0; assumption.
        bool_rel_all. subst. inversion Hcond6.
        destruct ((pgd_index z) @ (pgd_t (vmid @ (npts (shared habd))))) eqn:Hpgd.
        destruct ((pud_index z) @ ((pgd_index z) @ (pud_t (vmid @ (npts (shared habd)))))) eqn:Hpud.
        eapply set_npt_spec_1_pmd_exists; eassumption.
        eapply set_npt_spec_1_pud_exists; eassumption.
        eapply set_npt_spec_1_pgd_exists; eassumption.
        destruct ((pgd_index z) @ (pgd_t (vmid @ (npts (shared habd))))) eqn:Hpgd.
        destruct ((pud_index z) @ ((pgd_index z) @ (pud_t (vmid @ (npts (shared habd)))))) eqn:Hpud.
        destruct ((pmd_index z) @ ((pud_index z) @ ((pgd_index z) @ (pmd_t (vmid @ (npts (shared habd))))))) eqn:Hpmd.
        eapply set_npt_spec_2_pte_exists; eassumption.
        eapply set_npt_spec_2_pmd_exists; eassumption.
        eapply set_npt_spec_2_pud_exists; eassumption.
        eapply set_npt_spec_2_pgd_exists; eassumption.
      Qed.

      Lemma mem_load_ref_spec_exists:
        forall habd habd' labd gfn reg f
          (Hspec: mem_load_ref_spec gfn reg habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', mem_load_ref_spec gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. hsimpl_func Hspec.
        eexists. split. unfold mem_load_ref_spec. reflexivity.
        assumption.
      Qed.

      Lemma mem_store_ref_spec_exists:
        forall habd habd' labd gfn reg f
          (Hspec: mem_store_ref_spec gfn reg habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', mem_store_ref_spec gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. hsimpl_func Hspec.
        eexists. split. unfold mem_store_ref_spec. reflexivity.
        assumption.
      Qed.

    End FreshPrim.

  End WITHMEM.

End NPTWalkProofHigh.

```
