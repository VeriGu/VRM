# MmioSPTWalkRefine

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

Require Import MmioSPTWalk.Spec.
Require Import MmioPTWalk.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioPTAlloc.Spec.
Require Import RData.
Require Import MmioSPTWalk.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioPTWalk.Layer.
Require Import NPTWalk.ProofHighAux.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioSPTWalkProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioSPTWalk_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioPTWalk_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Inductive relate_entry (cbndx: Z) (index: Z) (hspt: SPT) (lspt: SPT): Z -> Z -> Z -> Prop :=
    | RELATE_ENTRY:
        forall addr pfn pte
          (Hpfn:  pfn = phys_page pte / PAGE_SIZE)
          (Hpte: let vttbr_pa := SMMU_TTBR index cbndx in
                 let pgd_idx := stage2_pgd_index addr in
                 let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
                 let pgd := ZMap.get pgd_p (spt_vttbr_pool lspt) in
                 let pgd_pa := phys_page pgd in
                 ((pgd = 0 /\ pte = 0) \/
                  (pgd <> 0 /\ let pmd_idx := pmd_index addr in
                             let pmd_p := Z.lor pgd_pa (pmd_idx * 8) in
                             let pmd := ZMap.get pmd_p (spt_pgd_pool lspt) in
                             let pmd_pa := phys_page pmd in
                             (pmd = 0 /\ pte = 0) \/
                             (pmd <> 0 /\ let pte_idx := pte_index addr in
                                        let pte_p := Z.lor pmd_pa (pte_idx * 8) in
                                        ZMap.get pte_p (spt_pmd_pool lspt) = pte)))),
          relate_entry cbndx index hspt lspt addr pfn pte.

    Inductive valid_lspt (lspt: SPT) : Prop :=
    | VALID_LSPT
        (Hvttbr_pool_range: forall p, is_int64 (p @ (spt_vttbr_pool lspt)) = true)
        (Hpgd_pool_range: forall p, is_int64 (p @ (spt_pgd_pool lspt)) = true)
        (Hpmd_pool_range: forall p, is_int64 (p @ (spt_pmd_pool lspt)) = true)
        (Hpgd_next_range: SMMU_PGD_START <= spt_pgd_next lspt <= SMMU_PMD_START)
        (Hpmd_next_range: SMMU_PMD_START <= spt_pmd_next lspt <= SMMU_POOL_END)
        (Hpgd_next_align: phys_page (spt_pgd_next lspt) = (spt_pgd_next lspt))
        (Hpmd_next_align: phys_page (spt_pmd_next lspt) = (spt_pmd_next lspt))
        (Hpgd_next: forall addr, addr >= spt_pgd_next lspt -> addr @ (spt_pgd_pool lspt) = 0)
        (Hpmd_next: forall addr, addr >= spt_pmd_next lspt -> addr @ (spt_pmd_pool lspt) = 0)
        (Hvttbr_pool: forall addr, addr @ (spt_vttbr_pool lspt) = 0 \/
                              (SMMU_PGD_START <= phys_page (addr @ (spt_vttbr_pool lspt)) < spt_pgd_next lspt /\
                               (phys_page (addr @ (spt_vttbr_pool lspt))) @ (spt_pgd_par lspt) = addr))
        (Hpgd_pool: forall addr, addr @ (spt_pgd_pool lspt) = 0 \/
                            (SMMU_PMD_START <= phys_page (addr @ (spt_pgd_pool lspt)) < spt_pmd_next lspt /\
                             (phys_page (addr @ (spt_pgd_pool lspt))) @ (spt_pmd_par lspt) = addr)):
        valid_lspt lspt.

    Inductive relate_spt : SPT -> SPT -> Prop :=
    | RELATE_SPT:
        forall hspt lspt
          (Hvalid: valid_lspt lspt)
          (Hnext_pgd: spt_pgd_next hspt = spt_pgd_next lspt)
          (Hnext_pmd: spt_pmd_next hspt = spt_pmd_next lspt)
          (Hpgd_t: forall cbndx index addr (ge0: 0 <= addr),
              let vttbr_p := SMMU_TTBR index cbndx in
              let pgd_idx := stage2_pgd_index addr in
              pgd_idx @ (vttbr_p @ (spt_pgd_t hspt)) = true <->
              let pgd_p := Z.lor vttbr_p (pgd_idx * 8) in
              pgd_p @ (spt_vttbr_pool lspt) <> 0)
          (Hpmd_t: forall cbndx index addr (ge0: 0 <= addr),
              let vttbr_p := SMMU_TTBR index cbndx in
              let pgd_idx := stage2_pgd_index addr in
              let pmd_idx := pmd_index addr in
              pmd_idx @ (pgd_idx @ (vttbr_p @ (spt_pmd_t hspt))) = true <->
              let pgd_p := Z.lor vttbr_p (pgd_idx * 8) in
              let pgd := pgd_p @ (spt_vttbr_pool lspt) in
              pgd <> 0 /\
              let pmd_p := Z.lor (phys_page pgd) (pmd_idx * 8) in
              let pmd := pmd_p @ (spt_pgd_pool lspt) in
              pmd <> 0)
          (Hrelate: forall cbndx index addr pfn pte
                      (Hvalid: valid_smmu_addr addr)
                      (Hhpt: (addr / PAGE_SIZE) @ ((SMMU_TTBR index cbndx) @ (spt_pt hspt)) = (pfn, pte)),
              relate_entry cbndx index hspt lspt addr pfn pte),
          relate_spt hspt lspt.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_icore: icore hadt = icore ladt;
          id_ihost: ihost hadt = ihost ladt;
          id_tstate: tstate hadt = tstate ladt;
          id_halt: halt hadt = halt ladt;
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
          id_npts: npts (shared hadt) = npts (shared ladt);
          id_smmu_vmid: smmu_vmid (shared hadt) = smmu_vmid (shared ladt);
          id_spts: (halt ladt = false) -> relate_spt (spts (shared hadt)) (spts (shared ladt))
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
           is_smmu_addr
           valid_smmu_addr
           get_smmu_cfg_hw_ttbr_spec
           walk_smmu_pgd_spec
           walk_smmu_pmd_spec
           walk_smmu_pte_spec
           set_smmu_pte_spec
           check64_spec
           panic_spec.

      Lemma vttbr_val: forall cbndx index, valid_smmu index -> valid_smmu_cfg cbndx -> phys_page (SMMU_TTBR index cbndx) = SMMU_TTBR index cbndx.
      Admitted.

      Lemma or_index_range_8192:
        forall addr n (Haddr: 0 <= addr) (Hn: 0 <= n),
          addr <= Z.lor addr ((Z.land n 1023) * 8) < addr + 8192.
      Admitted.

      Lemma or_index_ne_cond_8192:
        forall n m a b (diff: SMMU_POOL_START + n * 4096 * 2 <> SMMU_POOL_START + m * 4096 * 2 \/ (Z.land a 1023) <> Z.land b 1023),
          Z.lor (SMMU_POOL_START + n * 4096 * 2) ((Z.land a 1023) * 8) <> Z.lor (SMMU_POOL_START + m * 4096 * 2) ((Z.land b 1023) * 8).
      Admitted.

      Lemma or_index_range:
        forall addr n (Haddr: 0 <= addr) (Hn: 0 <= n),
          addr <= Z.lor addr ((Z.land n 511) * 8) < addr + 4096.
      Admitted.

      Lemma pte_same_cond:
        forall addr addr'
          (Hvalid: valid_smmu_addr addr)
          (Hvalid': valid_smmu_addr addr'),
          stage2_pgd_index addr = stage2_pgd_index addr' /\
          pmd_index addr = pmd_index addr' /\ pte_index addr = pte_index addr' <->
          addr / PAGE_SIZE = addr' / PAGE_SIZE.
      Admitted.

      Lemma pgd_pool_ne_pmd_next:
        forall addr a b lspt (Hvalid: valid_lspt lspt) (Ha: 0 <= a) (Hb: 0 <= b),
          Z.lor (phys_page (addr @ (spt_pgd_pool lspt))) (Z.land a 511 * 8) <>
          Z.lor (spt_pmd_next lspt) (Z.land b 511 * 8).
      Admitted.

      Lemma vttbr_pool_ne_pgd_next:
        forall addr a b lspt (Hvalid: valid_lspt lspt) (Ha: 0 <= a) (Hb: 0 <= b),
          Z.lor (phys_page (addr @ (spt_vttbr_pool lspt))) (Z.land a 511 * 8) <>
          Z.lor (spt_pgd_next lspt) (Z.land b 511 * 8).
      Admitted.

      Lemma pgd_index_diff_res_diff:
        forall addr addr0 cbndx index cbndx0 index0 lspt (Hvalid: valid_lspt lspt),
          let pgd_idx := stage2_pgd_index addr in
          let pgd_idx0 := stage2_pgd_index addr0 in
          let vttbr := SMMU_TTBR index cbndx in
          let vttbr0 := SMMU_TTBR index0 cbndx0 in
          let pgd_p := Z.lor vttbr (pgd_idx * 8) in
          let pgd := pgd_p @ (spt_vttbr_pool lspt) in
          let pgd_p0 := Z.lor vttbr0 (pgd_idx0 * 8) in
          let pgd0 := pgd_p0 @ (spt_vttbr_pool lspt) in
          forall (Hpgd_nz: pgd <> 0) (Hpgd0_nz: pgd0 <> 0),
            vttbr <> vttbr0 \/ pgd_idx <> pgd_idx0 -> phys_page pgd <> phys_page pgd0.
      Admitted.

      Lemma pmd_index_diff_res_diff:
        forall addr addr0 cbndx index cbndx0 index0 lspt (Hvalid: valid_lspt lspt),
          let pgd_idx := stage2_pgd_index addr in
          let pgd_idx0 := stage2_pgd_index addr0 in
          let pmd_idx := pmd_index addr in
          let pmd_idx0 :=pmd_index addr0 in
          let vttbr := SMMU_TTBR index cbndx in
          let vttbr0 := SMMU_TTBR index0 cbndx0 in
          let pgd_p := Z.lor vttbr (pgd_idx * 8) in
          let pgd := pgd_p @ (spt_vttbr_pool lspt) in
          let pgd_p0 := Z.lor vttbr0 (pgd_idx0 * 8) in
          let pgd0 := pgd_p0 @ (spt_vttbr_pool lspt) in
          let pmd_p := Z.lor (phys_page pgd) (pmd_idx * 8) in
          let pmd := pmd_p @ (spt_pgd_pool lspt) in
          let pmd_p0 := Z.lor (phys_page pgd0) (pmd_idx0 * 8) in
          let pmd0 := pmd_p0 @ (spt_pgd_pool lspt) in
          forall (Hpgd_nz: pgd <> 0) (Hpgd0_nz: pgd0 <> 0) (Hpmd_nz: pmd <> 0) (Hpmd0_nz: pmd0 <> 0),
            vttbr <> vttbr0 \/ pgd_idx <> pgd_idx0 \/ pmd_idx <> pmd_idx0 -> phys_page pmd <> phys_page pmd0.
      Admitted.

      Lemma set_smmu_pt_spec_pgd_exists:
        forall habd habd' labd cbndx index addr pte f
          (Hspec: set_smmu_pt_spec cbndx index addr pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hpgd: match addr with VZ64 addr => (stage2_pgd_index addr) @  ((SMMU_TTBR index cbndx) @ (spt_pgd_t (spts (shared habd)))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_smmu_pt_spec0 cbndx index addr pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        hsimpl_func Hspec.
        rename z into addr. rename z0 into pte.
        remember (spts (shared habd)) as hspt in *; symmetry in Heqhspt.
        remember (spts (shared labd)) as lspt in *; symmetry in Heqlspt.
        destruct Hrel. rewrite Hhaltl, Heqhspt, Heqlspt in id_spts0.
        clear_hyp; simpl_local. destruct Hlocal.
        unfold local_spt_map in C9. rename C9 into Hspec.
        rewrite Hpgd in Hspec.
        assert (Hpmd: (pmd_index addr) @ ((stage2_pgd_index addr) @ ((SMMU_TTBR index cbndx) @ (spt_pmd_t hspt))) = false).
        { match goal with | |- ?x = false => destruct x eqn: Hpmd end.
          apply Hpmd_t in Hpmd. destruct Hpmd. apply Hpgd_t in H. contra.
          bool_rel_all; omega. bool_rel_all; omega. reflexivity. }
        rewrite Hpmd in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_smmu_pt_spec0.
        repeat autounfold in *.
        autounfold. repeat (srewrite; simpl). bool_rel_all; clear_hyp.
        assert(Hlock: 3 @ (lock labd) = LockOwn true). srewrite. reflexivity.
        assert(Htstate: (tstate labd =? 0) = true). srewrite. reflexivity.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val cbndx index) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (SMMU_TTBR index cbndx) = SMMU_TTBR index cbndx).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. omega. }
        autounfold in vttbr_align. rewrite vttbr_align.
        extract_if. unfold stage2_pgd_index.
        match goal with |- context [Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 8192) end.
        autounfold; apply or_index_range_8192; somega. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
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
        apply or_index_range. omega. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond5.
        rewrite Hpgd_pool_range.
        rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond6.
        destruct_if.
        duplicate Cond6. rename D into Cond7.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond8.
        rewrite Hhaltl, Hlock, Htstate.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond9.
        simpl in Hspec. inv Hspec. clear Cond3 Cond7.
        eexists; split. reflexivity. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T.
        {
          bool_rel_all. constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega.
            + eapply phys_page_a_page. assumption. omega.
            + eapply phys_page_a_page. assumption. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. autounfold; somega. omega.
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
          - reflexivity. - reflexivity.
          - intros.
            destruct_zmap. destruct_zmap. split; intros; try reflexivity. apply or3nz.
            assert_gso. apply or_index_ne_cond_8192. right; assumption. rewrite (ZMap.gso _ _ Hneq).
            apply Hpgd_t. assumption.
            assert_gso. apply or_index_ne_cond_8192. left; assumption. rewrite (ZMap.gso _ _ Hneq).
            apply Hpgd_t. assumption.
          - autounfold; intros.
            destruct_zmap. destruct_zmap. destruct_zmap. split; intros; try reflexivity. split; apply or3nz.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). split. intro T.
            rewrite <- Heq, <- Heq0 in T; apply Hpmd_t in T. destruct T as (? & ?).
            rewrite Heq, Heq0 in H. contra. assumption. intros (? & ?).
            match type of H0 with ?a -> False => assert(a) end. apply Hpgd_next.
            rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range.  omega. autounfold; somega. omega.  contra.
            assert_gso. apply or_index_ne_cond_8192. right; assumption. rewrite (ZMap.gso _ _ Hneq).
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. rewrite phys_or; try assumption.
            match goal with |- phys_page (?a @ _) <> _ => pose proof (Hvttbr_pool a) end.
            destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. omega.
            destruct H. clear H0. omega. rewrite (ZMap.gso _ _ Hneq0). apply Hpmd_t. assumption.
            assert_gso. apply or_index_ne_cond_8192. left; assumption. rewrite (ZMap.gso _ _ Hneq).
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. rewrite phys_or; try assumption.
            match goal with |- phys_page (?a @ _) <> _ => pose proof (Hvttbr_pool a) end.
            destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. omega.
            destruct H. clear H0. omega. rewrite (ZMap.gso _ _ Hneq0). apply Hpmd_t. assumption.
          - intros. repeat autounfold in *.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Heqvttbr; bool_rel.
            autounfold in Heqvttbr. rewrite Heqvttbr in *; rewrite ZMap.gss in Hhpt.
            destruct (addr0 / 4096 =? addr / 4096) eqn:Heqaddr; bool_rel.
            rewrite Heqaddr in Hhpt. rewrite ZMap.gss in Hhpt. inv Hhpt. apply pte_same_cond in Heqaddr.
            destruct Heqaddr as (pgd_same & pmd_same & pte_same).
            constructor. reflexivity.
            simpl. autounfold in *. rewrite Heqvttbr. rewrite pgd_same. rewrite pmd_same. rewrite pte_same.
            repeat rewrite ZMap.gss. right. split. apply or3nz. right. split. apply or3nz. reflexivity.
            autounfold; assumption. autounfold; split; assumption.
            rewrite (ZMap.gso _ _ Heqaddr) in Hhpt.
            rewrite <- Heqvttbr in Hhpt. apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. simpl. autounfold. rewrite Heqvttbr. repeat rewrite ZMap.gss.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:pgd_same; bool_rel.
            rewrite pgd_same; repeat rewrite ZMap.gss. right. split. apply or3nz.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:pmd_same; bool_rel.
            rewrite pmd_same; repeat rewrite ZMap.gss. right. split. apply or3nz.
            destruct (pte_index addr0 =? pte_index addr) eqn:pte_same; bool_rel.
            assert(addr0 / 4096 = addr / 4096).
            apply pte_same_cond; try split_and; try assumption. autounfold; split; assumption. contra.
            destruct Hpte. destruct H. rewrite H0.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next.
            rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. autounfold; somega. omega. destruct H. rewrite Heqvttbr, pgd_same in H; contra.
            destruct Hpte. destruct H. rewrite H0.
            left. assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). split. apply Hpgd_next.
            rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. autounfold; somega. omega. reflexivity.
            destruct H. rewrite Heqvttbr, pgd_same in H; contra.
            assert_gso. apply or_index_ne_cond_8192. right; assumption. rewrite (ZMap.gso _ _ Hneq).
            destruct Hpte. left; rewrite <- Heqvttbr; assumption. right. rewrite <- Heqvttbr.
            destruct H as (T0 & T). split. assumption.
            assert_gso. rewrite phys_or; try assumption. apply vttbr_pool_ne_pgd_next.
            assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). destruct T as [T|T]. left; assumption. right.
            destruct T as [T1 T]. split. assumption.
            assert_gso. rewrite phys_or; try assumption.
            apply pgd_pool_ne_pmd_next. assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq1). assumption. assumption.
            autounfold in *. rewrite (ZMap.gso _ _ Heqvttbr) in Hhpt.
            apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. autounfold. simpl.
            assert_gso. apply or_index_ne_cond_8192. left; assumption. rewrite (ZMap.gso _ _ Hneq).
            destruct Hpte. left; assumption. right.
            destruct H as (T0 & T). split. assumption.
            assert_gso. rewrite phys_or; try assumption. apply vttbr_pool_ne_pgd_next.
            assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). destruct T as [T|T]. left; assumption. right.
            destruct T as [T1 T]. split. assumption.
            assert_gso. rewrite phys_or; try assumption.
            apply pgd_pool_ne_pmd_next. assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq1). assumption. assumption.
        }
        simpl in Hspec; inv Hspec.
        eexists; split. reflexivity. constructor; try assumption. simpl. omega. simpl. reflexivity. simpl. intro T; inversion T.
        erewrite Hpgd_next in Case1. inversion Case1.
        rewrite phys_or; try assumption.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega. omega.
        simpl in Hspec; inv Hspec.
        eexists; split. reflexivity. constructor; try assumption. simpl. omega. simpl. reflexivity. simpl. intro T; inversion T.
        bool_rel. apply Hpgd_t in Case. contra. assumption.
      Qed.

      Lemma set_smmu_pt_spec_pmd_exists:
        forall habd habd' labd cbndx index addr pte f
          (Hspec: set_smmu_pt_spec cbndx index addr pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hpgd: match addr with VZ64 addr => (stage2_pgd_index addr) @  ((SMMU_TTBR index cbndx) @ (spt_pgd_t (spts (shared habd)))) = true end)
          (Hpmd: match addr with VZ64 addr => (pmd_index addr) @ ((stage2_pgd_index addr) @  ((SMMU_TTBR index cbndx) @ (spt_pmd_t (spts (shared habd))))) = false end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_smmu_pt_spec0 cbndx index addr pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        hsimpl_func Hspec.
        rename z into addr. rename z0 into pte.
        remember (spts (shared habd)) as hspt in *; symmetry in Heqhspt.
        remember (spts (shared labd)) as lspt in *; symmetry in Heqlspt.
        destruct Hrel. rewrite Hhaltl, Heqhspt, Heqlspt in id_spts0.
        clear_hyp; simpl_local. destruct Hlocal.
        unfold local_spt_map in C9. rename C9 into Hspec.
        rewrite Hpgd, Hpmd in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_smmu_pt_spec0.
        repeat autounfold in *.
        autounfold. repeat (srewrite; simpl). bool_rel_all; clear_hyp.
        assert(Hlock: 3 @ (lock labd) = LockOwn true). srewrite. reflexivity.
        assert(Htstate: (tstate labd =? 0) = true). srewrite. reflexivity.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val cbndx index) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (SMMU_TTBR index cbndx) = SMMU_TTBR index cbndx).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. omega. }
        autounfold in vttbr_align. rewrite vttbr_align.
        extract_if. unfold stage2_pgd_index.
        match goal with |- context [Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 8192) end.
        autounfold; apply or_index_range_8192; somega. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        bool_rel. apply Hpgd_t in Hpgd. inversion Hpgd. assumption. assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (spt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= spt_pgd_next lspt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Heqlspt. rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond3.
        destruct_if.
        duplicate Cond3. rename D into Cond4.
        simpl. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond5.
        rewrite Hhaltl, Hlock, Htstate.
        extract_if. erewrite phys_or; try solve [assumption|omega].
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega.
        apply andb_true_iff; split; bool_rel; omega. rewrite Cond6.
        rewrite andb_comm in Hspec; simpl in Hspec.
        replace (spt_pgd_next lspt <=? 2162688) with true in Hspec by (symmetry; bool_rel; omega).
        inv Hspec. clear Cond4.
        eexists; split. reflexivity. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T.
        {
          bool_rel_all. constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + apply Hvttbr_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega.
            + assumption.
            + eapply phys_page_a_page. assumption. omega.
            + assert_gso. match goal with |- context[?a @ (spt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity.  autounfold; somega. omega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= spt_pgd_next (spts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpgd_next. omega.
            + assert_gso. erewrite phys_or; try solve [assumption|omega].
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. autounfold; somega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. omega.
            + apply Hvttbr_pool.
            + destruct_zmap. right. erewrite phys_or; try solve [assumption|omega].
              rewrite ZMap.gss. split_and; try omega.
              pose proof (Hpgd_pool addr0). destruct H. left; assumption.
              destruct H as (? & ?). right. split. omega.
              assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
          - reflexivity. - reflexivity.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = ((stage2_pgd_index addr0) @ ((SMMU_TTBR index0 cbndx0) @ (spt_pgd_t (spts (shared habd)))))) end.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Httbr_same; bool_rel; autounfold in Httbr_same.
            rewrite Httbr_same. rewrite ZMap.gss.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. autounfold; rewrite Httbr_same; rewrite Hpgd. reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). autounfold; rewrite Httbr_same; reflexivity.
            rewrite (ZMap.gso _ _ Httbr_same). reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - autounfold; intros.
            destruct_zmap. destruct_zmap. destruct_zmap. split; intros; try reflexivity. split. assumption. apply or3nz.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). split. intro T.
            rewrite <- Heq, <- Heq0 in T; apply Hpmd_t in T. rewrite Heq, Heq0 in *; assumption. assumption.
            rewrite <- Heq, <- Heq0. apply Hpmd_t. assumption.
            split. intro T. apply Hpmd_t in T.  destruct T.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. apply pgd_index_diff_res_diff; auto. rewrite (ZMap.gso _ _ Hneq). split; assumption. assumption.
            intros (? & ?). assert_gsoH H0. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. apply pgd_index_diff_res_diff; auto. rewrite (ZMap.gso _ _ Hneq) in H0.
            apply Hpmd_t. assumption. split; assumption.
            split. intro T. apply Hpmd_t in T.  destruct T.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. apply pgd_index_diff_res_diff; auto. rewrite (ZMap.gso _ _ Hneq). split; assumption. assumption.
            intros (? & ?). assert_gsoH H0. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left. apply pgd_index_diff_res_diff; auto. rewrite (ZMap.gso _ _ Hneq) in H0.
            apply Hpmd_t. assumption. split; assumption.
          - intros. repeat autounfold in *.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Heqvttbr; bool_rel.
            autounfold in Heqvttbr. rewrite Heqvttbr in *; rewrite ZMap.gss in Hhpt.
            destruct (addr0 / 4096 =? addr / 4096) eqn:Heqaddr; bool_rel.
            rewrite Heqaddr in Hhpt. rewrite ZMap.gss in Hhpt. inv Hhpt. apply pte_same_cond in Heqaddr.
            destruct Heqaddr as (pgd_same & pmd_same & pte_same).
            constructor. reflexivity.
            simpl. autounfold in *. rewrite Heqvttbr. rewrite pgd_same. rewrite pmd_same. rewrite pte_same.
            repeat rewrite ZMap.gss. right. split. assumption. right. split. apply or3nz. reflexivity.
            autounfold; assumption. autounfold; split; assumption.
            rewrite (ZMap.gso _ _ Heqaddr) in Hhpt.
            rewrite <- Heqvttbr in Hhpt. apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. simpl. autounfold. rewrite Heqvttbr. repeat rewrite ZMap.gss.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:pgd_same; bool_rel.
            rewrite pgd_same; repeat rewrite ZMap.gss. right. split. assumption.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:pmd_same; bool_rel.
            rewrite pmd_same; repeat rewrite ZMap.gss. right. split. apply or3nz.
            destruct (pte_index addr0 =? pte_index addr) eqn:pte_same; bool_rel.
            assert(addr0 / 4096 = addr / 4096).
            apply pte_same_cond; try split_and; try assumption. autounfold; split; assumption. contra.
            destruct Hpte. destruct H. rewrite H0.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next.
            rewrite phys_or; try assumption.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. autounfold; somega. omega. destruct H. destruct H0.
            destruct H0. rewrite H1. assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq). rewrite phys_or; try assumption.
            apply Hpmd_next.
            match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
            apply or_index_range. omega. autounfold; somega. omega.
            destruct H0; rewrite Heqvttbr, pgd_same, pmd_same in H0; contra.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            right; assumption. rewrite (ZMap.gso _ _ Hneq).
            destruct Hpte. destruct H; rewrite Heqvttbr, pgd_same in H; contra.
            destruct H as (T0 & T). rewrite <- Heqvttbr, <- pgd_same.
            destruct T as [T|T]. left; assumption. right. destruct T as (T1 & T).
            split. assumption. assert_gso. rewrite phys_or; try assumption.
            apply pgd_pool_ne_pmd_next. assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). assumption.
            rewrite <- Heqvttbr. destruct Hpte as [T|T]. left; assumption. right.
            destruct T as (T8 & T). split. assumption.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed. left.
            apply pgd_index_diff_res_diff; auto. autounfold; rewrite Heqvttbr; assumption.
            rewrite (ZMap.gso _ _ Hneq). destruct T as [T|T]. left; assumption. right.
            destruct T as (T2 & T). split. assumption.
            assert_gso. rewrite phys_or; try assumption.
            apply pgd_pool_ne_pmd_next. assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). assumption. assumption.
            autounfold in *. rewrite (ZMap.gso _ _ Heqvttbr) in Hhpt.
            apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. autounfold. simpl.
            destruct Hpte as [T|T]. left; assumption. right.
            destruct T as (T0 & T). split. assumption.
            assert_gso. apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed. left.
            apply pgd_index_diff_res_diff; auto.
            rewrite (ZMap.gso _ _ Hneq). destruct T as [T|T]. left; assumption. right.
            destruct T as (T2 & T). split. assumption.
            assert_gso. rewrite phys_or; try assumption.
            apply pgd_pool_ne_pmd_next. assumption. autounfold; somega. autounfold; somega.
            rewrite (ZMap.gso _ _ Hneq0). assumption. assumption.
        }
        rewrite andb_comm in Hspec; simpl in Hspec; inv Hspec.
        eexists; split. reflexivity. constructor; try assumption. simpl. omega. simpl. reflexivity. simpl. intro T; inversion T.
        bool_rel.
        assert((pmd_index addr) @ ((stage2_pgd_index addr) @ ((65536 + (index * 8 + cbndx) * 4096 * 2) @ (spt_pmd_t hspt))) = true).
        apply Hpmd_t. assumption. split; assumption. contra.
      Qed.

      Lemma set_smmu_pt_spec_pte_exists:
        forall habd habd' labd cbndx index addr pte f
          (Hspec: set_smmu_pt_spec cbndx index addr pte habd = Some habd')
          (Hhalt: halt habd = false)
          (Hpgd: match addr with VZ64 addr => (stage2_pgd_index addr) @  ((SMMU_TTBR index cbndx) @ (spt_pgd_t (spts (shared habd)))) = true end)
          (Hpmd: match addr with VZ64 addr => (pmd_index addr) @ ((stage2_pgd_index addr) @  ((SMMU_TTBR index cbndx) @ (spt_pmd_t (spts (shared habd))))) = true end)
          (Hrel: relate_RData f habd labd),
        exists labd', set_smmu_pt_spec0 cbndx index addr pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros.
        assert(range3: 0 <= 3 < 4096) by omega.
        pose proof phys_page_or_not_change as phys_or.
        assert(Hhaltl: halt labd = false).
        { destruct Hrel. srewrite. reflexivity. }
        hsimpl_func Hspec.
        rename z into addr. rename z0 into pte.
        remember (spts (shared habd)) as hspt in *; symmetry in Heqhspt.
        remember (spts (shared labd)) as lspt in *; symmetry in Heqlspt.
        destruct Hrel. rewrite Hhaltl, Heqhspt, Heqlspt in id_spts0.
        clear_hyp; simpl_local. destruct Hlocal.
        unfold local_spt_map in C9. rename C9 into Hspec.
        rewrite Hpgd, Hpmd in Hspec. simpl_hyp Hspec; contra.
        duplicate Hvalid. destruct D.
        unfold set_smmu_pt_spec0.
        repeat autounfold in *.
        autounfold. repeat (srewrite; simpl). bool_rel_all; clear_hyp.
        assert(Hlock: 3 @ (lock labd) = LockOwn true). srewrite. reflexivity.
        assert(Htstate: (tstate labd =? 0) = true). srewrite. reflexivity.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        pose proof (vttbr_val cbndx index) as Hvttbr. autounfold in Hvttbr.
        assert(vttbr_align: phys_page (SMMU_TTBR index cbndx) = SMMU_TTBR index cbndx).
        { autounfold. rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. omega. omega. }
        autounfold in vttbr_align. rewrite vttbr_align.
        extract_if. unfold stage2_pgd_index.
        match goal with |- context [Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 8192) end.
        autounfold; apply or_index_range_8192; somega. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        extract_if. apply Hvttbr_pool_range. rewrite Cond1.
        rewrite andb_comm. simpl. destruct_if.
        bool_rel. apply Hpgd_t in Hpgd. inversion Hpgd. assumption. assumption.
        rewrite Hvttbr_pool_range. rewrite Hhaltl, Hlock. rewrite Case.
        extract_if. match goal with |- context[?a @ (spt_vttbr_pool _)] => pose proof (Hvttbr_pool a) end.
        destruct H. rewrite H in Case. inversion Case. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= spt_pgd_next lspt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond2.
        rewrite Heqlspt. rewrite Hpgd_pool_range. rewrite andb_comm. simpl. destruct_if.
        apply Hpmd_t in Hpmd. destruct Hpmd. bool_rel; contra. assumption.
        rewrite Hpgd_pool_range. rewrite Hhaltl, Hlock, Htstate.
        extract_if. match goal with |- context[?a @ (spt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
        destruct H. rewrite H in Case0. inversion Case0. destruct H. clear H0.
        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
        apply or_index_range. omega. autounfold; somega.
        bool_rel_all; apply andb_true_iff; split; bool_rel. omega.
        match type of H0 with _ <= _ < ?a => assert(a <= spt_pmd_next lspt) end.
        eapply phys_page_lt_4096. apply phys_page_fixed. assumption. destruct H; assumption. omega. rewrite Cond3.
        replace (spt_pgd_next lspt <=? 2162688) with true in Hspec by (symmetry; bool_rel; omega).
        replace (spt_pmd_next lspt <=? 3211264) with true in Hspec by (symmetry; bool_rel; omega).
        inv Hspec. eexists; split. reflexivity. constructor; try assumption.
        simpl. reflexivity. simpl. rewrite Hhaltl. reflexivity. simpl. intro T; clear T.
        {
          bool_rel_all. constructor; simpl.
          - constructor; simpl; autounfold; intros.
            + apply Hvttbr_pool_range.
            + apply Hpgd_pool_range.
            + destruct_zmap. apply andb_true_iff; split; bool_rel; somega.
              apply Hpmd_pool_range.
            + omega. + omega.
            + assumption. + assumption.
            + apply Hpgd_next. assumption.
            + assert_gso. match goal with |- context[?a @ (spt_pgd_pool _)] => pose proof (Hpgd_pool a) end.
              destruct H0. rewrite H0. replace (phys_page 0) with 0 by reflexivity.
              match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. reflexivity. autounfold; somega. omega.
              destruct H0. match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
              apply or_index_range. omega. autounfold; somega.
              match type of H2 with _ <= _ < ?a => assert(a <= spt_pmd_next (spts (shared labd))) end.
              eapply phys_page_lt_4096. apply phys_page_fixed. assumption. omega. omega.
              rewrite (ZMap.gso _ _ Hneq). apply Hpmd_next. omega.
            + apply Hvttbr_pool.
            + apply Hpgd_pool.
          - reflexivity. - reflexivity.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = ((stage2_pgd_index addr0) @ ((SMMU_TTBR index0 cbndx0) @ (spt_pgd_t (spts (shared habd)))))) end.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Httbr_same; bool_rel; autounfold in Httbr_same.
            rewrite Httbr_same. rewrite ZMap.gss.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss. autounfold; rewrite Httbr_same; rewrite Hpgd. reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). autounfold; rewrite Httbr_same; reflexivity.
            rewrite (ZMap.gso _ _ Httbr_same). reflexivity.
            rewrite H. apply Hpgd_t. assumption.
          - intros; autounfold.
            match goal with |- ?c = true <-> _ =>
                            assert(c = (pmd_index addr0) @ ((stage2_pgd_index addr0) @ ((SMMU_TTBR index0 cbndx0) @ (spt_pmd_t (spts (shared habd)))))) end.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Httbr_same; bool_rel; autounfold in Httbr_same.
            rewrite Httbr_same. rewrite ZMap.gss.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:Hpgd_same; bool_rel.
            rewrite Hpgd_same. rewrite ZMap.gss.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:Hpmd_same; bool_rel.
            rewrite Hpmd_same. rewrite ZMap.gss.
            autounfold; rewrite Httbr_same; rewrite Hpmd. reflexivity.
            rewrite (ZMap.gso _ _ Hpmd_same). rewrite <- Httbr_same; reflexivity.
            rewrite (ZMap.gso _ _ Hpgd_same). autounfold; rewrite Httbr_same; reflexivity.
            rewrite (ZMap.gso _ _ Httbr_same). reflexivity.
            rewrite H. apply Hpmd_t. assumption.
          - intros. repeat autounfold in *.
            destruct (SMMU_TTBR index0 cbndx0 =? SMMU_TTBR index cbndx) eqn:Heqvttbr; bool_rel.
            autounfold in Heqvttbr. rewrite Heqvttbr in *; rewrite ZMap.gss in Hhpt.
            destruct (addr0 / 4096 =? addr / 4096) eqn:Heqaddr; bool_rel.
            rewrite Heqaddr in Hhpt. rewrite ZMap.gss in Hhpt. inv Hhpt. apply pte_same_cond in Heqaddr.
            destruct Heqaddr as (pgd_same & pmd_same & pte_same).
            constructor. reflexivity.
            simpl. autounfold in *. rewrite Heqvttbr. rewrite pgd_same. rewrite pmd_same. rewrite pte_same.
            repeat rewrite ZMap.gss. right. split. assumption. right. split. assumption. reflexivity.
            autounfold; assumption. autounfold; split; assumption.
            rewrite (ZMap.gso _ _ Heqaddr) in Hhpt.
            rewrite <- Heqvttbr in Hhpt. apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. simpl. autounfold. rewrite Heqvttbr. repeat rewrite ZMap.gss.
            rewrite <- Heqvttbr.
            destruct Hpte as [T|T]. left; assumption. right. destruct T as (T1 & T). split. assumption.
            destruct T as [T|T]. left; assumption. right. destruct T as (T2 & T). split. assumption.
            destruct_zmap. match type of Heq with ?a = ?b => assert(a <> b) end.
            destruct (stage2_pgd_index addr0 =? stage2_pgd_index addr) eqn:pgd_same; bool_rel.
            destruct (pmd_index addr0 =? pmd_index addr) eqn:pmd_same; bool_rel.
            destruct (pte_index addr0 =? pte_index addr) eqn:pte_same; bool_rel.
            assert(addr0 / 4096 = addr / 4096).
            apply pte_same_cond; try split_and; try assumption. autounfold; split; assumption. contra.
            apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed. right; assumption.
            apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left; apply pmd_index_diff_res_diff; auto. autounfold; rewrite Heqvttbr; assumption.
            autounfold; rewrite Heqvttbr; assumption.
            apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left; apply pmd_index_diff_res_diff; auto. autounfold; rewrite Heqvttbr; assumption.
            autounfold; rewrite Heqvttbr; assumption. contra. assumption. assumption.
            autounfold in *. rewrite (ZMap.gso _ _ Heqvttbr) in Hhpt.
            apply Hrelate in Hhpt. destruct Hhpt; autounfold in *.
            constructor. assumption. autounfold. simpl.
            destruct Hpte as [T|T]. left; assumption. right. destruct T as (T1 & T). split. assumption.
            destruct T as [T|T]. left; assumption. right. destruct T as (T2 & T). split. assumption.
            destruct_zmap. match type of Heq with ?a = ?b => assert(a <> b) end.
            apply or_index_ne_cond. apply phys_page_fixed. apply phys_page_fixed.
            left; apply pmd_index_diff_res_diff; auto. contra. assumption. assumption.
        }
      Qed.

    End FreshPrim.

  End WITHMEM.

End MmioSPTWalkProofHigh.
```
