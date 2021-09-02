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
Require Import PageIndex.Layer.
Require Import PageManager.Spec.
Require Import PageIndex.Spec.
Require Import PageManager.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PageManagerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := PageManager_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := PageIndex_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition valid_regions (regions: ZMap.t Memblock) :=
      forall i, let reg := (ZMap.get i regions) in
           is_addr (mb_base reg) = true /\ is_int64 (mb_size reg) = true /\ is_addr (mb_base reg + mb_size reg) = true /\
           ((is_s2page (mb_index reg) = true /\ is_s2page (mb_index reg + mb_size reg / PAGE_SIZE) = true) \/ mb_index reg = INVALID64).

    Lemma mem_region_succ:
      forall addr adt (Hvalid: valid_regions (regions adt)) (Hcnt: is_memblock (region_cnt adt) = true),
      exists i' res, region_search_loop (Z.to_nat (region_cnt adt)) addr 0 INVALID (regions adt) = Some (i', res) /\
                     is_memblock i' = true /\ (res = INVALID \/ (is_memblock res = true /\
                                                                 addr >= mb_base (ZMap.get res (regions adt)) /\
                                                                 addr < mb_base (ZMap.get res (regions adt)) +
                                                                        mb_size (ZMap.get res (regions adt)))).
    Proof.
      intros. unfold valid_regions in Hvalid.
      assert(forall n, Z.of_nat n <= (region_cnt adt) ->
                       exists i' res, region_search_loop n addr 0 INVALID (regions adt) = Some (i', res) /\
                                      (0 <=? i') = true /\ i' = Z.of_nat n /\ (res = INVALID \/
                                                                               (is_memblock res = true /\
                                                                                addr >= mb_base (ZMap.get res (regions adt)) /\
                                                                                addr < mb_base (ZMap.get res (regions adt)) +
                                                                                       mb_size (ZMap.get res (regions adt))))).
      { autounfold. induction n. simpl. intros.
        eexists. eexists. split_and. reflexivity. auto.
        omega. left. reflexivity.
        intros. rewrite Nat2Z.inj_succ, succ_plus_1 in *. simpl.
        assert (Z.of_nat n <= region_cnt adt) by omega.
        apply IHn in H0. destruct H0 as (i0 & res0 & spec0 & Hi0 & Hi0' & Hres0).
        rewrite spec0. autounfold. rewrite Hi0.
        assert(i0 <? 32 = true).
        { rewrite Hi0'. autounfold in *. destruct_con. bool_rel. omega. }
        rewrite H0. simpl.
        assert((0 <=? res0) && (res0 <=? 4294967295) = true).
        { destruct Hres0. rewrite H1. auto.
          destruct H1. destruct_con. simpl. bool_rel. omega. }
        rewrite H1. pose proof (Hvalid i0). destruct H2 as (Hb & Hs & Hbs & Hidx).
        autounfold in *. rewrite Hb, Hs, Hbs.
        destruct ((mb_base (ZMap.get i0 (regions adt)) <=? addr) &&
                 (addr <? mb_base (ZMap.get i0 (regions adt)) + mb_size (ZMap.get i0 (regions adt)))) eqn:Haddr.
        eexists. eexists. split_and. reflexivity. bool_rel. omega. omega.
        right. rewrite Hi0, H0.
        destruct_con; bool_rel.
        split_and. reflexivity. omega. omega.
        eexists. eexists. split_and. reflexivity. bool_rel. omega. omega.
        assumption. }
      assert(Z.of_nat (Z.to_nat (region_cnt adt)) <= region_cnt adt).
      { rewrite Z2Nat.id. reflexivity. autounfold in Hcnt. destruct_con. bool_rel. assumption. }
      pose proof (H _ H0).
      destruct H1 as (i0 & res0 & spec0 & Hi0 & Hi0' & Hres0).
      exists i0, res0. split_and; try assumption.
      bool_rel. rewrite Z2Nat.id in Hi0'. rewrite Hi0'. assumption.
      autounfold in *. destruct_con. bool_rel. assumption.
    Qed.

    Lemma page_index_succ:
      forall addr adt (Haddr: is_addr addr = true) (Hvalid: valid_regions (regions adt)) (Hcnt: is_memblock (region_cnt adt) = true),
      exists idx , get_s2_page_index_spec (VZ64 addr) adt = Some (VZ64 idx) /\ (idx = INVALID64 \/ is_s2page idx = true).
    Proof.
      intros. unfold valid_regions in Hvalid. simpl. rewrite Hcnt. simpl. autounfold.
      assert((0 <=? addr) && (addr <? 281474976710656) = true).
      { autounfold in Haddr. assumption. }
      {
        rewrite H.
        {
          exploit mem_region_succ. eauto 1; intros (labd' & Hspec & Hrel). rewrite Hcnt. reflexivity. intros.
          destruct H0 as (i' & res & Hsr & Him & Hrest). rewrite Hsr.

          assert((0 <=? i') && (i' <? 32) = true).
          { unfold is_memblock in Him. destruct Him. autounfold. reflexivity. }
            rewrite H0.
          assert(((0 <=? res) && (res <=? 4294967295)) = true).
            {
              unfold INVALID, is_memblock in Hrest. unfold MAX_MEMBLOCK_NUM in Hrest.
              destruct Hrest as [Hrest1 | Hrest2  _].
              { rewrite Hrest1. reflexivity. }
              { destruct Hrest2. rewrite andb_true_iff in H1.
                destruct H1 as [H1' H1'']. rewrite H1'.
                assert(res <= 4294967295). bool_rel. omega. simpl. bool_rel. rewrite H1.
                reflexivity. }
            }
            rewrite H1. unfold INVALID in Hrest.
            destruct (res =? 4294967295) eqn:Inv. split_and.
            { eexists. split_and. reflexivity. left. reflexivity. }
            destruct Hrest.  bool_rel. contradiction.
            assert((0<=?res) && (res <? 32) = true).
            { destruct H2 as (H2'). unfold is_memblock in H2'. unfold MAX_MEMBLOCK_NUM in H2'. rewrite H2'. reflexivity. }
            rewrite H3. pose proof (Hvalid res).
            destruct H4 as (Hb & Hs & Hbs & Hidx). unfold is_addr in Hb. unfold KVM_ADDR_SPACE in Hb. rewrite Hb.
            unfold is_s2page, PAGE_SIZE, INVALID64 in Hidx. unfold MAX_S2PAGE_NUM in Hidx.
            destruct Hidx. destruct H4. rewrite andb_true_iff in H4. destruct H4. rewrite H4.
            assert((mb_index (ZMap.get res (regions adt)) <=? 18446744073709551615 = true)). bool_rel. omega.
            rewrite H7. simpl.
            destruct (mb_index (ZMap.get res (regions adt)) =? 18446744073709551615).
            { eexists. split_and. reflexivity. left. reflexivity. }
            {
              assert(mb_index (ZMap.get res (regions adt)) <? 281474976710656 = true).
              { pose proof (Hvalid res).
                repeat match goal with | [H: _ /\ _ |- _] => destruct H end.
                bool_rel. omega. }
              {
                rewrite H8. destruct H2 as (Ht & Hbr & Hbrs).
                assert( addr >=? mb_base (ZMap.get res (regions adt)) = true).
                { bool_rel. omega. }
                {
                  rewrite H2.
                  eexists. rewrite andb_true_iff in H5. split_and. trivial.
                  right.
                  assert((0 <=? mb_index (ZMap.get res (regions adt)) + (addr - mb_base (ZMap.get res (regions adt))) / 4096)
                           &&(mb_index (ZMap.get res (regions adt)) + (addr - mb_base (ZMap.get res (regions adt))) / 4096 <? 16777216) = true).
                  { apply andb_true_iff. split.
                    repeat match goal with
                           | [H:_ && _ = true |- _] => apply andb_true_iff in H; destruct H
                           end.
                     bool_rel.
                     assert((addr - mb_base (ZMap.get res (regions adt))) <= mb_size (ZMap.get res (regions adt))) by omega.
                     assert(0 <= (addr - mb_base (ZMap.get res (regions adt))) / 4096).
                     { apply Z_div_pos. omega. omega. }
                     omega.
                     repeat match goal with
                           | [H:_ && _ = true |- _] => apply andb_true_iff in H; destruct H
                           end.
                     bool_rel.
                     assert((addr - mb_base (ZMap.get res (regions adt))) <= mb_size (ZMap.get res (regions adt))) by omega.
                     assert((addr - mb_base (ZMap.get res (regions adt))) / 4096 <= mb_size (ZMap.get res (regions adt)) / 4096).
                     { apply Z_div_le.  omega.  omega. }
                     destruct H5. bool_rel. omega. }
                  apply H9.
                }
              }
            }
            {
              rewrite H4. simpl. eexists. split_and. reflexivity. left. reflexivity.
            }
        }
      }
      Qed.

    Definition valid_regions2 (regions: ZMap.t Memblock) :=
      forall i j (Hne: i > j) ,
        let reg1 := (ZMap.get i regions) in
        let reg2 := (ZMap.get j regions) in
        mb_base reg1 >= mb_base reg2 + mb_size reg2 /\ mb_index reg1 > mb_index reg2 + mb_size reg2.

    Lemma page_index_unique:
      forall adt pfn1 pfn2 idx1 idx2
        (Hhalt: halt adt = false)
        (Hregion: valid_regions (regions adt))
        (Hregion2: valid_regions2 (regions adt))
        (Hblock: is_memblock (region_cnt adt) = true)
        (Hspec1: get_s2_page_index_spec (VZ64 (pfn1 * PAGE_SIZE)) adt = Some (VZ64 idx1))
        (Hspec2: get_s2_page_index_spec (VZ64 (pfn2 * PAGE_SIZE)) adt = Some (VZ64 idx2))
        (Hidx1: is_s2page idx1 = true) (Hidx2: is_s2page idx2 = true),
        idx1 = idx2 -> pfn1 = pfn2.
    Proof.
      intros. hsimpl_func Hspec1; hsimpl_func Hspec2;
                repeat match goal with
                       | [H: is_s2page 18446744073709551615 = true |- _] =>
                         autounfold in H; apply andb_true_iff in H; destruct H; bool_rel; omega
                       | [H1: 18446744073709551615 = ?x, H2: is_s2page ?x = true |- _] => rewrite <- H1 in H2
                       | _ => idtac
                       end.

      pose proof (mem_region_succ (pfn1 * 4096) adt Hregion Hblock).
      destruct H as (i' & res & Hreg1 & prop1).
      unfold INVALID in Hreg1. rewrite C1 in Hreg1. inv Hreg1.
      pose proof (mem_region_succ (pfn2 * 4096) adt Hregion Hblock).
      destruct H as (i'0 & res0 & Hreg2 & prop2).
      unfold INVALID in Hreg2. rewrite C13 in Hreg2. inv Hreg2.
      repeat (destruct_con; contra).
      repeat match goal with
             | [H: is_memblock _ = true /\ (_ = INVALID \/ _) |- _] => destruct H
             | [H1: _ = INVALID \/ is_memblock _ = true /\ _ |- _] => destruct H1
             | [H2: _ = INVALID |- _] => autounfold in H2; bool_rel; contradiction
             | [H3: is_memblock _ = true /\ _ /\ _ |- _] => destruct H3
             | _ => idtac
             end.
      unfold valid_regions2 in Hregion2.
      destruct (res0 >? res) eqn:Hrel1.
      pose proof (Hregion2 res0 res) as Hr.
      bool_rel. destruct Hr. omega.
      assert ((pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) < mb_size (ZMap.get res (regions adt))).
      omega.
      assert((mb_index (ZMap.get res (regions adt)) + (pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096) <=
             mb_index (ZMap.get res (regions adt)) + mb_size (ZMap.get res (regions adt))).
      apply Zplus_le_compat_l.
      assert((pfn1 * 4096 - mb_base res @ (regions adt)) / 4096 <=  (pfn1 * 4096 - mb_base res @ (regions adt))).
      apply Zdiv_le_upper_bound. omega. omega. omega.
      assert((pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) / 4096 >= 0).
      assert((pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) >= 0). omega.
      apply (Z_div_ge  (pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) 0 4096) in H10.
      rewrite Zdiv_0_l in H10. omega. reflexivity.
      assert( mb_index (ZMap.get res (regions adt)) + (pfn2 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096 <
              mb_index (ZMap.get res0 (regions adt)) + (pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) / 4096 ) as Hf.
      omega. contradict Hf. omega.
      destruct (res0 <? res) eqn:Hrel2.
      pose proof (Hregion2 res res0) as Hr. destruct Hr. bool_rel. omega.
      assert ((pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) < mb_size (ZMap.get res0 (regions adt))).
      omega.
      assert((mb_index (ZMap.get res0 (regions adt)) + (pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) / 4096) <
             mb_index (ZMap.get res0 (regions adt)) + mb_size (ZMap.get res0 (regions adt))).
      apply Zplus_lt_compat_l.
      assert((pfn2 * 4096 - mb_base res0 @ (regions adt)) / 4096 <= (pfn2 * 4096 - mb_base res0 @ (regions adt))).
      apply Zdiv_le_upper_bound. omega. omega. omega.
      assert((mb_index (ZMap.get res0 (regions adt)) + (pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) / 4096) <
             (mb_index (ZMap.get res (regions adt)))).
      omega.
      assert((pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096 >= 0).
      assert((pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) >= 0). omega.
      apply (Z_div_ge  (pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) 0 4096) in H11.
      rewrite Zdiv_0_l in H11. omega. reflexivity.
      assert(mb_index (ZMap.get res0 (regions adt)) + (pfn2 * 4096 - mb_base (ZMap.get res0 (regions adt))) / 4096 <
             mb_index (ZMap.get res (regions adt)) + (pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096 ) as Hf.
      omega. contradict Hf. omega.
      assert (res0 = res). bool_rel. omega.
      srewrite.
      assert ((pfn2 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096 = (pfn1 * 4096 - mb_base (ZMap.get res (regions adt))) / 4096).
      omega. clear_hyp.
      assert(forall a b, a - b = a + (-b)). intros. omega.
      repeat rewrite H3 in H7. rewrite  Z_div_plus_full_l in H7. rewrite  Z_div_plus_full_l in H7.
      omega. intro T; inv T. intro T; inv T.
    Qed.

    Inductive relate_s2page (hadt: HDATA) (ladt: LDATA) :=
    | RELATE_S2PAGE:
        forall (Hs2rel: forall pfn idx (Hidx: get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) ladt = Some (VZ64 idx)),
              (idx = INVALID64 <-> s2_owner (ZMap.get pfn (s2page (shared hadt))) = INVALID) /\
              (idx = INVALID64 -> s2_count (ZMap.get pfn (s2page (shared hadt))) = INVALID) /\
              (idx = INVALID64 -> s2_gfn (ZMap.get pfn (s2page (shared hadt))) = INVALID64) /\
              (is_s2page idx = true -> ZMap.get pfn (s2page (shared hadt)) = ZMap.get idx (s2page (shared ladt)))),
          relate_s2page hadt ladt.

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
          region_cnt_rel: is_memblock (region_cnt ladt) = true;
          id_regions: regions hadt = regions ladt;
          Hreg0: valid_regions (regions ladt);
          Hreg1: valid_regions2 (regions ladt);
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
          id_s2page: relate_s2page hadt ladt;
          id_core_data: core_data (shared hadt) = core_data (shared ladt);
          id_vminfos: vminfos (shared hadt) = vminfos (shared ladt);
          id_spts: spts (shared hadt) = spts (shared ladt);
          id_smmu_vmid: smmu_vmid (shared hadt) = smmu_vmid (shared ladt);
          id_npts: npts (shared hadt) = npts (shared ladt)
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

      Lemma get_pfn_owner_spec_exists:
        forall habd labd pfn res f
               (Hspec: get_pfn_owner_spec pfn habd = Some res)
               (Hrel: relate_RData f habd labd),
          get_pfn_owner_spec0 pfn labd = Some res.
      Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec.
        unfold get_pfn_owner_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl. unfold Spec.check_spec.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_owner z @ (s2page (shared habd)) = 4294967295). apply owner_rel. reflexivity.
          rewrite H. reflexivity.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.get_s2_page_vmid_spec, Spec.check_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          exploit idx_rel. apply andb_true_iff; split; bool_rel; assumption.
          intro Hidx. rewrite Hidx in *. srewrite. reflexivity.
      Qed.

      Lemma get_pfn_owner_spec_ref:
        compatsim (crel RData RData) (gensem get_pfn_owner_spec) get_pfn_owner_spec_low.
      Proof.
        Opaque get_pfn_owner_spec.
        compatsim_simpl (@match_RData).
        exploit get_pfn_owner_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma set_pfn_owner_spec_exists:
        forall habd habd' labd pfn vmid f
          (Hspec: set_pfn_owner_spec pfn vmid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_pfn_owner_spec0 pfn vmid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec.
        unfold set_pfn_owner_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_owner z @ (s2page (shared habd)) = 4294967295). apply owner_rel. reflexivity.
          bool_rel; contra.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.set_s2_page_vmid_spec, Spec.check_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_owner z @ (s2page (shared habd')) <> 4294967295).
          intro T. apply owner_rel in T. bool_rel; contra. bool_rel; contra.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          extract_if. apply andb_true_iff; split; bool_rel; assumption.
          rewrite Cond0. apply idx_rel in Cond0. rewrite Cond0 in *.
          eexists; split. reflexivity.
          constructor; simpl; srewrite; simpl; try assumption; try reflexivity.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          constructor; simpl.
          Local Transparent get_s2_page_index_spec.
          unfold get_s2_page_index_spec in *; simpl in *.
          intros. pose proof (Hs2rel _ _ Hidx).
          destruct_zmap; simpl. subst; srewrite.
          autounfold in *. rewrite Hget_index in Hidx. inv Hidx.
          split_and. split. intros. generalize Hcond4. generalize H0.
          repeat match goal with | [H: _ |- _] => clear H end. intros. omega.
          intros. generalize C4. generalize H0.
          repeat match goal with | [H: _ |- _] => clear H end.
          intros. bool_rel_all; omega.
          apply H. apply H.
          intros. rewrite ZMap.gss. reflexivity.
          split_and. apply H. apply H. apply H.
          intros. assert_gso. intro T. eapply (page_index_unique labd pfn z) in T. contra.
          assumption. assumption. assumption.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          apply Hidx. apply Hget_index. assumption. autounfold.
          apply andb_true_iff; split; bool_rel; assumption.
          rewrite (ZMap.gso _ _ Hneq). apply H. apply H0.
      Qed.

      Lemma set_pfn_owner_spec_ref:
        compatsim (crel RData RData) (gensem set_pfn_owner_spec) set_pfn_owner_spec_low.
      Proof.
        Opaque set_pfn_owner_spec.
        compatsim_simpl (@match_RData).
        exploit set_pfn_owner_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma get_pfn_count_spec_exists:
        forall habd labd pfn res f
          (Hspec: get_pfn_count_spec pfn habd = Some res)
          (Hrel: relate_RData f habd labd),
          get_pfn_count_spec0 pfn labd = Some res.
      Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec.
        unfold get_pfn_count_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl. unfold Spec.check_spec.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_count z @ (s2page (shared habd)) = 4294967295). apply count_rel. reflexivity.
          rewrite H. reflexivity.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.get_s2_page_count_spec, Spec.check_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          exploit idx_rel. apply andb_true_iff; split; bool_rel; assumption.
          intro Hidx. rewrite Hidx in *. srewrite. reflexivity.
        Qed.

      Lemma get_pfn_count_spec_ref:
        compatsim (crel RData RData) (gensem get_pfn_count_spec) get_pfn_count_spec_low.
      Proof.
        Opaque get_pfn_count_spec.
        compatsim_simpl (@match_RData).
        exploit get_pfn_count_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma set_pfn_count_spec_exists:
        forall habd habd' labd pfn count f
               (Hspec: set_pfn_count_spec pfn count habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_pfn_count_spec0 pfn count labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec.
        unfold set_pfn_count_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_count z @ (s2page (shared habd)) = 4294967295). apply count_rel. reflexivity.
          assert(s2_owner z @ (s2page (shared habd)) = 4294967295). apply owner_rel. reflexivity.
          bool_rel; contra.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.set_s2_page_count_spec, Spec.check_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_owner z @ (s2page (shared habd')) <> 4294967295).
          intro T. apply owner_rel in T. bool_rel; contra. bool_rel; contra.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          extract_if. apply andb_true_iff; split; bool_rel; assumption.
          rewrite Cond0. apply idx_rel in Cond0. rewrite Cond0 in *.
          eexists; split. reflexivity.
          constructor; simpl; srewrite; simpl; try assumption; try reflexivity.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          constructor; simpl.
          Local Transparent get_s2_page_index_spec.
          unfold get_s2_page_index_spec in *; simpl in *.
          intros. pose proof (Hs2rel _ _ Hidx).
          destruct_zmap; simpl. subst; srewrite.
          autounfold in *. rewrite Hget_index in Hidx. inv Hidx.
          split_and. apply H.
          intros. generalize Hcond4. generalize H0.
          repeat match goal with | [H: _ |- _] => clear H end. intros. omega.
          apply H.
          intros. rewrite ZMap.gss. reflexivity.
          split_and. apply H. apply H. apply H.
          intros. assert_gso. intro T. eapply (page_index_unique labd pfn z) in T. contra.
          assumption. assumption. assumption.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          apply Hidx. apply Hget_index. assumption. autounfold.
          apply andb_true_iff; split; bool_rel; assumption.
          rewrite (ZMap.gso _ _ Hneq). apply H. apply H0.
        Qed.

      Lemma set_pfn_count_spec_ref:
        compatsim (crel RData RData) (gensem set_pfn_count_spec) set_pfn_count_spec_low.
      Proof.
        Opaque set_pfn_count_spec.
        compatsim_simpl (@match_RData).
        exploit set_pfn_count_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma get_pfn_map_spec_exists:
        forall habd labd pfn res f
          (Hspec: get_pfn_map_spec pfn habd = Some (VZ64 res))
          (Hrel: relate_RData f habd labd),
          get_pfn_map_spec0 pfn labd = Some (VZ64 res).
      Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec.
        unfold get_pfn_map_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl. unfold Spec.check64_spec.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_gfn z @ (s2page (shared habd)) = 18446744073709551615). apply gfn_rel. reflexivity.
          rewrite H. reflexivity.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.get_s2_page_gfn_spec, Spec.check64_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec. reflexivity.
          extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          exploit idx_rel. apply andb_true_iff; split; bool_rel; assumption.
          intro Hidx. rewrite Hidx in *. srewrite. reflexivity.
      Qed.

      Lemma get_pfn_map_spec_ref:
        compatsim (crel RData RData) (gensem get_pfn_map_spec) get_pfn_map_spec_low.
      Proof.
        Opaque get_pfn_map_spec.
        compatsim_simpl (@match_RData).
        exploit get_pfn_map_spec_exists; eauto 1;
          refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma set_pfn_map_spec_exists:
        forall habd habd' labd pfn gfn f
          (Hspec: set_pfn_map_spec pfn gfn habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_pfn_map_spec0 pfn gfn labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Opaque get_s2_page_index_spec.
        intros. duplicate Hrel. destruct D. destruct id_s2page0.
        unfold_spec Hspec; autounfold in Hspec.
        simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
        unfold set_pfn_map_spec0; autounfold.
        exploit (page_index_succ (z * 4096) labd); try assumption.
        autounfold in *; bool_rel_all. apply andb_true_iff; split; bool_rel; omega.
        intros (idx0 & Hget_index & Hidx0). rewrite Hget_index.
        autounfold in *; srewrite.
        destruct Hidx0 as [Hidx0|Hidx0].
        - rewrite Hidx0. simpl.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_gfn z @ (s2page (shared habd)) = 18446744073709551615). apply gfn_rel. reflexivity.
          assert(s2_owner z @ (s2page (shared habd)) = 4294967295). apply owner_rel. reflexivity.
          bool_rel; contra.
        - bool_rel_all. clear_hyp. simpl.
          extract_if. bool_rel. omega. rewrite Cond.
          destruct_if. bool_rel; omega.
          unfold Spec.set_s2_page_gfn_spec, Spec.check_spec; autounfold.
          repeat simpl_hyp Hspec; inv Hspec.
          eexists; split. reflexivity. assumption.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          assert(s2_owner z @ (s2page (shared habd')) <> 4294967295).
          intro T. apply owner_rel in T. bool_rel; contra. bool_rel; contra.
          destruct (Hs2rel _ _ Hget_index) as (owner_rel & count_rel & gfn_rel & idx_rel).
          extract_if. apply andb_true_iff; split; bool_rel; assumption.
          rewrite Cond0. apply idx_rel in Cond0. rewrite Cond0 in *.
          eexists; split. reflexivity.
          constructor; simpl; srewrite; simpl; try assumption; try reflexivity.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          constructor; simpl.
          Local Transparent get_s2_page_index_spec.
          unfold get_s2_page_index_spec in *; simpl in *.
          intros. pose proof (Hs2rel _ _ Hidx).
          destruct_zmap; simpl. subst; srewrite.
          autounfold in *. rewrite Hget_index in Hidx. inv Hidx.
          split_and. apply H. apply H.
          intros. generalize Hcond4. generalize H0.
          repeat match goal with | [H: _ |- _] => clear H end. intros. omega.
          intros. rewrite ZMap.gss. reflexivity.
          split_and. apply H. apply H. apply H.
          intros. assert_gso. intro T. eapply (page_index_unique labd pfn z) in T. contra.
          assumption. assumption. assumption.
          repeat autounfold. apply andb_true_iff; split; bool_rel; assumption.
          apply Hidx. apply Hget_index. assumption. autounfold.
          apply andb_true_iff; split; bool_rel; assumption.
          rewrite (ZMap.gso _ _ Hneq). apply H. apply H0.
      Qed.

      Lemma set_pfn_map_spec_ref:
        compatsim (crel RData RData) (gensem set_pfn_map_spec) set_pfn_map_spec_low.
      Proof.
        Opaque set_pfn_map_spec.
        compatsim_simpl (@match_RData).
        exploit set_pfn_map_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

  End WITHMEM.

End PageManagerProofHigh.

```
