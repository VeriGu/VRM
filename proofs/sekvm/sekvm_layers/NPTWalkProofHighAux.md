# NPTWalkProofHighAux

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

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Ltac destruct_case H :=
  match type of H with
  | ?a < ?x <= ?b =>
    let H' := fresh "C" in
    let H1 := fresh "T" in
    assert(H': a < x <= b - 1 \/ x = b) by omega; clear H;
    simpl in H'; destruct H' as [H' | H1]; [try omega; destruct_case H'|]
  | ?a <= ?n < ?b =>
    let H' := fresh "C" in
    let H1 := fresh "T" in
    assert (H': n = a \/ a + 1 <= n < b) by omega; clear H;
    simpl in H'; destruct H' as [H' | H1]; destruct_case H'
  end.

Local Hint Unfold
      phys_page
      pmd_page
      stage2_pgd_index
      pgd_index
      pud_index
      pmd_index
      pte_index.

(* page table relation *)

Inductive relate_entry (vmid: Z) (hnpt: NPT) (lnpt: NPT): Z -> Z -> Z -> Z -> Prop :=
| RELATE_ENTRY:
    forall addr pfn level pte
      (Hlevel: level = 0 \/ level = 2 \/ level = 3)
      (Hpte0: level = 0 <-> pte = 0)
      (Hpfn0: level = 0 -> pfn = 0)
      (Hpfn2: level = 2 -> pfn = phys_page pte / PAGE_SIZE +
                                (addr / PAGE_SIZE - addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD))
      (Hpfn3: level = 3 -> pfn = phys_page pte / PAGE_SIZE)
      (Hlevel0: level = 0 ->
                let vttbr_pa := pool_start vmid in
                let pgd_idx := pgd_index addr in
                let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
                let pgd := ZMap.get pgd_p (pt_vttbr_pool lnpt) in
                let pgd_pa := phys_page pgd in
                (pgd = 0 \/
                 (pgd <> 0 /\
                  let pud_idx := pud_index addr in
                  let pud_p := Z.lor pgd_pa (pud_idx * 8) in
                  let pud := ZMap.get pud_p (pt_pgd_pool lnpt) in
                  let pud_pa := phys_page pud in
                  pud = 0 \/
                  (pud <> 0 /\
                   let pmd_idx := pmd_index addr in
                   let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
                   let pmd := ZMap.get pmd_p (pt_pud_pool lnpt) in
                   let pmd_pa := phys_page pmd in
                   pmd = 0 \/ (pmd <> 0 /\ pmd_table pmd = PMD_TYPE_TABLE /\
                              let pte_idx := pte_index addr in
                              let pte_p := Z.lor pmd_pa (pte_idx * 8) in
                              ZMap.get pte_p (pt_pmd_pool lnpt) = pte)))))
      (Hlevel2: level = 2 ->
                let vttbr_pa := pool_start vmid in
                let pgd_idx := pgd_index addr in
                let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
                let pgd := ZMap.get pgd_p (pt_vttbr_pool lnpt) in
                let pgd_pa := phys_page pgd in
                pgd <> 0 /\
                let pud_idx := pud_index addr in
                let pud_p := Z.lor pgd_pa (pud_idx * 8) in
                let pud := ZMap.get pud_p (pt_pgd_pool lnpt) in
                let pud_pa := phys_page pud in
                pud <> 0 /\
                let pmd_idx := pmd_index addr in
                let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
                ZMap.get pmd_p (pt_pud_pool lnpt) = pte /\
                pmd_table pte <> PMD_TYPE_TABLE)
      (Hlevel3: level = 3 ->
                let vttbr_pa := pool_start vmid in
                let pgd_idx := pgd_index addr in
                let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
                let pgd := ZMap.get pgd_p (pt_vttbr_pool lnpt) in
                let pgd_pa := phys_page pgd in
                pgd <> 0 /\
                let pud_idx := pud_index addr in
                let pud_p := Z.lor pgd_pa (pud_idx * 8) in
                let pud := ZMap.get pud_p (pt_pgd_pool lnpt) in
                let pud_pa := phys_page pud in
                pud <> 0 /\
                let pmd_idx := pmd_index addr in
                let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
                let pmd := ZMap.get pmd_p (pt_pud_pool lnpt) in
                pmd <> 0 /\
                pmd_table pmd = PMD_TYPE_TABLE /\
                let pmd_pa := phys_page pmd in
                let pte_idx := pte_index addr in
                let pte_p := Z.lor pmd_pa (pte_idx * 8) in
                ZMap.get pte_p (pt_pmd_pool lnpt) = pte),
      relate_entry vmid hnpt lnpt addr pfn level pte.

Inductive valid_lnpt (vmid: Z) (lnpt: NPT) : Prop :=
| VALID_LNPT
    (Hvmid_valid: valid_vmid vmid)
    (Hvttbr_pool_range: forall p, is_int64 (p @ (pt_vttbr_pool lnpt)) = true)
    (Hpgd_pool_range: forall p, is_int64 (p @ (pt_pgd_pool lnpt)) = true)
    (Hpud_pool_range: forall p, is_int64 (p @ (pt_pud_pool lnpt)) = true)
    (Hpmd_pool_range: forall p, is_int64 (p @ (pt_pmd_pool lnpt)) = true)
    (Hpgd_next_range: pgd_start vmid <= pt_pgd_next lnpt <= pud_start vmid)
    (Hpud_next_range: pud_start vmid <= pt_pud_next lnpt <= pmd_start vmid)
    (Hpmd_next_range: pmd_start vmid <= pt_pmd_next lnpt <= pool_end vmid)
    (Hpgd_next_align: phys_page (pt_pgd_next lnpt) = (pt_pgd_next lnpt))
    (Hpud_next_align: phys_page (pt_pud_next lnpt) = (pt_pud_next lnpt))
    (Hpmd_next_align: phys_page (pt_pmd_next lnpt) = (pt_pmd_next lnpt))
    (Hpgd_next: forall addr, addr >= pt_pgd_next lnpt -> addr @ (pt_pgd_pool lnpt) = 0)
    (Hpud_next: forall addr, addr >= pt_pud_next lnpt -> addr @ (pt_pud_pool lnpt) = 0)
    (Hpmd_next: forall addr, addr >= pt_pmd_next lnpt -> addr @ (pt_pmd_pool lnpt) = 0)
    (Hvttbr_pool: forall addr, addr @ (pt_vttbr_pool lnpt) = 0 \/
                          (pgd_start vmid <= phys_page (addr @ (pt_vttbr_pool lnpt)) < pt_pgd_next lnpt /\
                           (phys_page (addr @ (pt_vttbr_pool lnpt))) @ (pt_pgd_par lnpt) = addr))
    (Hpgd_pool: forall addr, addr @ (pt_pgd_pool lnpt) = 0 \/
                        (pud_start vmid <= phys_page (addr @ (pt_pgd_pool lnpt)) < pt_pud_next lnpt /\
                         (phys_page (addr @ (pt_pgd_pool lnpt))) @ (pt_pud_par lnpt) = addr))
    (Hpud_pool: forall addr, addr @ (pt_pud_pool lnpt) = 0 \/ pmd_table (addr @ (pt_pud_pool lnpt)) <> PMD_TYPE_TABLE \/
                        (pmd_table (addr @ (pt_pud_pool lnpt)) = PMD_TYPE_TABLE /\
                         pmd_start vmid <= phys_page (addr @ (pt_pud_pool lnpt)) < pt_pmd_next lnpt /\
                         (phys_page (addr @ (pt_pud_pool lnpt))) @ (pt_pmd_par lnpt) = addr)):
    valid_lnpt vmid lnpt.

Inductive relate_npt : Z -> NPT -> NPT -> Prop :=
| RELATE_NPT:
    forall vmid hnpt lnpt
      (Hvalid: valid_lnpt vmid lnpt)
      (Hnext_pgd: pt_pgd_next hnpt = pt_pgd_next lnpt)
      (Hnext_pud: pt_pud_next hnpt = pt_pud_next lnpt)
      (Hnext_pmd: pt_pmd_next hnpt = pt_pmd_next lnpt)
      (Hlevel2: forall addr addr'
                  (His_addr: valid_addr addr)
                  (His_addr': valid_addr addr')
                  (Hpgd_same: pgd_index addr = pgd_index addr')
                  (Hpud_same: pud_index addr = pud_index addr')
                  (Hpmd_same: pmd_index addr = pmd_index addr')
                  pfn level pte
                  (Hpte: (addr / PAGE_SIZE) @ (pt hnpt) = (pfn, level, pte))
                  pfn' level' pte'
                  (Hpte': (addr' / PAGE_SIZE) @ (pt hnpt) = (pfn', level', pte')),
          level = 2 -> level' = 2)
      (Hpgd_t: forall addr (ge0: 0 <= addr),
          let pgd_idx := pgd_index addr in
          pgd_idx @ (pgd_t hnpt) = true <->
          let vttbr_p := pool_start vmid in
          let pgd_p := Z.lor vttbr_p (pgd_idx * 8) in
          pgd_p @ (pt_vttbr_pool lnpt) <> 0)
      (Hpud_t: forall addr (ge0: 0 <= addr),
          let pgd_idx := pgd_index addr in
          let pud_idx := pud_index addr in
          pud_idx @ (pgd_idx @ (pud_t hnpt)) = true <->
          let vttbr_p := pool_start vmid in
          let pgd_p := Z.lor vttbr_p (pgd_idx * 8) in
          let pgd := pgd_p @ (pt_vttbr_pool lnpt) in
          pgd <> 0 /\
          let pud_p := Z.lor (phys_page pgd) (pud_idx * 8) in
          let pud := pud_p @ (pt_pgd_pool lnpt) in
          pud <> 0)
      (Hpmd_t: forall addr (ge0: 0 <= addr),
          let pgd_idx := pgd_index addr in
          let pud_idx := pud_index addr in
          let pmd_idx := pmd_index addr in
          pmd_idx @ (pud_idx @ (pgd_idx @ (pmd_t hnpt))) = true <->
          let vttbr_p := pool_start vmid in
          let pgd_p := Z.lor vttbr_p (pgd_idx * 8) in
          let pgd := pgd_p @ (pt_vttbr_pool lnpt) in
          pgd <> 0 /\
          let pud_p := Z.lor (phys_page pgd) (pud_idx * 8) in
          let pud := pud_p @ (pt_pgd_pool lnpt) in
          pud <> 0 /\
          let pmd_p := Z.lor (phys_page pud) (pmd_idx * 8) in
          let pmd := pmd_p @ (pt_pud_pool lnpt) in
          pmd_table pmd = PMD_TYPE_TABLE /\ pmd <> 0)
      (Hrelate: forall addr pfn level pte
                  (Hvalid: valid_addr addr)
                  (Hhpt: ZMap.get (addr / PAGE_SIZE) (pt hnpt) = (pfn, level, pte)),
          relate_entry vmid hnpt lnpt addr pfn level pte),
      relate_npt vmid hnpt lnpt.

(* auxillary lemmas *)

Lemma zne_comm:
  forall (a b: Z), a <> b -> b <> a.
Proof.
  auto.
Qed.

Lemma and_or_same:
  forall n k, Z.land (Z.lor n k) k = k.
Proof.
  intros. Z.bitwise. rewrite andb_orb_distrib_l.
  now destruct (Z.testbit n m) eqn:H1; destruct (Z.testbit k m) eqn:H2.
Qed.

Lemma lor_ne0:
  forall a b, Z.lor a b <> 0 <-> a <> 0 \/ b <> 0.
Proof.
  intros. pose proof (Z.lor_eq_0_iff a b).
  split; apply Decidable.contrapositive;
    unfold Decidable.decidable; tauto.
Qed.

Lemma testbit_false_eq0:
  forall a n, n >= 0 -> a = 0 -> Z.testbit a n = false.
Proof.
  intros. rewrite H0. induction n. easy. easy. contradict H. auto.
Qed.

Lemma testbit_true_ne0:
  forall a , (exists n, n >= 0 /\ Z.testbit a n = true) -> a <> 0.
Proof.
  intro. pose proof (testbit_false_eq0 a).
  apply Decidable.contrapositive. unfold Decidable.decidable. tauto.
  intros. assert (a = 0) by tauto. destruct H1 as (? & ? & ?).
  apply H in H1. contradict H1. rewrite H3. easy. easy.
Qed.

Lemma testbit_ones n i (H : 0 <= n)
  : Z.testbit (Z.ones n) i = ((0 <=? i) && (i <? n))%bool.
Proof.
  destruct (Z.leb_spec 0 i), (Z.ltb_spec i n); simpl;
    rewrite ?Z.testbit_neg_r, ?Z.ones_spec_low, ?Z.ones_spec_high by auto; trivial.
Qed.

Lemma testbit_lnot:
  forall a n, n >= 0 -> Z.testbit a n = negb (Z.testbit (Z.lnot a) n).
Proof.
  intros. induction a; induction n. easy. easy.
  assert (Z.neg p < 0) by easy. contradiction.
  induction p; easy.
  simpl. rewrite -> Pos.add_1_r. rewrite Pos.pred_N_succ. simpl. rewrite negb_involutive. auto.
  assert (Z.neg p < 0) by easy. contradiction.
  simpl. induction p. easy. simpl. induction p; easy.
  easy.
  induction p; simpl; try easy.
  induction p. assert (Z.neg p0 < 0) by easy. contradiction.
  assert (Z.neg p0 < 0) by easy. contradiction.
  assert (Z.neg p0 < 0) by easy. contradiction.
Qed.

Lemma phys_page_land:
  forall a, phys_page a = Z.land a 281474976706560.
Proof.
  intros. unfold phys_page. rewrite <- Z.land_assoc. simpl. reflexivity.
Qed.

Lemma phys_page_testbit_low:
  forall a n, n < 12 -> Z.testbit (phys_page a) n = false.
Proof.
  intros. rewrite phys_page_land. rewrite Z.land_spec.
  apply andb_false_iff. right.
  assert (n < 0 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/
          n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11) by omega.
  destruct H0. induction n; auto with zarith. now assert (Z.pos p > 0).
  repeat (destruct H0; srewrite; auto with zarith).
Qed.

Lemma phys_page_testbit_mid:
  forall a n, 12 <= n < 48 -> Z.testbit (phys_page a) n = Z.testbit a n.
Proof.
  intros. rewrite phys_page_land. rewrite Z.land_spec.
  assert (forall n, 12 <= n < 48 -> Z.testbit 281474976706560 n = true).
  intros. assert (Z.testbit (Z.shiftr 281474976706560 12) (n0-12) = true).
  replace (Z.shiftr 281474976706560 12) with (Z.ones 36) by auto with zarith.
  assert (0 <= n0 - 12 < 36) by omega. rewrite testbit_ones.
  apply andb_true_iff. split; bool_rel; omega. auto with zarith.
  rewrite Z.shiftr_spec in H1. now replace (n0-12+12) with n0 in H1 by auto with zarith.
  omega.
  pose proof (H0 n H). rewrite H1. apply andb_true_r.
Qed.

Lemma phys_page_testbit_high:
  forall a n, 48 <= n -> Z.testbit (phys_page a) n = false.
Proof.
  intros. rewrite phys_page_land. rewrite Z.land_spec.
  assert (Z.testbit 281474976706560 n = false).
  apply Z.bits_above_log2; try omega. assert (Z.log2 281474976706560 = 47) by auto with zarith.
  omega. rewrite H0. apply andb_false_r.
Qed.

Lemma phys_page_upper_bound:
  forall a, phys_page a <= 281474976706560.
Proof.
  intros. rewrite phys_page_land.
  induction a. auto with zarith. apply land_upper_bound_r; auto with zarith.
  apply land_leN_if. assert (Z.neg p < 0). apply Zlt_neg_0. omega.
Qed.

Lemma mod_pow2_0_if:
  forall a n, (forall m, m < n -> Z.testbit a m = false) -> (n >=0) -> a mod 2^n = 0.
Proof.
  intros. apply Z.bits_inj'. intros. assert (0 <= n0 < n \/ n <= n0) as Hn0 by omega.
  destruct Hn0 as [Hn0 | Hn0]. destruct Hn0. rewrite Z.bits_0.
  pose proof (H n0 H3). rewrite <- H4. now apply Z.mod_pow2_bits_low.
  rewrite Z.mod_pow2_bits_high; try omega. now rewrite Z.bits_0.
Qed.

Lemma div_gt_if:
  forall a b c, a mod c = 0 -> b mod c =0 -> c > 0 -> a > b -> a / c > b / c.
Proof.
  intros.
  replace (a) with (c*(a/c)) in H2. replace (b) with (c*(b/c)) in H2.
  apply (Zmult_gt_reg_r (a/c) (b/c) c H1).
  replace (a/c*c) with (c*(a/c)) by auto with zarith.
  replace (b/c*c) with (c*(b/c)) by auto with zarith.
  auto.
  symmetry. apply Z_div_exact_full_2; omega. symmetry. apply Z_div_exact_full_2; omega.
Qed.

Lemma div_le_if:
  forall a b c, a mod c = 0 -> b mod c = 0 -> c > 0 -> a < b -> a / c < b / c.
Proof.
  intros. apply Z.gt_lt. apply Z.lt_gt in H2. apply (div_gt_if b a c H0 H H1 H2).
Qed.

Lemma div_mult_cancel_if:
  forall a b, b > 0 -> a mod b = 0 -> a / b * b = a.
Proof.
  intros. assert (a mod b + a / b * b = a / b * b). rewrite H0. auto.
  rewrite <- H1. pose proof (Zmod_eq a b H). auto with zarith.
Qed.

Lemma Z_div_mult_ge0: forall a b:Z, a >= 0 -> b > 0 -> (a/b)*b >= 0.
Proof.
  intros. assert (a/b>=0) by now apply Z_div_ge0. apply Z.ge_le in H1. apply Z.le_ge.
  now apply Zmult_gt_0_le_0_compat.
Qed.

Lemma Z_div_mult_le: forall a b:Z, a >= 0 -> b > 0 -> (a/b)*b <= a.
Proof.
  intros. pose proof (Zdiv_mult_le a b b). rewrite Z.mul_comm in H1.
  replace (b * a) with (a * b) in H1 by apply Z.mul_comm.
  replace (a * b / b) with (a) in H1. apply H1; auto with zarith.
  symmetry. apply Z_div_mult; auto with zarith.
Qed.

Lemma bits_iff_ge:
  forall a (Ha: 0 < a) b (Hb: b <= a), exists m, (Z.testbit a m = true /\ Z.log2 b <= m).
Proof.
  intros. exists (Z.log2 a). split. now apply Z.bit_log2. now apply Z.log2_le_mono.
Qed.

Lemma testbit_false_neg:
  forall a n (Hn: n < 0), Z.testbit a n = false.
Proof.
  intros. induction n; easy.
Qed.

Lemma Hshiftl3: (Z.shiftl 511 3 = 4088).
Proof.
  auto with zarith.
Qed.

Lemma Htest_f:
  (forall n (Hn: 12 <= n) m (Hm: 0 <= m), Z.testbit (Z.land (Z.shiftl m 3) (Z.shiftl 511 3)) n = false).
Proof.
  intros.
  assert (0 <= Z.shiftl m 3) as Ha_shiftl. rewrite Z.shiftl_nonneg. auto with zarith.
  assert (0 <= 4088) as Htmp by auto with zarith.
  pose proof (land_upper_bound_r (Z.shiftl m 3) 4088 Ha_shiftl Htmp).
  apply Z.log2_le_mono in H. simpl in H.
  apply Z.bits_above_log2. apply Z.land_nonneg. auto with zarith.
  rewrite Hshiftl3. auto with zarith.
Qed.

Lemma simpl_land_mult:
  forall a, Z.land a 511 * 8 = Z.land (Z.shiftl a 3) (Z.shiftl 511 3).
Proof.
  intros. replace 8 with (2^3) by auto with zarith.
  repeat rewrite <- Z.shiftl_mul_pow2 by auto with zarith.
  repeat rewrite Z.shiftl_land. reflexivity.
Qed.

Lemma Hhigh_or:
  forall n (Hn: 12 <= n) m (Hm: 0 <= m) b,
    b || Z.testbit (Z.land (Z.shiftl m 3) (Z.shiftl 511 3)) n = b.
Proof.
  intros. rewrite Htest_f. now rewrite orb_false_r. apply Hn. apply Hm.
Qed.

Lemma land_upper_bound_r':
  forall a b, (0 <= b) -> Z.land a b <= b.
Proof.
  intros. induction a. auto. apply land_upper_bound_r; auto with zarith.
  apply (land_leN_if (Z.neg p) b b). assert (Z.neg p < 0). easy.
  omega.
Qed.

Lemma pgd_index_upperbound:
  forall addr, pgd_index addr <= 511.
Proof.
  intros. unfold pgd_index. now apply land_upper_bound_r'.
Qed.

Lemma pud_index_upperbound:
  forall addr, pud_index addr <= 511.
Proof.
  intros. unfold pud_index. now apply land_upper_bound_r'.
Qed.

Lemma pmd_index_upperbound:
  forall addr, pmd_index addr <= 511.
Proof.
  intros. unfold pmd_index. now apply land_upper_bound_r'.
Qed.

Lemma or3nz:
  forall n, Z.lor n 3 <> 0.
Proof.
  intros. red. intros. induction n. Transparent Z.lor. now simpl in H.
  pose proof (Z.lor_nonneg (Z.pos p) 3). destruct H0.
  assert (0 <= Z.pos p /\ 0 <= 3 ) by auto with zarith.
  now apply H1 in H2.
  pose proof (Z.lor_neg (Z.neg p) 3). destruct H0.
  assert (Z.neg p < 0 \/ 3 < 0). now left.
  now apply H1 in H2.
  Opaque Z.lor.
Qed.

(* page address lemmas *)

Lemma pt_addr_not_zero_or:
  forall addr n, is_pt_addr addr = true -> phys_page (Z.lor addr n) <> 0.
Proof.
  intros. Local Transparent Z.land Z.lor.
  unfold phys_page. unfold is_pt_addr in H. apply andb_true_iff in H.
  destruct H as [Haddr1 Haddr2].
  rewrite <- Z.land_assoc. simpl. rewrite Z.land_lor_distr_l.
  bool_rel.
  assert (addr mod 2 ^ 49 = addr). apply Z.mod_small.
  assert (PT_POOL_START + PT_POOL_SIZE < 2^49). autounfold. simpl.
  unfold Z.pow_pos. simpl. auto with zarith. bool_rel.
  split. autounfold in Haddr1. omega. autounfold in Haddr2, H. omega.
  assert (12 < Z.log2 addr < 48). autounfold in Haddr1. autounfold in Haddr2.
  assert (65536 + 256 * 33554432 = 8590000128) by easy.
  assert (addr <= 8590000128) by omega. pose proof (Z.log2_le_mono addr 8590000128).
  apply H2 in H1.
  assert (Z.log2 8590000128 < 48) by easy.
  pose proof (Z.log2_le_mono 65536 addr). assert (Z.log2 65536 = 16) by easy.
  apply H4 in Haddr1. omega.
  apply lor_ne0. assert (Z.land addr 281474976706560 <> 0).
  assert (Z.testbit (Z.land addr 281474976706560) (Z.log2 addr) = true).
  rewrite Z.land_spec. apply andb_true_iff. split.
  apply Z.bit_log2. autounfold in Haddr1. omega.
  assert (Z.testbit (Z.shiftr 281474976706560 12) ((Z.log2 addr)-12) = true).
  assert (Z.shiftr 281474976706560 12 = (Z.ones 36)) by easy.
  rewrite H1. rewrite testbit_ones. apply andb_true_iff. split; bool_rel; omega. easy.
  rewrite Z.shiftr_spec in H1. assert (Z.log2 addr-12+12 = Z.log2 addr). auto with zarith.
  rewrite H2 in H1. apply H1. omega.
  pose proof (testbit_true_ne0 (Z.land addr 281474976706560)).
  apply H2. eexists. assert (Z.log2 addr >= 0) by omega.
  split. apply H3. apply H1. auto.
  Local Opaque Z.land Z.lor.
Qed.

Lemma phys_page_or_not_change:
  forall addr n (Hn: 0 <= n < 4096), phys_page addr = addr -> phys_page (Z.lor addr n) = addr.
Proof.
  intros. Local Transparent Z.land Z.lor.
  unfold phys_page in *. rewrite <- Z.land_assoc in H. rewrite <- Z.land_assoc.
  simpl in *. rewrite Z.land_lor_distr_l. rewrite H.
  assert (Z.land n 281474976706560 = 0).
  apply Z.bits_inj'. intros. rewrite Z.testbit_0_l.
  rewrite Z.land_spec. apply andb_false_iff.
  assert (0 <= n0 < 12 \/ 12 <= n0) by omega. destruct H1. right.
  assert (-1 < n0 <= 11) by omega. destruct_case H2; srewrite; simpl; reflexivity.
  left. apply Z.bits_above_log2; auto with zarith. assert (n <= 4095) by omega.
  apply Z.log2_le_mono in H2. simpl in H2. omega.
  rewrite H0. apply Z.lor_0_r.
  Local Opaque Z.land Z.lor.
Qed.

Lemma page_and_4096:
  forall n (Hn: 0 <= n), 0 <= (Z.land n 511) * 8 < 4096.
Proof.
  intros. split. pose proof (Z.land_nonneg n 511). omega.
  pose proof (land_upper_bound_r n 511). omega.
Qed.

Lemma phys_page_mod_4096:
  forall a, phys_page a mod 4096 = 0.
Proof.
  intros. replace 4096 with (2^12) by auto with zarith.
  pose proof (phys_page_testbit_low a).
  apply (mod_pow2_0_if (phys_page a) 12 H). auto with zarith.
Qed.

Lemma phys_page_lt_4096:
  forall n m (Hpn: phys_page n = n) (Hpm: phys_page m = m), n < m -> n + 4096 <= m.
Proof.
  intros. assert ((n + 4096) / 4096 = n / 4096 + 1).
  replace (n + 4096) with (n + 1 * 4096) by auto.
  now rewrite Z_div_plus_full by auto with zarith.
  assert (n mod 4096 = 0) as Hnmod. rewrite <- Hpn. apply phys_page_mod_4096.
  assert (m mod 4096 = 0) as Hmmod. rewrite <- Hpm. apply phys_page_mod_4096.
  assert (n / 4096 < m / 4096). apply div_le_if; omega.
  assert (n/4096 + 1 <= m / 4096). omega. rewrite <- H0 in H2.
  assert (4096 * ((n + 4096) / 4096) <= 4096 * (m / 4096)). auto with zarith.
  replace (4096  * ((n + 4096) / 4096)) with (n + 4096) in H3.
  replace (4096 * (m / 4096)) with m in H3. apply H3.
  apply Z_div_exact_2; auto with zarith.
  assert ((n + 4096) mod 4096 = 0).
  replace (n + 4096) with (n + 1 * 4096) by auto.
  rewrite Z_mod_plus; auto with zarith.
  apply Z_div_exact_2; auto with zarith.
Qed.

Lemma phys_page_fixed:
  forall addr, phys_page (phys_page addr) = phys_page addr.
Proof.
  intros. unfold phys_page.
  rewrite <- Z.land_assoc. simpl. rewrite <- Z.land_assoc. simpl.
  rewrite <- Z.land_assoc. simpl. rewrite <- Z.land_assoc. simpl.
  reflexivity.
Qed.

Hypothesis or_index_range:
  forall addr n (Haddr: 0 <= addr) (align: phys_page addr = addr) (Hn: 0 <= n),
    addr <= Z.lor addr ((Z.land n 511) * 8) < addr + 4096.

Lemma phys_page_a_page:
  forall addr, (phys_page addr = addr) -> addr < 281474976706560 ->
          phys_page (addr + 4096) = addr + 4096.
Proof.
  intros.
  assert (addr + 4096 = ((addr / 4096 + 1) * 2^12)).
  replace (2^12) with 4096 by auto with zarith. auto with zarith.
  assert ((addr + 4096) / 4096 = addr / 4096 + 1).
  replace (addr + 4096) with (addr + 1 * 4096) by auto.
  now rewrite Z_div_plus_full by auto with zarith.
  rewrite <- H1. symmetry. apply div_mult_cancel_if. auto with zarith.
  rewrite Zplus_mod. replace (4096 mod 4096) with 0 by auto with zarith.
  pose proof (phys_page_mod_4096 addr). rewrite H in H2.
  now rewrite H2.
  apply Z.bits_inj'. intros. assert (0 <= n < 12 \/ 12 <= n < 48 \/ 48 <= n) by omega.
  destruct H3.
  rewrite phys_page_testbit_low; try omega.
  rewrite H1. symmetry. apply Z.mul_pow2_bits_low. omega.
  destruct H3.
  rewrite phys_page_testbit_mid; try omega. reflexivity.
  pose proof (phys_page_upper_bound addr). rewrite H in H4.
  assert (0 < addr + 4096 <= 281474976710655).
  assert (0 <= addr). rewrite <- H. unfold phys_page. unfold PAGE_MASK.
  apply Z.land_nonneg. right. omega. omega.
  rewrite phys_page_testbit_high. symmetry.
  apply Z.bits_above_log2. omega. destruct H5.
  apply Z.log2_le_mono in H6.
  replace (Z.log2 281474976710655) with 47 in H6 by auto with zarith.
  omega. omega.
Qed.

Lemma div_mul_pmd_addr:
  forall addr, valid_addr addr ->
          valid_addr (addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD * PAGE_SIZE).
Proof.
  intros. unfold valid_addr in *.
  assert (addr / PAGE_SIZE / PTRS_PER_PMD = addr / (PAGE_SIZE * PTRS_PER_PMD)) as Hdivmult.
  rewrite Zdiv_Zdiv. reflexivity. now unfold PAGE_SIZE. now unfold PTRS_PER_PMD.
  rewrite Hdivmult.
  assert (addr / (PAGE_SIZE * PTRS_PER_PMD) * PTRS_PER_PMD * PAGE_SIZE =
          addr / (PAGE_SIZE * PTRS_PER_PMD) * (PTRS_PER_PMD * PAGE_SIZE)) as Hmultassoc.
  auto with zarith.
  rewrite Hmultassoc.
  assert (addr / (PAGE_SIZE * PTRS_PER_PMD) * (PTRS_PER_PMD * PAGE_SIZE) <= addr) as Hle.
  assert (addr >= 0) by omega.
  now apply Z_div_mult_le.
  split. assert (addr / (PAGE_SIZE * PTRS_PER_PMD) >= 0) as Hge0. apply Z_div_ge0. easy. omega.
  apply Z.ge_le in Hge0.
  apply Zmult_gt_0_le_0_compat. easy. apply Hge0.
  omega.
Qed.

Lemma div_mul_page_addr:
  forall addr, valid_addr addr ->
          valid_addr (addr / PAGE_SIZE * PAGE_SIZE).
Proof.
  intros. unfold valid_addr in *. assert (addr >= 0) by omega.
  assert (addr / PAGE_SIZE * PAGE_SIZE <= addr) as Hle by now apply Z_div_mult_le.
  split. apply Z.ge_le. apply Z_div_mult_ge0. omega. easy. omega.
Qed.

Lemma pgd_pud_pmd_shift_eq:
  forall addr addr'
    (Hvalid: valid_addr addr)
    (Hvalid': valid_addr addr'),
    pgd_index addr = pgd_index addr' /\
    pud_index addr = pud_index addr' /\
    pmd_index addr = pmd_index addr' ->
    (Z.shiftr addr 39 = Z.shiftr addr' 39 /\
     Z.shiftr addr 30 = Z.shiftr addr' 30 /\
     Z.shiftr addr 21 = Z.shiftr addr' 21).
Proof.
  intros.
  unfold valid_addr in Hvalid, Hvalid'.
  assert (511 = Z.ones 9) as Hones by auto with zarith.
  unfold pgd_index, pud_index, pmd_index in H.
  destruct H as [Hpgd_idx [Hpud_idx Hpmd_idx]].
  rewrite Hones in *.
  repeat (rewrite Z.land_ones in Hpgd_idx, Hpud_idx, Hpmd_idx; try easy).
  unfold PGDIR_SHIFT in Hpgd_idx.
  unfold PUD_SHIFT in Hpud_idx.
  unfold PMD_SHIFT in Hpmd_idx.
  repeat (rewrite Z.shiftr_div_pow2 in Hpgd_idx, Hpud_idx, Hpmd_idx; try easy).
  (* Z.shiftr addr 39 = Z.shiftr addr' 39 *)
  assert (Z.shiftr addr 39 = Z.shiftr addr' 39) as Hpgd.
  assert (addr / 2 ^ 39 <= (KVM_ADDR_SPACE-1)/ 2 ^ 39) as Hdivle. apply Z_div_le. easy. omega.
  assert (addr' / 2 ^ 39 <= (KVM_ADDR_SPACE-1)/ 2 ^ 39) as Hdivle'. apply Z_div_le. easy. omega.
  assert ((KVM_ADDR_SPACE -1)/ 2 ^ 39 = 511) as Hkas by auto. rewrite Hkas in Hdivle.
  assert (addr / 2 ^ 39 < 512) as Hle_512 by omega.
  assert (addr' / 2 ^ 39 < 512) as Hle_512' by omega.
  assert (0 < 2 ^ 39). apply Z.pow_pos_nonneg; auto with zarith.
  destruct Hvalid as [Hvalid0 Hvalid1].
  assert ((addr/ 2 ^ 39) mod 2 ^ 9 = addr / 2 ^ 39) as Hdiv_mod. apply Z.mod_small.
  split. apply Z.ge_le. apply Z_div_ge0; auto with zarith. auto with zarith.
  assert ((addr'/ 2 ^ 39) mod 2 ^ 9 = addr' / 2 ^ 39) as Hdiv_mod'. apply Z.mod_small.
  split. apply Z.ge_le. apply Z_div_ge0; auto with zarith. auto with zarith.
  repeat (rewrite Z.shiftr_div_pow2; auto with zarith).
  (* Z.shiftr addr 30 = Z.shiftr addr' 30 *)
  assert (Z.shiftr addr 30 = Z.shiftr addr' 30) as Hpud.
  assert (forall n0, n0<9 -> Z.testbit (addr / 2 ^ 30)  n0 = Z.testbit (addr' / 2 ^ 30)  n0).
  intros.
  apply Z.bits_inj_iff in Hpud_idx. unfold Z.eqf in Hpud_idx.
  pose proof (Hpud_idx n0) as Hpud_idx'.
  rewrite Z.mod_pow2_bits_low in Hpud_idx'. rewrite Z.mod_pow2_bits_low in Hpud_idx'.
  apply Hpud_idx'. auto. auto.
  repeat (rewrite <- Z.shiftr_div_pow2 in H; try easy).
  apply Z.bits_inj_iff in Hpgd. unfold Z.eqf in Hpgd.
  assert (forall n0, 0<=n0->Z.testbit (Z.shiftr addr 30) n0 = Z.testbit (Z.shiftr addr' 30) n0).
  intros. assert (n0 < 9 \/ n0 >= 9) as Hn0. omega. destruct Hn0 as [Hn0 | Hn0'].
  apply H in Hn0. apply Hn0.
  pose proof (Hpgd (n0-9)) as Hpgdn0.
  repeat rewrite Z.shiftr_spec; try omega.
  repeat (rewrite Z.shiftr_spec in Hpgdn0; try omega).
  replace (n0-9+39) with (n0+30) in Hpgdn0; try auto with zarith.
  apply Z.bits_inj'. apply H0.
  (* Z.shiftr addr 21 = Z.shiftr addr' 21 *)
  assert (Z.shiftr addr 21 = Z.shiftr addr' 21) as Hpmd.
  assert (forall n0, n0<9 -> Z.testbit (addr / 2 ^ 21)  n0 = Z.testbit (addr' / 2 ^ 21)  n0).
  intros.
  apply Z.bits_inj_iff in Hpmd_idx. unfold Z.eqf in Hpmd_idx.
  pose proof (Hpmd_idx n0) as Hpmd_idx'.
  rewrite Z.mod_pow2_bits_low in Hpmd_idx'. rewrite Z.mod_pow2_bits_low in Hpmd_idx'.
  apply Hpmd_idx'. auto. auto.
  repeat (rewrite <- Z.shiftr_div_pow2 in H; try easy).
  apply Z.bits_inj_iff in Hpgd. unfold Z.eqf in Hpgd.
  apply Z.bits_inj_iff in Hpud. unfold Z.eqf in Hpud.
  assert (forall n0, 0<=n0->Z.testbit (Z.shiftr addr 21) n0 = Z.testbit (Z.shiftr addr' 21) n0).
  intros. assert (n0 < 9 \/ n0 >= 9) as Hn0. omega. destruct Hn0 as [Hn0 | Hn0'].
  apply H in Hn0. apply Hn0.
  pose proof (Hpud (n0-9)) as Hpudn0.
  repeat rewrite Z.shiftr_spec; try omega.
  repeat (rewrite Z.shiftr_spec in Hpudn0; try omega).
  replace (n0-9+30) with (n0+21) in Hpudn0; try auto with zarith.
  apply Z.bits_inj'. apply H0. auto.
Qed.

Lemma pte_shift_eq:
  forall addr addr'
    (Hvalid: valid_addr addr)
    (Hvalid': valid_addr addr'),
    pgd_index addr = pgd_index addr' /\ pud_index addr = pud_index addr' /\
    pmd_index addr = pmd_index addr' /\ pte_index addr = pte_index addr' ->
    Z.shiftr addr 12 = Z.shiftr addr' 12.
Proof.
  intros. destruct H as [Hpgd_idx [Hpud_idx [Hpmd_idx Hpte_idx]]].
  pose proof (pgd_pud_pmd_shift_eq addr addr' Hvalid Hvalid') as Hshift_eq'.
  exploit Hshift_eq'. auto. intros Hshift_eq.
  destruct Hshift_eq as [Hpgd [Hpud Hpmd]].
  unfold valid_addr in Hvalid, Hvalid'.
  assert (511 = Z.ones 9) as Hones by auto with zarith.
  unfold pgd_index, pud_index, pmd_index, pte_index in *.
  rewrite Hones in *.
  repeat (rewrite Z.land_ones in Hpgd_idx, Hpud_idx, Hpmd_idx, Hpte_idx; try easy).
  unfold PGDIR_SHIFT in Hpgd_idx. unfold PUD_SHIFT in Hpud_idx.
  unfold PMD_SHIFT in Hpmd_idx. unfold PAGE_SHIFT in Hpte_idx.
  repeat (rewrite Z.shiftr_div_pow2 in Hpgd_idx, Hpud_idx, Hpmd_idx, Hpte_idx; try easy).
  assert (forall n0, n0<9 -> Z.testbit (addr / 2 ^ 12)  n0 = Z.testbit (addr' / 2 ^ 12)  n0).
  intros.
  apply Z.bits_inj_iff in Hpte_idx. unfold Z.eqf in Hpte_idx.
  pose proof (Hpte_idx n0) as Hpte_idx'.
  rewrite Z.mod_pow2_bits_low in Hpte_idx'. rewrite Z.mod_pow2_bits_low in Hpte_idx'.
  apply Hpte_idx'. auto. auto.
  repeat (rewrite <- Z.shiftr_div_pow2 in H; try easy).
  apply Z.bits_inj_iff in Hpgd. unfold Z.eqf in Hpgd.
  apply Z.bits_inj_iff in Hpud. unfold Z.eqf in Hpud.
  apply Z.bits_inj_iff in Hpmd. unfold Z.eqf in Hpmd.
  assert (forall n0, 0<=n0->Z.testbit (Z.shiftr addr 12) n0 = Z.testbit (Z.shiftr addr' 12) n0).
  intros. assert (n0 < 9 \/ n0 >= 9) as Hn0. omega. destruct Hn0 as [Hn0 | Hn0'].
  apply H in Hn0. apply Hn0.
  pose proof (Hpmd (n0-9)) as Hpmdn0.
  repeat rewrite Z.shiftr_spec; try omega.
  repeat (rewrite Z.shiftr_spec in Hpmdn0; try omega).
  replace (n0-9+21) with (n0+12) in Hpmdn0; try auto with zarith.
  apply Z.bits_inj'. apply H0.
Qed.

Lemma pmd_same_cond:
  forall addr addr'
    (Hvalid: valid_addr addr)
    (Hvalid': valid_addr addr'),
    pgd_index addr = pgd_index addr' /\ pud_index addr = pud_index addr' /\
    pmd_index addr = pmd_index addr' <->
    addr / PAGE_SIZE / PTRS_PER_PMD = addr' / PAGE_SIZE / PTRS_PER_PMD.
Proof.
  intros.
  assert (PAGE_SIZE = 2 ^ 12) as Hpgsz by auto with zarith.
  assert (PTRS_PER_PMD = 2 ^ 9) as Hppm by auto with zarith.
  assert (511 = Z.ones 9) as Hones by auto with zarith.
  rewrite Hpgsz. rewrite Hppm.
  split; intros.
  (* -> *)
  pose proof (pgd_pud_pmd_shift_eq addr addr' Hvalid Hvalid' H) as Hshift_eq.
  destruct H as [Hpgd_idx [Hpud_idx Hpmd_idx]].
  unfold valid_addr in Hvalid, Hvalid'.
  unfold pgd_index, pud_index, pmd_index in *.
  repeat rewrite <- Z.shiftr_div_pow2; try easy.
  (* <- *)
  unfold valid_addr in Hvalid, Hvalid'.
  repeat (rewrite <- Z.shiftr_div_pow2 in H; try easy).
  repeat (rewrite Z.shiftr_shiftr in H; try easy).
  replace (12+9) with (21) in H by easy. autounfold.
  rewrite Hones. repeat rewrite Z.land_ones; try easy.
  apply Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall n0, n0>=21->Z.shiftr addr n0 = Z.shiftr addr' n0) as Haddrn0.
  intros. apply Z.bits_inj'. intros.
  pose proof (Z.shiftr_spec (Z.shiftr addr 21) (n0-21) n H1) as Hadd.
  rewrite Z.shiftr_shiftr in Hadd; auto with zarith.
  replace (21+(n0-21)) with n0 in Hadd; auto with zarith.
  rewrite Hadd.
  pose proof (Z.shiftr_spec (Z.shiftr addr' 21) (n0-21) n H1) as Hadd'.
  rewrite Z.shiftr_shiftr in Hadd'; auto with zarith.
  replace (21+(n0-21)) with n0 in Hadd'; auto with zarith.
  rewrite Hadd'. apply H.
  repeat split.
  assert (Z.shiftr addr 39 = Z.shiftr addr' 39). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
  assert (Z.shiftr addr 30 = Z.shiftr addr' 30). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
  assert (Z.shiftr addr 21 = Z.shiftr addr' 21). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
Qed.

Lemma pte_same_cond:
  forall addr addr'
    (Hvalid: valid_addr addr)
    (Hvalid': valid_addr addr'),
    pgd_index addr = pgd_index addr' /\ pud_index addr = pud_index addr' /\
    pmd_index addr = pmd_index addr' /\ pte_index addr = pte_index addr' <->
    addr / PAGE_SIZE = addr' / PAGE_SIZE.
Proof.
  intros.
  assert (PAGE_SIZE = 2 ^ 12) as Hpgsz by auto with zarith.
  assert (511 = Z.ones 9) as Hones by auto with zarith.
  rewrite Hpgsz.
  split; intros.
  (* -> *)
  destruct H as [Hpgd_idx [Hpud_idx [Hpmd_idx Hpte_idx]]].
  pose proof (pgd_pud_pmd_shift_eq addr addr' Hvalid Hvalid') as Hshift_eq'.
  pose proof (pte_shift_eq addr addr' Hvalid Hvalid') as Hpte_shift_eq'.
  exploit Hshift_eq'. auto. intros Hshift_eq.
  exploit Hpte_shift_eq'. auto. intros Hpte_shift_eq.
  unfold valid_addr in Hvalid, Hvalid'.
  unfold pgd_index, pud_index, pmd_index in *.
  repeat rewrite <- Z.shiftr_div_pow2; try easy.
  (* <- *)
  unfold valid_addr in Hvalid, Hvalid'.
  repeat (rewrite <- Z.shiftr_div_pow2 in H; try easy).
  repeat (rewrite Z.shiftr_shiftr in H; try easy).
  autounfold.
  rewrite Hones. repeat rewrite Z.land_ones; try easy.
  apply Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall n0, n0>=12->Z.shiftr addr n0 = Z.shiftr addr' n0) as Haddrn0.
  intros. apply Z.bits_inj'. intros.
  pose proof (Z.shiftr_spec (Z.shiftr addr 12) (n0-12) n H1) as Hadd.
  rewrite Z.shiftr_shiftr in Hadd; auto with zarith.
  replace (12+(n0-12)) with n0 in Hadd; auto with zarith.
  rewrite Hadd.
  pose proof (Z.shiftr_spec (Z.shiftr addr' 12) (n0-12) n H1) as Hadd'.
  rewrite Z.shiftr_shiftr in Hadd'; auto with zarith.
  replace (12+(n0-12)) with n0 in Hadd'; auto with zarith.
  rewrite Hadd'. apply H.
  repeat split.
  assert (Z.shiftr addr 39 = Z.shiftr addr' 39). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
  assert (Z.shiftr addr 30 = Z.shiftr addr' 30). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
  assert (Z.shiftr addr 21 = Z.shiftr addr' 21). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
  assert (Z.shiftr addr 12 = Z.shiftr addr' 12). apply Haddrn0; auto with zarith.
  rewrite H0. reflexivity.
Qed.

Lemma or_index_ne_cond:
  forall n m a b (align_n: phys_page n = n) (align_m: phys_page m = m)
    (diff: n <> m \/ (Z.land a 511) <> Z.land b 511),
    Z.lor n ((Z.land a 511) * 8) <> Z.lor m ((Z.land b 511) * 8).
Proof.
  intros. autounfold. intros.
  rewrite <- Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall a n, n >= 12 -> Z.testbit (Z.land a 511 * 8) n = false) as Habove_false.
  intros.
  apply (Z.bits_above_log2 (Z.land a0 511  * 8) n0).
  assert (0 <= Z.land a0 511). apply Z.land_nonneg. omega. omega.
  assert ((Z.land a0 511) * 8 <= 4095). assert (0 <= 4095) as Hle by easy.
  pose proof (land_upper_bound_r' a0 511 Hle). omega.
  apply Z.log2_le_mono in H1. simpl in H1. omega.
  assert (forall n0, 0 <= n0 -> Z.testbit m n0 = Z.testbit n n0 /\
                         Z.testbit (Z.land a 511 * 8) n0 =
                         Z.testbit (Z.land b 511 * 8) n0).
  intros.
  pose proof (H n0) as Hfinal. repeat rewrite Z.lor_spec in Hfinal.
  assert (0 <= n0 < 12 \/ n0 >= 12) as Hn0 by omega. destruct Hn0 as [Hn0 | Hn0].
  destruct Hn0 as [_ Hn0].
  pose proof (phys_page_testbit_low m n0 Hn0) as Hm_false. rewrite align_m in Hm_false.
  pose proof (phys_page_testbit_low n n0 Hn0) as Hn_false. rewrite align_n in Hn_false.
  rewrite Hm_false, Hn_false in *. repeat rewrite orb_false_l in Hfinal. auto.
  pose proof (Habove_false a n0 Hn0) as Ha_false.
  pose proof (Habove_false b n0 Hn0) as Hb_false.
  rewrite Ha_false, Hb_false in Hfinal. repeat rewrite orb_false_r in Hfinal.
  rewrite Ha_false, Hb_false. auto.
  assert (n = m /\ Z.land a 511 * 8 = Z.land b 511 * 8) as Hfinal'.
  split; apply Z.bits_inj'; intros; pose proof (H0 n0 H1); easy.
  destruct Hfinal' as [Hfinal1 Hfinal2].
  assert (Z.land a 511 = Z.land b 511) by auto with zarith.
  destruct diff; auto.
Qed.

Lemma pgd_pool_next_zero:
  forall n vmid lnpt (Hvalid: valid_lnpt vmid lnpt) (Hvmid: 0 <= vmid) (Hn: 0 <= n),
    ((Z.lor (pt_pgd_next lnpt) (Z.land n 511 * 8)) @ (pt_pgd_pool lnpt)) = 0.
Proof.
  intros. destruct Hvalid.
  pose proof (Hpgd_next ((Z.lor (pt_pgd_next lnpt) (Z.land n 511 * 8)))).
  pose proof (lor_lower_bound_l (pt_pgd_next lnpt) (Z.land n 511 * 8)).
  apply H in H0. rewrite H0. unfold phys_page. auto.
  autounfold in Hpgd_next_range. omega.
  pose proof (Z.land_nonneg n 511) as Hnonneg.
  assert (0 <= n \/ 0 <= 511) as Htrue by omega. apply Hnonneg in Htrue. auto with zarith.
Qed.

Lemma pud_pool_next_zero:
  forall n vmid lnpt (Hvalid: valid_lnpt vmid lnpt) (Hvmid: 0 <= vmid) (Hn: 0 <= n),
    ((Z.lor (pt_pud_next lnpt) (Z.land n 511 * 8)) @ (pt_pud_pool lnpt)) = 0.
Proof.
  intros. destruct Hvalid.
  pose proof (Hpud_next ((Z.lor (pt_pud_next lnpt) (Z.land n 511 * 8)))).
  pose proof (lor_lower_bound_l (pt_pud_next lnpt) (Z.land n 511 * 8)).
  apply H in H0. rewrite H0. unfold phys_page. auto.
  autounfold in Hpud_next_range. omega.
  pose proof (Z.land_nonneg n 511) as Hnonneg.
  assert (0 <= n \/ 0 <= 511) as Htrue by omega. apply Hnonneg in Htrue. auto with zarith.
Qed.

Lemma pmd_pool_next_zero:
  forall n vmid lnpt (Hvalid: valid_lnpt vmid lnpt) (Hvmid: 0 <= vmid) (Hn: 0 <= n),
    ((Z.lor (pt_pmd_next lnpt) (Z.land n 511 * 8)) @ (pt_pmd_pool lnpt)) = 0.
Proof.
  intros. destruct Hvalid.
  pose proof (Hpmd_next ((Z.lor (pt_pmd_next lnpt) (Z.land n 511 * 8)))).
  pose proof (lor_lower_bound_l (pt_pmd_next lnpt) (Z.land n 511 * 8)).
  apply H in H0. rewrite H0. unfold phys_page. auto.
  autounfold in Hpmd_next_range. omega.
  pose proof (Z.land_nonneg n 511) as Hnonneg.
  assert (0 <= n \/ 0 <= 511) as Htrue by omega. apply Hnonneg in Htrue. auto with zarith.
Qed.

Lemma vttbr_pool_ne_pgd_next:
  forall addr a b vmid lnpt (Hvalid: valid_lnpt vmid lnpt) (Ha: 0 <= a) (Hb: 0 <= b) (Hvmid: 0 <= vmid),
    Z.lor (phys_page (addr @ (pt_vttbr_pool lnpt))) (Z.land a 511 * 8) <>
    Z.lor (pt_pgd_next lnpt) (Z.land b 511 * 8).
Proof.
  intros.
  destruct Hvalid. autounfold in Hpgd_next_range.
  pose proof (Hvttbr_pool addr) as Hvttbr_pool'.
  repeat rewrite simpl_land_mult.
  destruct Hvttbr_pool' as [Hvttbr_pool' | Hvttbr_pool'].
  rewrite Hvttbr_pool'. simpl. autounfold in Hpgd_next_range. autounfold.
  intros.
  rewrite <- Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall n, ~(Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                 Z.testbit (Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n)) as Hall_not_not.
  intros. autounfold. intros Hcond. apply Hcond. trivial.
  apply Logic.Classical_Pred_Type.all_not_not_ex in Hall_not_not.
  assert (exists n, Z.testbit (Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n = true /\
               16 <= n) as Hex.
  assert (Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) >= 69632) as Hlor_lower.
  assert (69632 <= pt_pgd_next lnpt) as Ha_lower by auto with zarith.
  assert (0 <= pt_pgd_next lnpt) as Ha_lower' by auto with zarith.
  assert (0 < pt_pgd_next lnpt) as Ha_lower'' by auto with zarith.
  assert (0 <= Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) as Hland_nonneg.
  apply Z.land_nonneg. rewrite Hshiftl3. auto with zarith.
  pose proof (lor_lower_bound_l (pt_pgd_next lnpt)
                                (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) Ha_lower' Hland_nonneg) as Hlor_lower.
  auto with zarith. apply Z.ge_le in Hlor_lower.
  assert (0 < Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) as Hlor_lower'.
  auto with zarith.
  pose proof (bits_iff_ge (Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) Hlor_lower'
                          69632 Hlor_lower).
  destruct H0. exists x. simpl in H0. apply H0.
  assert (exists n , Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                Z.testbit (Z.lor (pt_pgd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n) as Hcontra.
  destruct Hex as (x & Heex). destruct Heex as [Htest_t Hx]. assert (12 <= x) as Hx' by omega.
  pose proof (Htest_f x Hx') as Htest_f'.
  exists x. rewrite Htest_f'. rewrite Htest_t. easy. auto.
  contradict Hcontra. auto.

  destruct Hvttbr_pool' as [Hvttbr_pool' Hvttbr_pool''].
  autounfold. rewrite <- Z.bits_inj_iff. unfold Z.eqf. intros Hfalse.
  assert (forall n, (Z.testbit (phys_page addr @ (pt_vttbr_pool lnpt)) n) ||
               (Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n) =
               (Z.testbit (pt_pgd_next lnpt) n) || (Z.testbit (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) n))
    as Hfalse_spec.
  intros. repeat rewrite <- Z.lor_spec. apply Hfalse.

  assert (forall n, Z.testbit (phys_page addr @ (pt_vttbr_pool lnpt)) n =
               Z.testbit (pt_pgd_next lnpt) n) as Hhigh_or'.
  intros. assert (n < 12 \/ 12 <= n) as Hn by omega. destruct Hn as [Hn | Hn].
  rewrite <- Hpgd_next_align. unfold phys_page. unfold PHYS_MASK, PAGE_MASK.
  repeat rewrite <- Z.land_assoc. simpl. repeat rewrite Z.land_spec.
  assert (n < 0 \/ 0 <= n < 12) as Hn' by omega. destruct Hn' as [Hn' | Hn'].
  pose proof (testbit_false_neg 281474976710655 n Hn') as Htest_n. rewrite Htest_n.
  now repeat rewrite andb_false_r.
  assert (-1 < n <= 11) as Hn'' by omega.
  destruct_case Hn''; rewrite T; simpl; now repeat rewrite andb_false_r.
  pose proof (Hhigh_or n Hn a Ha (Z.testbit (phys_page addr @ (pt_vttbr_pool lnpt)) n)) as Hhigh_or'0.
  pose proof (Hhigh_or n Hn b Hb (Z.testbit (pt_pgd_next lnpt) n)) as Hhigh_or'1.
  pose proof (Hfalse_spec n) as Hfalse_spec'. rewrite Hhigh_or'0, Hhigh_or'1 in Hfalse_spec'. auto.
  assert (phys_page addr @ (pt_vttbr_pool lnpt)  = pt_pgd_next lnpt) as Hfalse_eq.
  apply Z.bits_inj'. auto. omega.
Qed.

Lemma pgd_pool_ne_pud_next:
  forall addr a b vmid lnpt (Hvalid: valid_lnpt vmid lnpt)  (Ha: 0 <= a) (Hb: 0 <= b) (Hvmid: 0 <= vmid),
    Z.lor (phys_page (addr @ (pt_pgd_pool lnpt))) (Z.land a 511 * 8) <>
    Z.lor (pt_pud_next lnpt) (Z.land b 511 * 8).
Proof.
  intros. Transparent Z.add. destruct Hvalid. autounfold in Hpud_next_range.
  pose proof (Hpgd_pool addr) as Hpgd_pool'.
  repeat rewrite simpl_land_mult.
  destruct Hpgd_pool' as [Hpgd_pool' | Hpgd_pool'].
  rewrite Hpgd_pool'. simpl. autounfold in Hpud_next_range. autounfold.
  intros.
  rewrite <- Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall n, ~(Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                 Z.testbit (Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n)) as Hall_not_not.
  intros. autounfold. intros Hcond. apply Hcond. trivial.
  apply Logic.Classical_Pred_Type.all_not_not_ex in Hall_not_not.
  assert (exists n, Z.testbit (Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n = true /\
               16 <= n) as Hex.
  assert (Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) >= 69632) as Hlor_lower.
  assert (69632 <= pt_pud_next lnpt) as Ha_lower by auto with zarith.
  assert (0 <= pt_pud_next lnpt) as Ha_lower' by auto with zarith.
  assert (0 < pt_pud_next lnpt) as Ha_lower'' by auto with zarith.
  assert (0 <= Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) as Hland_nonneg.
  apply Z.land_nonneg. rewrite Hshiftl3. auto with zarith.
  pose proof (lor_lower_bound_l (pt_pud_next lnpt)
                                (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) Ha_lower' Hland_nonneg) as Hlor_lower.
  auto with zarith. apply Z.ge_le in Hlor_lower.
  assert (0 < Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) as Hlor_lower'.
  auto with zarith.
  pose proof (bits_iff_ge (Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) Hlor_lower'
                          69632 Hlor_lower).
  destruct H0. exists x. simpl in H0. apply H0.
  assert (exists n , Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                Z.testbit (Z.lor (pt_pud_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n) as Hcontra.
  destruct Hex as (x & Heex). destruct Heex as [Htest_t Hx]. assert (12 <= x) as Hx' by omega.
  pose proof (Htest_f x Hx') as Htest_f'.
  exists x. rewrite Htest_f'. rewrite Htest_t. easy. auto.
  contradict Hcontra. auto.

  destruct Hpgd_pool' as [Hpgd_pool' Hpgd_pool''].
  autounfold. rewrite <- Z.bits_inj_iff. unfold Z.eqf. intros Hfalse.
  assert (forall n, (Z.testbit (phys_page addr @ (pt_pgd_pool lnpt)) n) ||
               (Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n) =
               (Z.testbit (pt_pud_next lnpt) n) || (Z.testbit (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) n))
    as Hfalse_spec.
  intros. repeat rewrite <- Z.lor_spec. apply Hfalse.

  assert (forall n, Z.testbit (phys_page addr @ (pt_pgd_pool lnpt)) n =
               Z.testbit (pt_pud_next lnpt) n) as Hhigh_or'.
  intros. assert (n < 12 \/ 12 <= n) as Hn by omega. destruct Hn as [Hn | Hn].
  rewrite <- Hpud_next_align. unfold phys_page. unfold PHYS_MASK, PAGE_MASK.
  repeat rewrite <- Z.land_assoc. simpl. repeat rewrite Z.land_spec.
  assert (n < 0 \/ 0 <= n < 12) as Hn' by omega. destruct Hn' as [Hn' | Hn'].
  pose proof (testbit_false_neg 281474976710655 n Hn') as Htest_n. rewrite Htest_n.
  now repeat rewrite andb_false_r.
  assert (-1 < n <= 11) as Hn'' by omega.
  destruct_case Hn''; rewrite T; simpl; now repeat rewrite andb_false_r.
  pose proof (Hhigh_or n Hn a Ha (Z.testbit (phys_page addr @ (pt_pgd_pool lnpt)) n)) as Hhigh_or'0.
  pose proof (Hhigh_or n Hn b Hb (Z.testbit (pt_pud_next lnpt) n)) as Hhigh_or'1.
  pose proof (Hfalse_spec n) as Hfalse_spec'. rewrite Hhigh_or'0, Hhigh_or'1 in Hfalse_spec'. auto.
  assert (phys_page addr @ (pt_pgd_pool lnpt)  = pt_pud_next lnpt) as Hfalse_eq.
  apply Z.bits_inj'. auto. omega.
Qed.

Lemma pud_pool_ne_pmd_next:
  forall addr a b vmid lnpt (Ha: 0 <= a) (Hb: 0 <= b) (Hvmid: 0 <= vmid)
    (Hvalid: valid_lnpt vmid lnpt)
    (Htable: pmd_table (addr @ (pt_pud_pool lnpt)) = PMD_TYPE_TABLE),
    Z.lor (phys_page (addr @ (pt_pud_pool lnpt))) (Z.land a 511 * 8) <>
    Z.lor (pt_pmd_next lnpt) (Z.land b 511 * 8).
Proof.
  intros. Transparent Z.add. destruct Hvalid. autounfold in Hpmd_next_range.
  pose proof (Hpud_pool addr) as Hpud_pool'.
  repeat rewrite simpl_land_mult.
  destruct Hpud_pool' as [Hpud_pool' | Hpud_pool'].
  rewrite Hpud_pool'. simpl. autounfold in Hpud_next_range. autounfold.
  intros.
  rewrite <- Z.bits_inj_iff in H. unfold Z.eqf in H.
  assert (forall n, ~(Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                 Z.testbit (Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n)) as Hall_not_not.
  intros. autounfold. intros Hcond. apply Hcond. trivial.
  apply Logic.Classical_Pred_Type.all_not_not_ex in Hall_not_not.
  assert (exists n, Z.testbit (Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n = true /\
               16 <= n) as Hex.
  assert (Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) >= 69632) as Hlor_lower.
  assert (69632 <= pt_pmd_next lnpt) as Ha_lower by auto with zarith.
  assert (0 <= pt_pmd_next lnpt) as Ha_lower' by auto with zarith.
  assert (0 < pt_pmd_next lnpt) as Ha_lower'' by auto with zarith.
  assert (0 <= Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) as Hland_nonneg.
  apply Z.land_nonneg. rewrite Hshiftl3. auto with zarith.
  pose proof (lor_lower_bound_l (pt_pmd_next lnpt)
                                (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) Ha_lower' Hland_nonneg) as Hlor_lower.
  auto with zarith. apply Z.ge_le in Hlor_lower.
  assert (0 < Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) as Hlor_lower'.
  auto with zarith.
  pose proof (bits_iff_ge (Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) Hlor_lower'
                          69632 Hlor_lower).
  destruct H0. exists x. simpl in H0. apply H0.
  assert (exists n , Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n <>
                Z.testbit (Z.lor (pt_pmd_next lnpt) (Z.land (Z.shiftl b 3) (Z.shiftl 511 3))) n) as Hcontra.
  destruct Hex as (x & Heex). destruct Heex as [Htest_t Hx]. assert (12 <= x) as Hx' by omega.
  pose proof (Htest_f x Hx') as Htest_f'.
  exists x. rewrite Htest_f'. rewrite Htest_t. easy. auto.
  contradict Hcontra. auto.

  destruct Hpud_pool' as [Hpud_pool' | [_ [Hpud_pool' Hpud_pool'']]]. auto.
  autounfold. rewrite <- Z.bits_inj_iff. unfold Z.eqf. intros Hfalse.
  assert (forall n, (Z.testbit (phys_page addr @ (pt_pud_pool lnpt)) n) ||
               (Z.testbit (Z.land (Z.shiftl a 3) (Z.shiftl 511 3)) n) =
               (Z.testbit (pt_pmd_next lnpt) n) || (Z.testbit (Z.land (Z.shiftl b 3) (Z.shiftl 511 3)) n))
    as Hfalse_spec.
  intros. repeat rewrite <- Z.lor_spec. apply Hfalse.

  assert (forall n, Z.testbit (phys_page addr @ (pt_pud_pool lnpt)) n =
               Z.testbit (pt_pmd_next lnpt) n) as Hhigh_or'.
  intros. assert (n < 12 \/ 12 <= n) as Hn by omega. destruct Hn as [Hn | Hn].
  rewrite <- Hpmd_next_align. unfold phys_page. unfold PHYS_MASK, PAGE_MASK.
  repeat rewrite <- Z.land_assoc. simpl. repeat rewrite Z.land_spec.
  assert (n < 0 \/ 0 <= n < 12) as Hn' by omega. destruct Hn' as [Hn' | Hn'].
  pose proof (testbit_false_neg 281474976710655 n Hn') as Htest_n. rewrite Htest_n.
  now repeat rewrite andb_false_r.
  assert (-1 < n <= 11) as Hn'' by omega.
  destruct_case Hn''; rewrite T; simpl; now repeat rewrite andb_false_r.
  pose proof (Hhigh_or n Hn a Ha (Z.testbit (phys_page addr @ (pt_pud_pool lnpt)) n)) as Hhigh_or'0.
  pose proof (Hhigh_or n Hn b Hb (Z.testbit (pt_pmd_next lnpt) n)) as Hhigh_or'1.
  pose proof (Hfalse_spec n) as Hfalse_spec'. rewrite Hhigh_or'0, Hhigh_or'1 in Hfalse_spec'. auto.
  assert (phys_page addr @ (pt_pud_pool lnpt)  = pt_pmd_next lnpt) as Hfalse_eq.
  apply Z.bits_inj'. auto. omega.
Qed.

Lemma vttbr_align:
  forall vmid (Hvmid: valid_vmid vmid), phys_page (pool_start vmid) = pool_start vmid.
Proof.
  intros. repeat autounfold in Hvmid. unfold pool_start. unfold PT_POOL_START, PT_POOL_PER_VM.
  apply Z.bits_inj_iff'. intros.
  assert (0 <= n < 12 \/ 12 <= n < 48 \/ 48 <= n) as Hn by omega. destruct Hn as [Hn | [Hn | Hn]].
  rewrite phys_page_testbit_low by auto with zarith.
  replace (65536 + 33554432 * vmid) with (65536 * (1 + 512 * vmid)).
  replace (65536) with (2^16) by auto with zarith. rewrite Z.mul_comm.
  now rewrite Z.mul_pow2_bits_low by auto with zarith.
  rewrite Z.mul_add_distr_l. auto with zarith.
  apply phys_page_testbit_mid; auto with zarith.
  rewrite phys_page_testbit_high by auto with zarith.
  assert (65536 + 33554432 * vmid <= 536936458) by omega.
  apply Z.log2_le_mono in H0. replace (Z.log2 536936458) with (29) in H0 by auto with zarith.
  symmetry. apply Z.bits_above_log2; omega.
Qed.

Lemma vttbr_nz:
  forall vmid (Hvmid: valid_vmid vmid), pool_start vmid <> 0.
Proof.
  intros. autounfold in *. omega.
Qed.

Lemma pgd_index_diff_res_diff:
  forall addr addr0 vmid lnpt (Hvalid: valid_lnpt vmid lnpt),
    let pgd_idx := pgd_index addr in
    let pgd_idx0 := pgd_index addr0 in
    let vttbr := pool_start vmid in
    let pgd_p := Z.lor vttbr (pgd_idx * 8) in
    let pgd := pgd_p @ (pt_vttbr_pool lnpt) in
    let pgd_p0 := Z.lor vttbr (pgd_idx0 * 8) in
    let pgd0 := pgd_p0 @ (pt_vttbr_pool lnpt) in
    forall (Hpgd_nz: pgd <> 0) (Hpgd0_nz: pgd0 <> 0),
      pgd_idx <> pgd_idx0 -> phys_page pgd <> phys_page pgd0.
Proof.
  intros. unfold pgd_index in *.
  destruct Hvalid. assert (vttbr = pool_start vmid) as vttbr_val by reflexivity.
  assert (pgd_p <> pgd_p0). unfold pgd_p, pgd_p0. unfold pgd_idx, pgd_idx0 in *.
  apply (or_index_ne_cond vttbr vttbr (Z.shiftr addr PGDIR_SHIFT)
                          (Z.shiftr addr0 PGDIR_SHIFT)); try apply vttbr_align; auto.
  pose proof (Hvttbr_pool  pgd_p).
  pose proof (Hvttbr_pool pgd_p0).
  autounfold. unfold pgd, pgd0. intros.
  destruct H1, H2. unfold pgd0 in Hpgd0_nz. rewrite H2 in Hpgd0_nz. auto.
  destruct H2. unfold pgd in Hpgd_nz. rewrite H1 in Hpgd_nz. auto.
  unfold pgd0 in Hpgd0_nz. rewrite H2 in Hpgd0_nz. auto.
  destruct H1, H2. autounfold in H4, H5. srewrite. auto.
Qed.

Lemma pud_index_diff_res_diff:
  forall addr addr0 vmid lnpt (Hvalid: valid_lnpt vmid lnpt),
    let pgd_idx := pgd_index addr in
    let pud_idx := pud_index addr in
    let pgd_idx0 := pgd_index addr0 in
    let pud_idx0 := pud_index addr0 in
    let vttbr := pool_start vmid in
    let pgd_p := Z.lor vttbr (pgd_idx * 8) in
    let pgd := pgd_p @ (pt_vttbr_pool lnpt) in
    let pgd_p0 := Z.lor vttbr (pgd_idx0 * 8) in
    let pgd0 := pgd_p0 @ (pt_vttbr_pool lnpt) in
    let pud_p := Z.lor (phys_page pgd) (pud_idx * 8) in
    let pud := pud_p @ (pt_pgd_pool lnpt) in
    let pud_p0 := Z.lor (phys_page pgd0) (pud_idx0 * 8) in
    let pud0 := pud_p0 @ (pt_pgd_pool lnpt) in
    forall (Hpgd_nz: pgd <> 0) (Hpgd0_nz: pgd0 <> 0)
      (Hpud_nz: pud <> 0) (Hpud0_nz: pud0 <> 0),
      pgd_idx <> pgd_idx0 \/ pud_idx <> pud_idx0 -> phys_page pud <> phys_page pud0.
Proof.
  intros. unfold pgd_index, pud_index in *.
  assert (pud_p <> pud_p0) as Hpudp_ne. unfold pud_p, pud_p0 in *. unfold pud_idx, pud_idx0 in *.
  apply (or_index_ne_cond (phys_page pgd) (phys_page pgd0) (Z.shiftr addr PUD_SHIFT)
                          (Z.shiftr addr0 PUD_SHIFT)); auto using phys_page_fixed.
  destruct H.
  left.
  apply (pgd_index_diff_res_diff addr addr0 vmid lnpt Hvalid Hpgd_nz Hpgd0_nz H).
  auto.
  destruct Hvalid.
  pose proof (Hpgd_pool pud_p) as Hpgd_pool'.
  pose proof (Hpgd_pool pud_p0) as Hpgd0_pool'.
  autounfold. intros. unfold pud, pud0 in H0.
  destruct Hpgd_pool'. unfold pud in Hpud_nz. rewrite H1 in Hpud_nz. auto.
  destruct Hpgd0_pool'. unfold pud0 in Hpud0_nz. rewrite H2 in Hpud0_nz. auto.
  destruct H1, H2. autounfold in H3, H4. srewrite. auto.
Qed.

Lemma pmd_index_diff_res_diff:
  forall addr addr0 vmid lnpt (Hvalid: valid_lnpt vmid lnpt),
    let pgd_idx := pgd_index addr in
    let pud_idx := pud_index addr in
    let pmd_idx := pmd_index addr in
    let pgd_idx0 := pgd_index addr0 in
    let pud_idx0 := pud_index addr0 in
    let pmd_idx0 := pmd_index addr0 in
    let vttbr := pool_start vmid in
    let pgd_p := Z.lor vttbr (pgd_idx * 8) in
    let pgd := pgd_p @ (pt_vttbr_pool lnpt) in
    let pgd_p0 := Z.lor vttbr (pgd_idx0 * 8) in
    let pgd0 := pgd_p0 @ (pt_vttbr_pool lnpt) in
    let pud_p := Z.lor (phys_page pgd) (pud_idx * 8) in
    let pud := pud_p @ (pt_pgd_pool lnpt) in
    let pud_p0 := Z.lor (phys_page pgd0) (pud_idx0 * 8) in
    let pud0 := pud_p0 @ (pt_pgd_pool lnpt) in
    let pmd_p := Z.lor (phys_page pud) (pmd_idx * 8) in
    let pmd := pmd_p @ (pt_pud_pool lnpt) in
    let pmd_p0 := Z.lor (phys_page pud0) (pmd_idx0 * 8) in
    let pmd0 := pmd_p0 @ (pt_pud_pool lnpt) in
    forall (Hpgd_nz: pgd <> 0) (Hpgd0_nz: pgd0 <> 0)
      (Hpud_nz: pud <> 0) (Hpud0_nz: pud0 <> 0)
      (Hpmd_table: pmd_table pmd = PMD_TYPE_TABLE) (Hpmd_nz: pmd <>0)
      (Hpmd0_table: pmd_table pmd0 = PMD_TYPE_TABLE) (Hpmd0_nz: pmd0 <> 0),
      pgd_idx <> pgd_idx0 \/ pud_idx <> pud_idx0 \/ pmd_idx <> pmd_idx0 ->
      phys_page pmd <> phys_page pmd0.
Proof.
  intros. unfold pgd_index, pud_index, pmd_index in *.
  assert (pmd_p <> pmd_p0) as Hpmdp_ne. unfold pmd_p, pmd_p0 in *. unfold pmd_idx, pmd_idx0 in *.
  apply (or_index_ne_cond (phys_page pud) (phys_page pud0) (Z.shiftr addr PMD_SHIFT)
                          (Z.shiftr addr0 PMD_SHIFT)); auto using phys_page_fixed.
  apply or_assoc in H. destruct H.
  left.
  apply (pud_index_diff_res_diff addr addr0 vmid lnpt Hvalid
                                 Hpgd_nz Hpgd0_nz Hpud_nz Hpud0_nz H).
  auto.
  destruct Hvalid.
  pose proof (Hpud_pool pmd_p) as Hpud_pool'.
  pose proof (Hpud_pool pmd_p0) as Hpud0_pool'.
  autounfold. intros. unfold pmd, pmd0 in H0.
  destruct Hpud_pool'. unfold pmd in Hpmd_nz. rewrite H1 in Hpmd_nz. auto.
  destruct Hpud0_pool'. unfold pmd0 in Hpmd0_nz. rewrite H2 in Hpmd0_nz. auto.
  destruct H1, H2; auto.
  destruct H1, H2. destruct H3, H4. autounfold in H5, H6. srewrite. auto.
Qed.

Lemma vttbr_val:
  forall vmid (Hvm: valid_vmid vmid),
    phys_page (pt_vttbr vmid) = pool_start vmid.
Proof.
  intros. unfold pool_start.
  unfold pt_vttbr. unfold PT_POOL_START, PT_POOL_PER_VM.
  replace (65536 + 33554432 * vmid) with ((1 + 512 * vmid) * 2^16).
  apply Z.bits_inj_iff'. intros.
  assert (0 <= n < 12 \/ 12 <= n < 48 \/ 48 <= n) as Hn by omega.
  destruct Hn as [Hn | [Hn | Hn]];
    rewrite ?phys_page_testbit_low, ?phys_page_testbit_mid, ?phys_page_testbit_high
    by auto with zarith.
  rewrite Z.mul_pow2_bits_low; auto with zarith.
  replace (281474976710656) with (2^48) by auto with zarith.
  rewrite Z.lor_spec. rewrite orb_comm. rewrite Z.mul_pow2_bits_low by auto with zarith.
  apply orb_false_l.
  autounfold in Hvm.
  replace (2 ^ 16) with 65536 by auto with zarith.
  assert (((1 + 512 * vmid) * 65536) <= 536936448). omega.
  apply Z.log2_le_mono in H0. replace (Z.log2 536936448) with 29 in H0 by auto with zarith.
  symmetry. apply Z.bits_above_log2; omega.
  autounfold in Hvm.
  replace (2 ^ 16) with 65536 by auto with zarith.
  rewrite Z.mul_comm, Z.mul_add_distr_l. auto with zarith.
Qed.
```
