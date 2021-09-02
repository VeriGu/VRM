# HypsecCommLib

```coq
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import MemoryX.
Require Import Events.
Require Import EventsX.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import Locations.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import LoopProof.
Require Import VCGen.
Require Import Errors.
Require Import Op.
Require Import Smallstep.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import GenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import Conventions.
Require Import Clight.
Require Import CDataTypes.
Require Import CLemmas.
Require Import XOmega.
Require Import ZArith.
Require Import TacticsForTesting.
Require Import CommonTactic.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import Ctypes.

Require Import Constants.
Require Import RData.

Local Open Scope Z.

(* Common Lemmas *)

Lemma zgt_false_le: forall x y, (x >? y) = false <-> x <= y.
Proof.
  split.
  - intros. pose (Zgt_cases x y).
    rewrite H in y0. assumption.
  - intros. apply Zle_imp_le_bool in H.
    unfold Z.leb in H. unfold Z.gtb.
    destruct (x ?= y); reflexivity || inversion H.
Qed.

Lemma zge_false_lt: forall x y, (x >=? y) = false <-> x < y.
Proof.
  split.
  - intros. pose (Zge_cases x y).
    rewrite H in y0. assumption.
  - intros.
    unfold Z.lt in H. unfold Z.geb.
    destruct (x ?= y); reflexivity || inversion H.
Qed.

Lemma zeq_false_ne: forall x y, (x =? y) = false <-> x <> y.
Proof.
  split.
  - intros.
    red. intro. rewrite <- Z.eqb_eq in H0.
    rewrite H in H0. inversion H0.
  - intros. red in H. destruct (x =? y) eqn:H1.
    rewrite Z.eqb_eq in H1. apply H in H1. inversion H1.
    reflexivity.
Qed.

Lemma add_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= a + b.
Proof.
  intros. omega.
  Qed.

Lemma sub_ge0_if:
  forall a b (Hab: a <= b), 0 <= b - a.
Proof.
  intros. omega.
  Qed.

Lemma mul_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= a * b.
Proof.
  intros. induction a. omega. induction b. omega.
  simpl. unfold "<=". unfold "?=". trivial.
  assert (0 = Z.neg p0). assert (Z.neg p0 <= 0). easy. omega.
  rewrite <- H. unfold "*". reflexivity.
  assert (0 = Z.neg p). assert (0 >= (Z.neg p)). easy. omega.
  rewrite <- H. omega.
Qed.

Lemma divu_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 < b), 0 <= a / b.
Proof.
  intros. pose proof (Z_div_pos a b). assert (b > 0). omega. apply H in H0. auto. auto.
Qed.

Lemma land_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= Z.land a b.
Proof.
  intros. Transparent Z.land. induction a. easy. induction b. easy.
  unfold Z.land. now destruct Pos.land.
  now assert (0 > Z.neg p0). now assert (0 > Z.neg p).
Qed.

Lemma lor_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= Z.lor a b.
Proof.
  intros. Transparent Z.lor. induction a. easy. induction b. easy.
  unfold Z.lor. now destruct Pos.lor.
  now assert (0 > Z.neg p0). now induction b.
Qed.

Lemma shiftl_ge0_if':
  forall (b: nat) (Hb: 0 <= Z.of_nat b) a (Ha: 0 <= a), 0 <= Z.shiftl a (Z.of_nat b).
Proof.
  intros. induction b. easy. induction a; simpl.
  now replace  (Pos.iter (Pos.of_succ_nat b)  (Z.mul 2) 0) with 0 by
      (apply Pos.iter_invariant; intros; subst; trivial).
  now rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial. now assert (0 > Z.neg p).
Qed.

Lemma shiftl_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= Z.shiftl a b.
Proof.
  intros. assert (0 <= Z.of_nat (Z.to_nat b)) as Hb'. omega.
  pose proof (shiftl_ge0_if' (Z.to_nat b) Hb' a Ha).
  assert (Z.of_nat (Z.to_nat b) = b). apply Z2Nat.id. apply Hb.
  rewrite H0 in H. apply H.
Qed.

(* Credit: https://github.com/antalsz/hs-to-coq/blob/master/examples/containers/theories/BitUtils.v *)
Lemma pos_nonneg: forall p, (0 <= N.pos p)%N.
Proof.
  compute; congruence.
Qed.

Lemma pos_pos: forall p, (0 < N.pos p)%N.
Proof.
  compute; congruence.
Qed.

Lemma succ_nonneg: forall n, 0 <= n -> 0 <= Z.succ n.
Proof. intros. omega. Qed.


Lemma ones_nonneg: forall n, 0 <= n -> 0 <= Z.ones n.
Proof.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by assumption.
  rewrite Z.mul_1_l.
  rewrite <- Z.lt_le_pred.
  apply Z.pow_pos_nonneg; auto.
  omega.
Qed.

Lemma log2_ones: forall n, 0 < n -> Z.log2 (Z.ones n) = Z.pred n.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_1_l.
  apply Z.log2_pred_pow2.
  assumption.
Qed.

Create HintDb nonneg.
Hint Immediate N2Z.is_nonneg : nonneg.
Hint Immediate pos_nonneg : nonneg.
Hint Resolve N.le_0_l : nonneg.
Hint Resolve Z.log2_nonneg : nonneg.
Hint Resolve ones_nonneg : nonneg.
Hint Resolve succ_nonneg : nonneg.
Hint Resolve <- Z.shiftl_nonneg : nonneg.
Hint Resolve <- Z.shiftr_nonneg : nonneg.
Hint Resolve <- Z.land_nonneg : nonneg.
Hint Resolve Z.pow_nonneg : nonneg.
Hint Extern 1 (0 <= Z.succ (Z.pred (Z.of_N _))) => rewrite Z.succ_pred : nonneg.
Hint Resolve <- Z.lxor_nonneg : nonneg.
Hint Extern 0 => omega : nonneg.

Ltac nonneg := solve [auto with nonneg].
Ltac Nomega := rewrite ?N.pred_sub in *; zify; omega.

Lemma of_N_shiftl:
  forall n i, Z.of_N (N.shiftl n i) = Z.shiftl (Z.of_N n) (Z.of_N i).
Proof.
  intros.
  apply Z.bits_inj_iff';intros j?.
  replace j with (Z.of_N (Z.to_N j))
    by (rewrite -> Z2N.id by assumption; reflexivity).
  rewrite N2Z.inj_testbit.
  destruct (N.leb_spec i (Z.to_N j)).
  * rewrite -> N.shiftl_spec_high' by assumption.
    rewrite -> Z.shiftl_spec by nonneg.
    rewrite <- N2Z.inj_sub by assumption.
    rewrite N2Z.inj_testbit.
    reflexivity.
  * rewrite -> N.shiftl_spec_low by assumption.
    rewrite -> Z.shiftl_spec_low by Nomega.
    reflexivity.
Qed.

(* Credit: https://github.com/antalsz/hs-to-coq/blob/master/examples/containers/theories/BitUtils.v *)

Lemma of_N_shiftr:
  forall n i (Hn: 0 <= Z.of_N n) (Hi: 0 <= Z.of_N i), Z.of_N (N.shiftr n i) = Z.shiftr (Z.of_N n) (Z.of_N i).
Proof.
  intros. destruct i. simpl. unfold Z.shiftr. simpl. easy.
  simpl. induction n. simpl. unfold Z.shiftr. simpl.
  replace (Pos.iter p Z.div2 0) with 0 by (apply Pos.iter_invariant; intros; subst; trivial).
  now replace (Pos.iter p N.div2 0%N) with 0%N by (apply Pos.iter_invariant; intros; subst; trivial).
  unfold Z.shiftr. simpl.
  change (Z.pos p0) with (Z.of_N (N.pos p0)) at 1.
  rewrite <- (Pos.iter_swap_gen _ _ _ Ndiv2). reflexivity.
  intros. induction a. auto. simpl. induction p1; simpl; reflexivity.
Qed.

Lemma shiftr_ge0_if'':
  forall b a ,  0 <= Z.of_N (N.shiftr a b).
Proof.
  intros b. induction b using  N.peano_ind; intros.
  unfold N.shiftr. now induction a. now destruct N.shiftr.
Qed.

Lemma shiftr_ge0_if:
  forall a b (Ha: 0 <= a) (Hb: 0 <= b), 0 <= Z.shiftr a b.
Proof.
  intros.
  assert (Z.of_N (Z.to_N a) = a) as Ida. apply Z2N.id. apply Ha. rewrite <- Ida in Ha.
  assert (Z.of_N (Z.to_N b) = b) as Idb. apply Z2N.id. apply Hb. rewrite <- Idb in Hb.
  pose proof (of_N_shiftr (Z.to_N a) (Z.to_N b) Ha Hb) as Hn. rewrite <- Ida. rewrite <- Idb.
  rewrite <- Hn. exact (shiftr_ge0_if'' (Z.to_N b) (Z.to_N a)).
Qed.

(* Credit: https://github.com/coq-community/qarith-stern-brocot/blob/master/Zaux.v *)
Ltac Flip :=
  apply Z.gt_lt || apply Z.lt_gt || apply Z.le_ge || apply Z.ge_le; assumption.

Lemma Z_div_neg :
  forall a b : Z, (0 < b) -> (a < 0) -> (a / b < 0).
Proof.
 intros.
 rewrite (Z_div_mod_eq a b) in H0.
 elim (Z_mod_lt a b).
 intros H1 _.
 apply Znot_ge_lt.
 intro.
 apply (Zlt_not_le (b * (a / b) + a mod b) 0 H0).
 apply Zplus_le_0_compat.
 apply Zmult_le_0_compat.
 apply Zlt_le_weak; assumption.
 Flip.
 assumption.
 Flip.
 Flip.
Qed.

Lemma Z_div_le :
 forall a b c : Z, (0 < c)%Z -> (b <= a)%Z -> (b / c <= a / c)%Z. 
Proof.
 intros.
 apply Z.ge_le.
 apply Z_div_ge; Flip; assumption.
Qed.

Lemma Z_div_le0:
  forall a b:Z, b >= 2 -> a >= 0 -> a/b <= a.
Proof.
  intros. induction a. auto with zarith. induction b. assert (0 < 2). omega. contradiction.
  assert (Z.pos p / Z.pos p0 < Z.pos p). apply Z_div_lt. auto. auto with zarith. auto with zarith.
  assert (Z.neg p0 < 2). easy. contradiction. induction b. assert (Z.neg p < 0). easy. contradiction.
  assert (Z.neg p < 0). easy. contradiction. assert (Z.neg p < 0). easy. contradiction.
Qed.

Lemma Z_div_mult_ge:
  forall a b:Z, b > 0 -> (a/b)*b <= a.
Proof.
  intros. assert ((a / b) * b = b * (a / b)). auto with zarith. rewrite H0.
  pose proof (Z_mult_div_ge a b). apply H1 in H. apply H.
Qed.

Lemma add_leN_if:
  forall a b N (Ha: a <= N/2) (Hb: b <= N/2), a + b <= N.
Proof.
  intros. assert (a + b <= N / 2 + b). auto with zarith. pose proof (Zplus_le_compat_l b (N / 2) (N / 2)).
  assert (b <= N / 2). auto. apply H0 in H1. assert (N / 2 + N / 2 <= N / 2 * 2). auto with zarith.
  pose proof (Z_div_mult_ge N 2). assert (2 > 0). easy. apply H3 in H4.
  transitivity (N / 2 + b). auto. transitivity (N / 2 + N / 2). auto. transitivity (N / 2 * 2). auto. auto.
Qed.

Lemma sub_leN_if:
  forall a b N (Ha: a <= N) (Hb: b >= 0), a - b <= N.
Proof.
  intros.  auto with zarith. Qed.

(* TODO: should be 0 < b ?*)
Lemma mul_leN_if:
  forall a b N (Ha: a <= N / b) (Hb: 0 < b), a * b <= N.
Proof.
  intros. assert (a * b <= N / b * b). auto with zarith. assert (N / b * b <= N).
  pose proof (Z_div_mult_ge N b). assert (b > 0). apply Z.lt_gt. apply Hb. apply H0 in H1. apply H1.
  transitivity (N / b * b). apply H. apply H0.
Qed.

Lemma divu_leN_if:
  forall a b N (Ha: a <= N * b) (Hb: 0 < b), a / b <= N.
Proof.
  intros. pose proof (Z_div_le (N * b) a b). assert (0 < b). auto. apply H in H0.
  pose proof (Z_div_mult_full N b). assert (b <> 0). auto with zarith. apply H1 in H2.
  transitivity (N * b / b). apply H0. rewrite H2. auto with zarith. apply Ha.
Qed.

 Lemma Z64_land_range_hi: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> Z.land x y <= Int64.max_unsigned.
 Proof.
   rewrite max_unsigned64_val.
   intros.
   assert (Z.land x y < 18446744073709551616).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
       apply Z.log2_land.
       omega.
       omega.
     rewrite Zmin_spec in H1.
     destruct (zlt (Z.log2 x) (Z.log2 y)).
     assert(Z.log2 x <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

Lemma size_nat2p:
  forall p: positive, (Pos.size_nat p) = Pos.to_nat (Pos.size p).
Proof.
  intros. induction p; simpl. rewrite IHp. pose proof (Pos2Nat.inj_succ (Pos.size p)). rewrite H. try reflexivity.
  rewrite IHp. pose proof (Pos2Nat.inj_succ (Pos.size p)). rewrite H. try reflexivity. easy.
Qed.

(* Credit: https://github.com/mit-plv/fiat-crypto/blob/5cab97ed8f17e294f4e7e66010147a518c45f3a6/src/Util/NUtil/WithoutReferenceToZ.v#L22 *)
Lemma NPos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
Proof.
  induction a as [a IHa|a IHa|]; destruct b as [b|b|]; try solve [cbv; congruence];
    simpl; specialize (IHa b); case_eq (Pos.land a b); intro p; simpl;
    try apply N.le_0_l; intro land_eq;
    try rewrite land_eq in *; unfold N.le, N.compare in *;
    rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
    try assumption. easy.
  destruct (p ?=a)%positive; cbv; congruence.
Qed.

Lemma NPos_lor_lower_bound_l : forall a b, (Pos.lor a b >= a)%positive.
Proof.
  induction a as [a IHa|a IHa|]; destruct b as [b|b|]; try solve [cbv; congruence];
    simpl; try specialize (IHa b); try case_eq (Pos.lor a b); intro p; simpl; try intro lor_eq;
    try rewrite lor_eq in IHa; try assumption; try easy; unfold Pos.ge in *;
    try rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO, ?Pos.compare_xI_xO in *;
    try rewrite p in IHa; auto;
  try rewrite Pos.compare_refl in p; try easy.
  destruct (p~1 ?= a)%positive; cbv; congruence.
  destruct (p~0 ?= a)%positive; cbv; congruence.
  destruct (1 ?=a)%positive; simpl in lor_eq; try easy.
Qed.

Lemma Nlor_lower_bound_l: forall a b, (N.lor a b >= a)%N.
Proof.
  intros.
  destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence];
  cbv [Z.lor]; simpl. unfold N.ge. unfold N.compare. now rewrite Pos.compare_refl.
  now assert (Pos.lor p p0 >= p)%positive by auto using NPos_lor_lower_bound_l.
Qed.

Lemma lor_lower_bound_l:
  forall a b, (0 <= a) -> (0 <= b) -> Z.lor a b >= a.
Proof.
  intros a b H H0.
  destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
  cbv [Z.lor]. auto with zarith.
  unfold Z.lor. assert (Pos.lor p p0 >= p)%positive by
  auto using NPos_lor_lower_bound_l. auto.
Qed.

Lemma land_upper_bound_l:
  forall a b, (0 <= a) -> (0 <= b) -> Z.land a b <= a.
Proof.
  intros a b H H0.
  destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
  cbv [Z.land].
  rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
  auto using NPos_land_upper_bound_l.
Qed.

Lemma Nland_upper_bound_l:
  forall (a: N) (b: N), (N.land a b <= a)%N.
Proof.
  intros.
  destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
  cbv [N.land].
  auto using NPos_land_upper_bound_l.
Qed.

Lemma land_upper_bound_r:
  forall a b, (0 <= a) -> (0 <= b) -> Z.land a b <= b.
Proof.
  intros. rewrite Z.land_comm. revert H0 H. exact (land_upper_bound_l b a).
Qed.

Lemma land_upper_bound_r_strict:
  forall a b, (0 <= a) -> (0 <= b) -> (a < b) -> Z.land a b < b.
Proof.
  intros. pose proof (land_upper_bound_l a b H H0).
  pose proof (Zgt_le_trans b a (Z.land a b)).
  apply Z.lt_gt in H1. apply H3 in H1. apply Z.gt_lt. apply H1.
  apply H2.
Qed.

Lemma land_upper_bound_l_strict:
  forall a b, (0 <= a) -> (0 <= b) -> (b < a) -> Z.land a b < a.
Proof.
  intros. rewrite Z.land_comm. revert H0 H H1.
  exact (land_upper_bound_r_strict b a).
Qed.

Lemma land_leN_ge0:
  forall a b N (Ha: 0 <= a) (Hb: 0 <= b) (HaN: a <= N) (HbN: b <= N), Z.land a b <= N.
Proof.
  intros. pose proof (Ztrichotomy a b) as Habtri.
  induction N.
  assert (a = 0) as Ha0. omega. assert (b = 0) as Hb0. omega. now rewrite Ha0, Hb0.
  assert (a < Z.pos p \/ (a = Z.pos p)) as Ha_le_or_eq by now apply Zle_lt_or_eq.
  assert (b < Z.pos p \/ (b = Z.pos p)) as Hb_le_or_eq by now apply Zle_lt_or_eq.
  destruct Ha_le_or_eq as [HaN' | HaN']; destruct Hb_le_or_eq as [HbN' | HbN'];
    destruct Habtri as [Hab | Hab'];
    try (rewrite <- HbN'; now pose proof (land_upper_bound_r a b Ha Hb));
    try (rewrite <- HaN'; now pose proof (land_upper_bound_l a b Ha Hb));
  assert (Z.land a b < Z.pos p).
  pose proof (land_upper_bound_r_strict a b Ha Hb Hab). now transitivity b.
  omega.
  destruct Hab' as [Hab | Hab].
  rewrite Hab. now rewrite Z.land_diag.
  apply Z.gt_lt in Hab.
  pose proof (land_upper_bound_l_strict a b Ha Hb Hab). transitivity a. apply H. apply HaN'.
  omega.
  assert (0 <= Z.neg p). transitivity a. apply Ha. apply HaN.
  assert (0 > Z.neg p). easy. contradiction.
Qed.

Lemma Nadd1_lt:
  forall (m: N), (m < m + 1)%N.
Proof.
  intros. induction m. easy. simpl. unfold N.lt. unfold N.compare.
  replace (p + 1)%positive with (Pos.succ p). apply Pos.lt_succ_diag_r. rewrite <- Pos.add_1_r. reflexivity.
Qed.

Lemma land_leN_if':
  forall (p p0: positive) N, (Z.pos p <= N) -> (Z.neg p0 <= N) -> Z.land (Z.pos p) (Z.neg p0) <= N.
Proof.
  intros.
  unfold Z.land.
  pose proof (N.ldiff_land_low (N.pos p) (Pos.pred_N p0) ((N.log2 (N.pos p)) + 1)).
  exploit H1. apply Nadd1_lt. intros. rewrite H2.
  assert (N.land (N.pos p) (N.lnot (Pos.pred_N p0) (N.log2 (N.pos p) + 1)) <= (N.pos) p)%N.
  apply Nland_upper_bound_l. rewrite N2Z.inj_le in H3.
  assert (Z.of_N (N.pos p) = Z.pos p). auto with zarith. rewrite H4 in H3.
  transitivity (Z.pos p); auto.
Qed.

Hypothesis land_leN_if:
  forall a b N (Hb: b <= N), Z.land a b <= N.

Lemma NPos__bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
Proof.
  induction a as [a IHa|a IHa|]; destruct b as [b|b|]; try solve [cbv; congruence];
    simpl; specialize (IHa b); case_eq (Pos.land a b); intro p; simpl;
    try apply N.le_0_l; intro land_eq;
    try rewrite land_eq in *; unfold N.le, N.compare in *;
    rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
    try assumption. easy.
  destruct (p ?=a)%positive; cbv; congruence.
Qed.

(* Xuheng update the Lemma *)
Hypothesis lor_leN_if:
  forall a b N (Hab: a + b <= N), Z.lor a b <= N.

Hypothesis shiftl_leN_if:
  forall a b N (Ha: a * 281474976710656 <= N) (Hb1: 0 <= b) (Hb2: b <= 48), Z.shiftl a b <= N.

Hypothesis shiftr_leN_if:
  forall a b N (Ha: a <= N) (Hb: 0 <= b), Z.shiftr a b <= N.

Lemma int_max_unsigned:
  Int.max_unsigned = 4294967295.
Proof.
  intros. reflexivity.
Qed.

Lemma int64_max_unsigned:
  Int64.max_unsigned = 18446744073709551615.
Proof.
  intros. reflexivity.
  Qed.

Lemma int_bound:
  forall z,
    0 <= Int.unsigned z <= 4294967295.
Proof.
  intros.
  apply Int.unsigned_range_2.
Qed.

Lemma int_bound64:
  forall z, 0 <= Int.unsigned z <= 18446744073709551615.
Proof.
  intros. auto. pose (int_bound z). omega.
Qed.

Lemma int64_bound:
  forall z, 0 <= Int64.unsigned z <= 18446744073709551615.
Proof.
  intros. apply Int64.unsigned_range_2.
Qed.

Lemma invalid_repr:
  Int.repr (-1) = Int.repr INVALID.
Proof.
  Local Transparent Int.repr.
  intros. unfold INVALID.
  unfold Int.repr.
  assert(Int.Z_mod_modulus (-1) = Int.Z_mod_modulus 4294967295) by reflexivity.
  apply Int.mkint_eq. assumption.
  Local Opaque Int.repr.
Qed.

Lemma invalid64_repr:
  Int64.repr (-1) = Int64.repr INVALID64.
Proof.
  Local Transparent Int64.repr.
  intros. unfold INVALID64.
  unfold Int64.repr.
  apply Int64.mkint_eq.
  reflexivity.
  Local Opaque Int64.repr.
Qed.

Lemma cast_u32_u64:
  forall z, Int64.unsigned (cast_int_long Unsigned z) = (Int.unsigned z).
Proof.
  intros. destruct z. simpl.
  rewrite Int64.unsigned_repr.
  reflexivity.
  rewrite int64_max_unsigned.
  unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize,two_power_nat, shift_nat, nat_iter in intrange.
  omega.
Qed.

Lemma int_eq_Z:
  forall x y ,(Int.unsigned x = Int.unsigned y) -> x = y.
Proof.
  intros. destruct x, y.
  apply Int.mkint_eq.
  simpl in H. assumption.
Qed.

Lemma int64_eq_Z:
  forall x y ,(Int64.unsigned x = Int64.unsigned y) -> x = y.
Proof.
  intros. destruct x, y.
  apply Int64.mkint_eq.
  simpl in H. assumption.
Qed.

Lemma loop_nat_sub1:
  forall m n, m >= n -> Z.to_nat (m - (n - 1)) = S (Z.to_nat (m - n)).
Proof.
  intros. rewrite Z.sub_sub_distr. apply Z2Nat.inj_succ.
  omega.
Qed.

Lemma loop_ind_sub1:
  forall m n, Z.of_nat (S n) <= m -> Z.to_nat (m - Z.of_nat n) = S (Z.to_nat (m - Z.of_nat (S n))).
Proof.
  intros. auto with zarith.
  rewrite Nat2Z.inj_succ. simpl.
  replace (m - Z.of_nat n) with (Z.succ (m - Z.of_nat n - 1)).
  rewrite Z2Nat.inj_succ.
  replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1).
  rewrite Z.sub_add_distr. reflexivity.
  auto with zarith. auto with zarith.
  rewrite Nat2Z.inj_succ in H. omega.
  rewrite Nat2Z.inj_succ in H. omega.
Qed.

Lemma host_pte_pfn_dev:
  forall addr, valid_addr addr -> phys_page (Z.lor (addr / PAGE_SIZE * PAGE_SIZE) (Z.lor PAGE_S2_DEVICE S2_RDWR)) / PAGE_SIZE = addr / PAGE_SIZE.
  intros. unfold phys_page. autounfold in *.
  rewrite <- Z.land_assoc. simpl.
  rewrite Z.land_lor_distr_l. simpl.
  rewrite Z.lor_land_distr_l. simpl.
  rewrite Z.lor_0_r. simpl.
  assert (4096 = 2^12) by auto with zarith.
  rewrite H0. repeat rewrite <- Z.shiftr_div_pow2 by auto with zarith.
  rewrite <- Z.shiftl_mul_pow2 by auto with zarith.
  rewrite Z.shiftr_land by auto with zarith.
  assert (Z.shiftr 281474976706560 12 = 68719476735) by auto with zarith.
  rewrite H1.
  rewrite Z.shiftr_shiftl_l by auto with zarith. simpl.
  destruct H. autounfold in *.
  assert(281474976710656 = 4096 * 68719476736) by auto with zarith.
  rewrite H3 in H2.
  apply Z.div_lt_upper_bound in H2. auto with zarith.
  rewrite H0 in H2.
  rewrite <- Z.shiftr_div_pow2 in H2 by auto with zarith.
  assert (68719476735 = Z.ones 36) by auto with zarith.
  rewrite H4.
  apply Z.land_ones_low.
  apply Z.shiftr_nonneg. auto.
  assert (Z.shiftr addr 12 <= 68719476735) by auto with zarith.
  apply Z.log2_le_mono in H5. simpl in H5.
  omega. reflexivity.
  Qed.
  
Lemma host_pte_pfn_mem:
  forall addr, valid_addr addr -> phys_page (Z.lor (addr / PAGE_SIZE * PAGE_SIZE) PAGE_S2_KERNEL) / PAGE_SIZE = addr / PAGE_SIZE.
  intros. unfold phys_page. autounfold.
  rewrite <- Z.land_assoc. simpl.
  rewrite Z.land_lor_distr_l. simpl.
  rewrite Z.lor_land_distr_l. simpl.
  rewrite Z.lor_0_r. simpl.
  assert (4096 = 2^12). auto with zarith.
  rewrite H0. repeat rewrite <- Z.shiftr_div_pow2 by auto with zarith.
  rewrite <- Z.shiftl_mul_pow2 by auto with zarith.
  rewrite Z.shiftr_land.
  assert (Z.shiftr 281474976706560 12 = 68719476735) by auto with zarith.
  rewrite H1.
  rewrite Z.shiftr_shiftl_l by auto with zarith. simpl.
  destruct H. autounfold in *.
  assert(281474976710656 = 4096 * 68719476736) by auto with zarith.
  rewrite H3 in H2.
  apply Z.div_lt_upper_bound in H2. auto with zarith.
  rewrite H0 in H2.
  rewrite <- Z.shiftr_div_pow2 in H2 by auto with zarith.
  assert (68719476735 = Z.ones 36) by auto with zarith.
  rewrite H4.
  apply Z.land_ones_low.
  apply Z.shiftr_nonneg. auto.
  assert (Z.shiftr addr 12 <= 68719476735) by auto with zarith.
  apply Z.log2_le_mono in H5. simpl in H5.
  omega. reflexivity.
  Qed.

Lemma vm_pte_pfn_level2:
  forall pte, phys_page (Z.land (Z.lor (phys_page pte) PAGE_S2_KERNEL) NOT_PMD_TABLE_BIT) = phys_page pte.
  intros. unfold phys_page. autounfold.
  repeat rewrite <- Z.land_assoc. simpl.
  rewrite ?Z.land_lor_distr_l, ?Z.lor_land_distr_l, <- ?Z.land_assoc, ?Z.lor_0_r. simpl.
  reflexivity.
Qed.

Lemma vm_pte_pfn_level3:
  forall pte, phys_page (Z.lor (phys_page pte) PAGE_S2_KERNEL) = phys_page pte.
  intros. unfold phys_page. autounfold.
  repeat rewrite <- Z.land_assoc. simpl.
  rewrite ?Z.land_lor_distr_l, ?Z.lor_land_distr_l.
  simpl. rewrite <- Z.land_assoc.
  rewrite Z.lor_0_r. simpl.
  reflexivity.
Qed.

Hypothesis vm_pte_pfn_dev:
  forall pa, valid_paddr pa ->
        let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
        phys_page pte / PAGE_SIZE = pa / PAGE_SIZE.

Lemma succ_plus_1:
  forall n, Z.succ n = n + 1.
Proof. intros. auto with zarith. Qed.

Hypothesis zmap_comm:
  forall a b, a <> b -> forall {T} m (x: T) (y: T), (m # a == x) # b == y = (m # b == y) # a == x.

Hypothesis zmap_set_id:
  forall {T} a (m: ZMap.t T), (m # a == (a @ m)) = m.

Section ListLemmas.

Lemma list_prefix_nil:
  forall {A:Type} (i: A) q q0 q1,
    ~ In i q ->
    q ++ i :: q0 = i :: q1 ->
    q = nil.
Proof.
  intros.
  destruct q.
  + auto.
  + simpl in *.
    injection H0;intros.
    contradict H. auto.
Qed.

Lemma list_In_middle:
  forall {A: Type} (i: A) q q0,
    In i (q ++ i :: q0).
Proof.
  induction q; simpl; intros; auto.
Qed.

Lemma list_valid_In_append:
  forall a curid l,
    (forall i0 e, In (TEVENT i0 e) (a :: l) -> i0 <> curid) ->
    (forall i0 e, In (TEVENT i0 e) l -> i0 <> curid).
Proof.
  intros.
  apply (H i0 e).
  right.
  auto.
Qed.

Lemma list_valid_In_append':
  forall a l P,
    (forall i0 e, In (TEVENT i0 e) (a :: l) -> P i0 e) ->
    (forall i0 e, In (TEVENT i0 e) l -> P i0 e).
Proof.
  intros; eauto. eapply X.
  right. trivial.
Qed.

Lemma list_append_trans:
  forall {A: Type} (i: A) l0 l,
    i :: (l0 ++ l) = (i::l0) ++ l.
Proof.
  reflexivity.
Qed.

Lemma list_append_neq0:
  forall {A: Type} l (a: A),
    l = a :: l -> False.
Proof.
  induction l; intros.
  - inv H.
  - inversion H. eauto.
Qed.

Lemma list_append_neq:
  forall {A: Type} l l' (a: A),
    l = l' ++ a :: l -> False.
Proof.
  induction l; intros.
  - destruct l'; inv H.
  - destruct l'; inversion H.
    + eapply list_append_neq0 in H2; eauto.
    + specialize (IHl (l' ++ a0 :: nil) a1). eapply IHl.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      rewrite app_nil_l. assumption.
Qed.

Lemma list_append_neq':
  forall {A: Type} (l l': list A),
    l = l' ++ l -> l' = nil.
Proof.
  destruct l; intros.
  - rewrite app_nil_r in H. congruence.
  - destruct l'; trivial.
    inversion H. clear H.
    eapply list_append_neq in H2. inv H2.
Qed.

Lemma list_append_e_eq:
  forall {A : Type} l0 l (e e0: A),
    l0 ++ e :: l = e0 :: l ->
    l0 = nil /\ e = e0.
Proof.
  induction l0; intros.
  - inv H. eauto.
  - inversion H.
    symmetry in H2.
    apply list_append_neq in H2. inv H2.
Qed.

Lemma list_not_e_nil:
  forall {A:Type} (e: A) l l',
    l ++ e :: l' <> nil.
Proof.
  destruct l.
  - intros l' HF. inv HF.
  - intros l' HF. inv HF.
Qed.

Lemma list_same_tail:
  forall {A : Type} l0 l1 (i j: A),
    l0 ++ i :: nil = l1 ++ j :: nil ->
    l0 = l1 /\ i = j.
Proof.
  induction l0; simpl; intros.
  - destruct l1.
    + inv H. auto.
    + inv H. symmetry in H2.
      eapply list_not_e_nil in H2. inv H2.
  - destruct l1.
    + inv H. eapply list_not_e_nil in H2. inv H2.
    + inv H. exploit IHl0; eauto.
      intros (? & ?); subst.
      auto.
Qed.


Lemma list_append_rewrite:
  forall {A: Type} l (a b: A),
    a :: b :: l = (a:: nil) ++ (b :: l).
Proof.
  intros.
  rewrite <- app_comm_cons. trivial.
Qed.

Lemma list_tail_one_element:
  forall {A : Type} l2 l0 l1 (i j: A)
         (Heq: l0 ++ i :: nil = l1 ++ j :: l2),
    (i = j /\ l2 = nil) \/
    (exists l2', l0 = l1 ++ j :: l2').
Proof.
  induction l2; simpl; intros.
  - eapply list_same_tail in Heq.
    destruct Heq as (? & ?); subst.
    left; auto.
  - right. rewrite list_append_rewrite in Heq.
    rewrite app_assoc in Heq.
    exploit IHl2; eauto.
    intros HF.
    destruct HF as [(? & ?) | HF']; subst.
    + eapply list_same_tail in Heq.
      destruct Heq as (? & _); subst.
      eauto.
    + destruct HF' as (l2' & HF').
      rewrite <- app_assoc in HF'.
      rewrite <- app_comm_cons in HF'.
      eauto.
Qed.


Lemma list_unique_element:
  forall {A: Type} q q' q0 q1 (z: A)
         (Heq: q ++ z :: q0 = q' ++ z :: q1)
         (Hnin: ~ In z q)
         (Hnin0: ~ In z q0),
    q = q' /\ q0 = q1.
Proof.
  induction q; simpl; intros.
  - destruct q'.
    + inv Heq. auto.
    + inv Heq. elim Hnin0.
      eapply list_In_middle; eauto.
  - destruct q'.
    + inv Heq. elim Hnin. left; trivial.
    + inv Heq. exploit IHq; eauto.
      intros (? & ?); subst. auto.
Qed.

Lemma list_not_in_append_re:
  forall {A: Type} (i: A) i0 l,
    ~ In i (i0 :: l) ->
    ~ In i l.
Proof.
  intros.
  simpl in H.
  tauto.
Qed.

Lemma list_not_in_append:
  forall {A: Type} (i: A) i0 l,
    ~ In i l ->
    i0 <> i ->
    ~ In i (i0 :: l).
Proof.
  intros.
  simpl.
  tauto.
Qed.

Lemma count_occ_append:
  forall l l' x,
    (count_occ zeq (l ++ l') x = count_occ zeq l x + count_occ zeq l' x) % nat.
Proof.
  induction l; simpl; intros; auto.
  destruct (zeq a x); subst.
  - erewrite IHl. omega.
  - eauto.
Qed.

End ListLemmas.

(* Tactics *)

Ltac contra :=
  match goal with
  | [H: Some _ = None |- _] => inversion H
  | [H: None = Some _ |- _] => inversion H
  | [H: true = false |- _] => inversion H
  | [H: false = true |- _] => inversion H
  | [H: ?x <> ?x |- _] => let T := fresh "T" in assert(T:x=x) by reflexivity; apply H in T; inversion T
  | [H: ?x = ?x -> False |- _] => let T := fresh "T" in assert(T:x=x) by reflexivity; apply H in T; inversion T
  | [H1: ?x = ?y, H2: ?x <> ?y |- _] => apply H2 in H1; inversion H1
  | H: ?x, H': ?x -> False |- _ => apply H' in H; inversion H
  | [H1: ?x = true, H2: ?x = false |- _] => rewrite H1 in H2; inversion H2
  | [|- _] => idtac
  end.

Ltac clear_hyp :=
  repeat
    match goal with
    | [H: ?x = ?x |- _ ] => clear H
    | [H1: ?P, H2: ?P |- _ ] => clear H2
    end.

Ltac simpl_some :=
  repeat
    let T := fresh "T" in
    match goal with
    | [H: Some ?x = Some ?y |- _] =>
      assert(T: x = y) by (inversion H; reflexivity; assumption); clear H; rename T into H
    end.

Ltac bool_rel :=
  repeat match goal with
         | [ H: (?x >? ?y) = true |- _] =>
           rewrite Z.gtb_lt in H
         | [ H: (?x >? ?y) = false |- _] =>
           rewrite zgt_false_le in H
         | [ H: (?x >=? ?y) = true |- _] =>
           rewrite Z.geb_le in H
         | [ H: (?x >=? ?y) = false |- _] =>
           rewrite zge_false_lt in H
         | [ H: (?x <? ?y) = _ |- _] =>
           rewrite <- (Z.gtb_ltb y x) in H
         | [ H: (?x <=? ?y) = _ |- _] =>
           rewrite <- (Z.geb_leb y x) in H
         | [ H: (?x =? ?y) = true |- _] =>
           rewrite Z.eqb_eq in H
         | [ H: (?x =? ?y) = false |- _] =>
           rewrite zeq_false_ne in H
         | [ |- (?x >? ?y) = true ] =>
           rewrite Z.gtb_lt
         | [ |- (?x >? ?y) = false ] =>
           rewrite zgt_false_le
         | [ |- (?x >=? ?y) = true ] =>
           rewrite Z.geb_le
         | [ |- (?x >=? ?y) = false ] =>
           rewrite zge_false_lt
         | [ |- (?x <? ?y) = _ ] =>
           rewrite <- (Z.gtb_ltb y x)
         | [ |- (?x <=? ?y) = _ ] =>
           rewrite <- (Z.geb_leb y x)
         | [ |- (?x =? ?y) = true ] =>
           rewrite Z.eqb_eq
         | [ |- (?x =? ?y) = false ] =>
           rewrite zeq_false_ne
         end.

Ltac extract_if :=
  let H := fresh "Cond" in
  match goal with
  | [|- context [if ?c then _ else None ]] => assert(H: c=true)
  | [|- context [if ?c then None else _ ]] => assert(H: c=false)
  end.

Ltac destruct_if :=
  let H := fresh "Case" in
  match goal with
  | [|- context [if ?c then _ else _]] => destruct c eqn:H; simpl
  end.

Ltac destruct_zmap :=
  let H := fresh "Heq" in
  match goal with
  | |- context [?a @ (?m # ?b == ?c)] =>
    destruct (a =? b) eqn:H; bool_rel;
    [rewrite H; repeat rewrite ZMap.gss| repeat rewrite (ZMap.gso _ _ H)]
  end.

Ltac assert_gso :=
  let H := fresh "Hneq" in
  match goal with
  | |- context [?a @ (?m # ?b == ?c)] => assert(H: a <> b)
  end.

Ltac assert_gsoH H :=
  let H := fresh "Hneq" in
  match type of H with
  | context [?a @ (?m # ?b == ?c)] => assert(H: a <> b)
  end.

Ltac assert_gss :=
  let H := fresh "Hneq" in
  match goal with
  | |- context [?a @ (?m # ?b == ?c)] => assert(H: a = b)
  end.

Ltac assert_gssH H :=
  let H := fresh "Hneq" in
  match type of H with
  | context [?a @ (?m # ?b == ?c)] => assert(H: a = b)
  end.

Ltac srewrite :=
  (repeat
     let T := fresh "tmp" in
     match goal with
     | [H:?x = ?y |- _] => repeat rewrite H in *; assert(T: True -> x = y) by (intros; apply H); clear H; rename T into H
     end);
  (repeat
     let E := fresh "Eq" in
     match goal with
     | [H: True -> ?x = ?y |- _] => assert(E: x = y) by (apply H; constructor); clear H; rename E into H
     end).

Ltac simpl_hyp H :=
  let cond := fresh "C" in
  match type of H with
  | (if ?x then _ else None) = _ =>
    destruct (x) eqn:cond; contra
  | (match ?x with | Some _ => _ | None => None end) = _ =>
    destruct (x) eqn:cond; contra
  | (match ?x with | _ => _ end) = _ =>
    destruct (x) eqn:cond
  | _ => idtac
  end.

Ltac despec exp :=
  simpl in *; srewrite; contra;
  let Hcond := fresh "cond" in
  match exp with
  | (if ?cond then ?ex1 else ?ex2) =>
    destruct cond eqn:Hcond; [despec cond; inv Hcond; despec ex1|despec cond; inv Hcond; despec ex2]
  | (match ?cond with | _ => _ end) =>
    destruct cond eqn:Hcond; despec cond; inv Hcond
  | Some ?ex => despec ex
  | _ => idtac
  end.

Ltac destruct_spec Hspec :=
  repeat match type of Hspec with
         | ?exp = Some _ =>
           despec exp; contra
         end.

Ltac duplicate H :=
  let H' := fresh "D" in
  let X := type of H in
  assert (H': X) by apply H.


Ltac big_vcgen :=
  match goal with
  | [|- external_call _ _ _ _ _ _ _ _] => fail 1
  | [|- context [if true then _ else _]] => simpl
  | [|- context [if false then _ else _]] => simpl
  | [|- (PTree.set ?id (Vlong ?a) _) ! ?id = Some (Vlong ?b) ] =>
    replace a with b; [eapply PTree.gss|]
  | [|- (PTree.set ?id (Vint ?a) _) ! ?id = Some (Vint ?b) ] =>
    replace a with b; [eapply PTree.gss|]
  | [|- _] => vcgen
  end;
  match goal with
  | [|- external_call (EF_external ?id _) _ _ _ _ _ _ _] =>
    econstructor; simpl; split;
    [ match goal with
      | |- context [id ↦ ?sem] => instantiate ( 1 := sem ) ; reflexivity
      end
    | econstructor; esplit; repeat progress (split; simpleproof);
      econstructor || eapply extcall_generic_sem_intro';
      repeat match goal with
             | [|- GenSem.semof _ _ _ _ _] => try econstructor
             end
    ]
  | [|- _] => idtac
  end.

Ltac split_and :=
  repeat match goal with
         | [|- _ /\ _ ] => split
         | [|- _] => idtac
         end.

Ltac simpl_imply H :=
  match type of H with
  | ?a -> ?b =>
    let T := fresh "T" in assert(T: b) by (apply H; assumption); clear H; rename T into H
  end.

Ltac add_int H x :=
  rewrite <- (Int.unsigned_repr x) in H.

Ltac add_int64 H x :=
  rewrite <- (Int64.unsigned_repr x) in H.

Ltac add_int' x :=
  rewrite <- (Int.unsigned_repr x).

Ltac add_int64' x :=
  rewrite <- (Int64.unsigned_repr x).

Ltac rm_bind H :=
  unfold bind in H; unfold bind' in H; unfold bind64 in H; unfold bind64' in H.

Ltac rm_bind' :=
  unfold bind; unfold bind'; unfold bind64; unfold bind64'.

Ltac unfold_spec H :=
  match type of H with
  | ?x _ = _ => unfold x in H
  | ?x _ _ = _ => unfold x in H
  | ?x _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ _ _ = _ => unfold x in H
  end; rm_bind H.

Ltac destruct_con :=
  let Hc1 := fresh "Hcond" in
  let Hc2 := fresh "Hcond" in
  match goal with
  | [H: ?x && ?y = true |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; inversion H
  | [H: ?x && ?y = false |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; inversion H
  | [H: ?x || ?y = true |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold orb in H; inversion H
  | [H: ?x || ?y = false |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold orb in H; inversion H
  end.

Ltac destruct_con0 :=
  let Hc1 := fresh "Hcond" in
  let Hc2 := fresh "Hcond" in
  match goal with
  | [H: ?x && ?y = true |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; inversion H
  | [H: ?x && ?y = false |- _] => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; inversion H
  end.

Ltac simpl_bool_eq :=
  repeat match goal with
         | [H: context[?x =? ?x] |- _] =>
           replace (x =? x) with true in * by (symmetry; bool_rel; reflexivity)
         | [|- context[?x =? ?x]] =>
           replace (x =? x) with true in * by (symmetry; bool_rel; reflexivity)
         end.

Ltac bool_rel_all := repeat (destruct_con; contra); bool_rel.
Ltac bool_rel_all0 := repeat (destruct_con0; contra); bool_rel.

Ltac simpl_func Hspec :=
  autounfold in Hspec; repeat simpl_hyp Hspec; inv Hspec; repeat destruct_con; bool_rel; contra.

Ltac solve_code_proof Hspec code_body :=
  intros; subst; unfold_spec Hspec; simpl_func Hspec; unfold code_body.

Ltac get_loop_body :=
  let LoopCond := fresh "cond" in
  let LoopBody := fresh "body" in
  match goal with
  | [|- context [Swhile ?cond ?body]] =>
    remember cond as LoopCond; remember body as LoopBody
  end.

Ltac const_div :=
  match goal with
  | [|- context[18446744073709551615/1] ] => replace (18446744073709551615/1) with 18446744073709551615 by reflexivity
  | [|- context[18446744073709551615/2] ] => replace (18446744073709551615/2) with 9223372036854775807 by reflexivity
  | [|- context[18446744073709551615/4] ] => replace (18446744073709551615/4) with 4611686018427387903 by reflexivity
  | [|- context[18446744073709551615/8] ] => replace (18446744073709551615/8) with 2305843009213693951 by reflexivity
  | [|- context[18446744073709551615/16] ] => replace (18446744073709551615/16) with 1152921504606846975 by reflexivity
  | [|- context[18446744073709551615/32] ] => replace (18446744073709551615/32) with 576460752303423487 by reflexivity
  | [|- context[18446744073709551615/64] ] => replace (18446744073709551615/64) with 288230376151711743 by reflexivity
  | [|- context[18446744073709551615/128] ] => replace (18446744073709551615/128) with 144115188075855871 by reflexivity
  | [|- context[18446744073709551615/256] ] => replace (18446744073709551615/256) with 72057594037927935 by reflexivity
  | [|- context[18446744073709551615/512] ] => replace (18446744073709551615/512) with 36028797018963967 by reflexivity
  | [|- context[18446744073709551615/1024] ] => replace (18446744073709551615/1024) with 18014398509481983 by reflexivity
  | [|- context[18446744073709551615/2048] ] => replace (18446744073709551615/2048) with 9007199254740991 by reflexivity
  | [|- context[18446744073709551615/4096] ] => replace (18446744073709551615/4096) with 4503599627370495 by reflexivity
  | [|- context[18446744073709551615/8192] ] => replace (18446744073709551615/8192) with 2251799813685247 by reflexivity
  | [|- context[18446744073709551615/16384] ] => replace (18446744073709551615/16384) with 1125899906842623 by reflexivity
  | [|- context[18446744073709551615/32768] ] => replace (18446744073709551615/32768) with 562949953421311 by reflexivity
  | [|- context[18446744073709551615/65536] ] => replace (18446744073709551615/65536) with 281474976710655 by reflexivity
  | [|- context[9223372036854775807/1] ] => replace (9223372036854775807/1) with 9223372036854775807 by reflexivity
  | [|- context[9223372036854775807/2] ] => replace (9223372036854775807/2) with 4611686018427387903 by reflexivity
  | [|- context[9223372036854775807/4] ] => replace (9223372036854775807/4) with 2305843009213693951 by reflexivity
  | [|- context[9223372036854775807/8] ] => replace (9223372036854775807/8) with 1152921504606846975 by reflexivity
  | [|- context[9223372036854775807/16] ] => replace (9223372036854775807/16) with 576460752303423487 by reflexivity
  | [|- context[9223372036854775807/32] ] => replace (9223372036854775807/32) with 288230376151711743 by reflexivity
  | [|- context[9223372036854775807/64] ] => replace (9223372036854775807/64) with 144115188075855871 by reflexivity
  | [|- context[9223372036854775807/128] ] => replace (9223372036854775807/128) with 72057594037927935 by reflexivity
  | [|- context[9223372036854775807/256] ] => replace (9223372036854775807/256) with 36028797018963967 by reflexivity
  | [|- context[9223372036854775807/512] ] => replace (9223372036854775807/512) with 18014398509481983 by reflexivity
  | [|- context[9223372036854775807/1024] ] => replace (9223372036854775807/1024) with 9007199254740991 by reflexivity
  | [|- context[9223372036854775807/2048] ] => replace (9223372036854775807/2048) with 4503599627370495 by reflexivity
  | [|- context[9223372036854775807/4096] ] => replace (9223372036854775807/4096) with 2251799813685247 by reflexivity
  | [|- context[9223372036854775807/8192] ] => replace (9223372036854775807/8192) with 1125899906842623 by reflexivity
  | [|- context[9223372036854775807/16384] ] => replace (9223372036854775807/16384) with 562949953421311 by reflexivity
  | [|- context[9223372036854775807/32768] ] => replace (9223372036854775807/32768) with 281474976710655 by reflexivity
  | [|- context[9223372036854775807/65536] ] => replace (9223372036854775807/65536) with 140737488355327 by reflexivity
  | [|- context[4611686018427387903/1] ] => replace (4611686018427387903/1) with 4611686018427387903 by reflexivity
  | [|- context[4611686018427387903/2] ] => replace (4611686018427387903/2) with 2305843009213693951 by reflexivity
  | [|- context[4611686018427387903/4] ] => replace (4611686018427387903/4) with 1152921504606846975 by reflexivity
  | [|- context[4611686018427387903/8] ] => replace (4611686018427387903/8) with 576460752303423487 by reflexivity
  | [|- context[4611686018427387903/16] ] => replace (4611686018427387903/16) with 288230376151711743 by reflexivity
  | [|- context[4611686018427387903/32] ] => replace (4611686018427387903/32) with 144115188075855871 by reflexivity
  | [|- context[4611686018427387903/64] ] => replace (4611686018427387903/64) with 72057594037927935 by reflexivity
  | [|- context[4611686018427387903/128] ] => replace (4611686018427387903/128) with 36028797018963967 by reflexivity
  | [|- context[4611686018427387903/256] ] => replace (4611686018427387903/256) with 18014398509481983 by reflexivity
  | [|- context[4611686018427387903/512] ] => replace (4611686018427387903/512) with 9007199254740991 by reflexivity
  | [|- context[4611686018427387903/1024] ] => replace (4611686018427387903/1024) with 4503599627370495 by reflexivity
  | [|- context[4611686018427387903/2048] ] => replace (4611686018427387903/2048) with 2251799813685247 by reflexivity
  | [|- context[4611686018427387903/4096] ] => replace (4611686018427387903/4096) with 1125899906842623 by reflexivity
  | [|- context[4611686018427387903/8192] ] => replace (4611686018427387903/8192) with 562949953421311 by reflexivity
  | [|- context[4611686018427387903/16384] ] => replace (4611686018427387903/16384) with 281474976710655 by reflexivity
  | [|- context[4611686018427387903/32768] ] => replace (4611686018427387903/32768) with 140737488355327 by reflexivity
  | [|- context[4611686018427387903/65536] ] => replace (4611686018427387903/65536) with 70368744177663 by reflexivity
  | [|- context[2305843009213693951/1] ] => replace (2305843009213693951/1) with 2305843009213693951 by reflexivity
  | [|- context[2305843009213693951/2] ] => replace (2305843009213693951/2) with 1152921504606846975 by reflexivity
  | [|- context[2305843009213693951/4] ] => replace (2305843009213693951/4) with 576460752303423487 by reflexivity
  | [|- context[2305843009213693951/8] ] => replace (2305843009213693951/8) with 288230376151711743 by reflexivity
  | [|- context[2305843009213693951/16] ] => replace (2305843009213693951/16) with 144115188075855871 by reflexivity
  | [|- context[2305843009213693951/32] ] => replace (2305843009213693951/32) with 72057594037927935 by reflexivity
  | [|- context[2305843009213693951/64] ] => replace (2305843009213693951/64) with 36028797018963967 by reflexivity
  | [|- context[2305843009213693951/128] ] => replace (2305843009213693951/128) with 18014398509481983 by reflexivity
  | [|- context[2305843009213693951/256] ] => replace (2305843009213693951/256) with 9007199254740991 by reflexivity
  | [|- context[2305843009213693951/512] ] => replace (2305843009213693951/512) with 4503599627370495 by reflexivity
  | [|- context[2305843009213693951/1024] ] => replace (2305843009213693951/1024) with 2251799813685247 by reflexivity
  | [|- context[2305843009213693951/2048] ] => replace (2305843009213693951/2048) with 1125899906842623 by reflexivity
  | [|- context[2305843009213693951/4096] ] => replace (2305843009213693951/4096) with 562949953421311 by reflexivity
  | [|- context[2305843009213693951/8192] ] => replace (2305843009213693951/8192) with 281474976710655 by reflexivity
  | [|- context[2305843009213693951/16384] ] => replace (2305843009213693951/16384) with 140737488355327 by reflexivity
  | [|- context[2305843009213693951/32768] ] => replace (2305843009213693951/32768) with 70368744177663 by reflexivity
  | [|- context[2305843009213693951/65536] ] => replace (2305843009213693951/65536) with 35184372088831 by reflexivity
  | [|- context[4294967295/1] ] => replace (4294967295/1) with 4294967295 by reflexivity
  | [|- context[4294967295/2] ] => replace (4294967295/2) with 2147483647 by reflexivity
  | [|- context[4294967295/4] ] => replace (4294967295/4) with 1073741823 by reflexivity
  | [|- context[4294967295/8] ] => replace (4294967295/8) with 536870911 by reflexivity
  | [|- context[4294967295/16] ] => replace (4294967295/16) with 268435455 by reflexivity
  | [|- context[4294967295/32] ] => replace (4294967295/32) with 134217727 by reflexivity
  | [|- context[4294967295/64] ] => replace (4294967295/64) with 67108863 by reflexivity
  | [|- context[4294967295/128] ] => replace (4294967295/128) with 33554431 by reflexivity
  | [|- context[4294967295/256] ] => replace (4294967295/256) with 16777215 by reflexivity
  | [|- context[4294967295/512] ] => replace (4294967295/512) with 8388607 by reflexivity
  | [|- context[4294967295/1024] ] => replace (4294967295/1024) with 4194303 by reflexivity
  | [|- context[4294967295/2048] ] => replace (4294967295/2048) with 2097151 by reflexivity
  | [|- context[4294967295/4096] ] => replace (4294967295/4096) with 1048575 by reflexivity
  | [|- context[4294967295/8192] ] => replace (4294967295/8192) with 524287 by reflexivity
  | [|- context[4294967295/16384] ] => replace (4294967295/16384) with 262143 by reflexivity
  | [|- context[4294967295/32768] ] => replace (4294967295/32768) with 131071 by reflexivity
  | [|- context[4294967295/65536] ] => replace (4294967295/65536) with 65535 by reflexivity
  | [|- context[2147483647/1] ] => replace (2147483647/1) with 2147483647 by reflexivity
  | [|- context[2147483647/2] ] => replace (2147483647/2) with 1073741823 by reflexivity
  | [|- context[2147483647/4] ] => replace (2147483647/4) with 536870911 by reflexivity
  | [|- context[2147483647/8] ] => replace (2147483647/8) with 268435455 by reflexivity
  | [|- context[2147483647/16] ] => replace (2147483647/16) with 134217727 by reflexivity
  | [|- context[2147483647/32] ] => replace (2147483647/32) with 67108863 by reflexivity
  | [|- context[2147483647/64] ] => replace (2147483647/64) with 33554431 by reflexivity
  | [|- context[2147483647/128] ] => replace (2147483647/128) with 16777215 by reflexivity
  | [|- context[2147483647/256] ] => replace (2147483647/256) with 8388607 by reflexivity
  | [|- context[2147483647/512] ] => replace (2147483647/512) with 4194303 by reflexivity
  | [|- context[2147483647/1024] ] => replace (2147483647/1024) with 2097151 by reflexivity
  | [|- context[2147483647/2048] ] => replace (2147483647/2048) with 1048575 by reflexivity
  | [|- context[2147483647/4096] ] => replace (2147483647/4096) with 524287 by reflexivity
  | [|- context[2147483647/8192] ] => replace (2147483647/8192) with 262143 by reflexivity
  | [|- context[2147483647/16384] ] => replace (2147483647/16384) with 131071 by reflexivity
  | [|- context[2147483647/32768] ] => replace (2147483647/32768) with 65535 by reflexivity
  | [|- context[2147483647/65536] ] => replace (2147483647/65536) with 32767 by reflexivity
  | [|- context[1073741823/1] ] => replace (1073741823/1) with 1073741823 by reflexivity
  | [|- context[1073741823/2] ] => replace (1073741823/2) with 536870911 by reflexivity
  | [|- context[1073741823/4] ] => replace (1073741823/4) with 268435455 by reflexivity
  | [|- context[1073741823/8] ] => replace (1073741823/8) with 134217727 by reflexivity
  | [|- context[1073741823/16] ] => replace (1073741823/16) with 67108863 by reflexivity
  | [|- context[1073741823/32] ] => replace (1073741823/32) with 33554431 by reflexivity
  | [|- context[1073741823/64] ] => replace (1073741823/64) with 16777215 by reflexivity
  | [|- context[1073741823/128] ] => replace (1073741823/128) with 8388607 by reflexivity
  | [|- context[1073741823/256] ] => replace (1073741823/256) with 4194303 by reflexivity
  | [|- context[1073741823/512] ] => replace (1073741823/512) with 2097151 by reflexivity
  | [|- context[1073741823/1024] ] => replace (1073741823/1024) with 1048575 by reflexivity
  | [|- context[1073741823/2048] ] => replace (1073741823/2048) with 524287 by reflexivity
  | [|- context[1073741823/4096] ] => replace (1073741823/4096) with 262143 by reflexivity
  | [|- context[1073741823/8192] ] => replace (1073741823/8192) with 131071 by reflexivity
  | [|- context[1073741823/16384] ] => replace (1073741823/16384) with 65535 by reflexivity
  | [|- context[1073741823/32768] ] => replace (1073741823/32768) with 32767 by reflexivity
  | [|- context[1073741823/65536] ] => replace (1073741823/65536) with 16383 by reflexivity
  | [|- context[536870911/1] ] => replace (536870911/1) with 536870911 by reflexivity
  | [|- context[536870911/2] ] => replace (536870911/2) with 268435455 by reflexivity
  | [|- context[536870911/4] ] => replace (536870911/4) with 134217727 by reflexivity
  | [|- context[536870911/8] ] => replace (536870911/8) with 67108863 by reflexivity
  | [|- context[536870911/16] ] => replace (536870911/16) with 33554431 by reflexivity
  | [|- context[536870911/32] ] => replace (536870911/32) with 16777215 by reflexivity
  | [|- context[536870911/64] ] => replace (536870911/64) with 8388607 by reflexivity
  | [|- context[536870911/128] ] => replace (536870911/128) with 4194303 by reflexivity
  | [|- context[536870911/256] ] => replace (536870911/256) with 2097151 by reflexivity
  | [|- context[536870911/512] ] => replace (536870911/512) with 1048575 by reflexivity
  | [|- context[536870911/1024] ] => replace (536870911/1024) with 524287 by reflexivity
  | [|- context[536870911/2048] ] => replace (536870911/2048) with 262143 by reflexivity
  | [|- context[536870911/4096] ] => replace (536870911/4096) with 131071 by reflexivity
  | [|- context[536870911/8192] ] => replace (536870911/8192) with 65535 by reflexivity
  | [|- context[536870911/16384] ] => replace (536870911/16384) with 32767 by reflexivity
  | [|- context[536870911/32768] ] => replace (536870911/32768) with 16383 by reflexivity
  | [|- context[536870911/65536] ] => replace (536870911/65536) with 8191 by reflexivity
  | [|- _] => idtac
  end.

Ltac case_cond H :=
  let Hc1 := fresh "Hcond" in
  let Hc2 := fresh "Hcond" in
  match type of H with
  | (?x && ?y) = true => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; contra;
                         case_cond Hc1; case_cond Hc2
  | (?x && ?y) = false => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold andb in H; contra;
                          case_cond Hc1; case_cond Hc2
  | (?x || ?y) = true => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold orb in H; contra;
                         case_cond Hc1; case_cond Hc2
  | (?x || ?y) = false => destruct x eqn:Hc1; destruct y eqn:Hc2; unfold orb in H; contra;
                          case_cond Hc1; case_cond Hc2
  | _ => bool_rel; try omega
  end.

Ltac htrivial :=
  eexists; split; [reflexivity|constructor;reflexivity].

Ltac hsimpld adt :=
  eexists; split; [reflexivity|constructor;destruct adt; cbv; simpl in *; subst; reflexivity].

Ltac solve_refine_proof Hlow :=
  unfold Hlow; autounfold; intros Hspec Hrel; inv Hrel; unfold_spec Hspec; simpl_func Hspec.

Ltac simpl_not_halt :=
  repeat let D := fresh "D" in
         match goal with
         | [H: false = false -> ?x  |- _] =>
           pose proof H as D; clear H; assert(H: x) by (apply D; reflexivity); clear D;
           try (rewrite H in *; clear H)
         | [H: _ = halt _ |-_ ] => symmetry in H; try rewrite H in *
         end.

Ltac auto_rewrite0 :=
  match goal with
  | [H: ?x = true |- context[?x]] => rewrite H
  | [H: ?x = false |- context[?x]] => rewrite H
  | [H: true = ?x |- context[?x]] => rewrite <- H
  | [H: false = ?x |- context[?x]] => rewrite <- H
  | [H: ?f = _ |- context[match ?f with | _ => _  end]] =>
    rewrite H
  | [|-context[ZMap.get ?x (ZMap.set ?x _ _)]] => rewrite ZMap.gss
  end.

Ltac hstep :=
  let Hcond := fresh "Hcond" in
  match goal with
  | [H: ?f = _ |- context[match ?f with | _ => _  end]] =>
    rewrite H
  | [|- context[match ?f _ _ _ _ _ _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[match ?f _ _ _ _ _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[match ?f _ _ _ _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[match ?f _ _ _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[match ?f _ _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[match ?f _ with | Some _ => _ | None => None end]] =>
    unfold f; autounfold
  | [|- context[?f _ _ _ _ _ _ = Some _]] =>
    unfold f; autounfold
  | [|- context[?f _ _ _ _ _ = Some _]] =>
    unfold f; autounfold
  | [|- context[?f _ _ _ _ = Some _]] =>
    unfold f; autounfold
  | [|- context[?f _ _ _ = Some _]] =>
    unfold f; autounfold
  | [|- context[?f _ _ = Some _]] =>
    unfold f; autounfold
  | [|- context[?f _ = Some _]] =>
    unfold f; autounfold
  end.

Ltac solve_halt :=
  eexists; split; [reflexivity| constructor; simpl;
                                [constructor; simpl; repeat auto_rewrite0; try reflexivity;
                                 intro T; inversion T |
                                 repeat auto_rewrite0; intro T; inversion T |
                                 repeat auto_rewrite0; intro T; inversion T ]].

Ltac hsimpl_func Hspec :=
  unfold_spec Hspec; autounfold in Hspec; repeat simpl_hyp Hspec; contra; inv Hspec.

Ltac simpl_local :=
  repeat let Hn := fresh "Hlocal" in
         match goal with
         | [H: true = ?x |- _] => symmetry in H
         | [H: false = ?x |- _] => symmetry in H
         | [H: false = false -> ?x |- _] =>
           assert(Hn: x) by (apply H; reflexivity); clear H
         end.

Ltac simpl_case_no_se :=
  match goal with
  | [ |- context [_ + 0] ] => rewrite Z.add_0_r
  | [ |- context [0 + _] ] => rewrite Z.add_0_l
  | [ H: context [_ + 0] |- _ ] => rewrite Z.add_0_r in H
  | [ H: context [0 + _] |- _ ] => rewrite Z.add_0_l in H
  | [ |- context [_ - 0] ] => rewrite Z.sub_0_r
  | [ |- context [0 - _] ] => rewrite Z.sub_0_l
  | [ H: context [_ - 0] |- _ ] => rewrite Z.sub_0_r in H
  | [ H: context [0 - _] |- _ ] => rewrite Z.sub_0_l in H
  | [ |- context[Int.repr (-1)] ] => rewrite invalid_repr; unfold INVALID
  | [ H: context[Int.repr (-1)] |- _ ] => rewrite invalid_repr in H; unfold INVALID in H
  | [ |- context[Int64.repr (-1)] ] => rewrite invalid64_repr; unfold INVALID64
  | [ H: context[Int64.repr (-1)] |- _ ] => rewrite invalid64_repr in H; unfold INVALID64 in H
  | [ |- context [Int64.max_unsigned] ] => rewrite int64_max_unsigned
  | [ |- context [Int.max_unsigned] ] => rewrite int_max_unsigned
  | [ H: context [Int64.max_unsigned] |- _ ] => rewrite int64_max_unsigned in H
  | [ H: context [Int.max_unsigned] |- _ ] => rewrite int_max_unsigned in H
  | [ H: Int.unsigned _ = Int.unsigned _ |- _ ] => apply int_eq_Z in H; subst
  | [ H: Int64.unsigned _ = Int64.unsigned _ |- _ ] => apply int64_eq_Z in H; subst
  | [ |- context [Int64.unsigned (cast_int_long Unsigned ?x)]] => rewrite cast_u32_u64
  | [ |- context [Int64.cmpu _ _ _]] => unfold Int64.cmpu
  | [ |- context [Int64.ltu _ _]] => unfold Int64.ltu
  | [ |- context [Int64.eq _ _]] => unfold Int64.eq
  | [ |- context [Int64.and _ _]] => unfold Int64.and
  | [ |- context [Int64.or _ _]] => unfold Int64.or
  | [ |- context [Int64.add _ _]] => unfold Int64.add
  | [ |- context [Int64.sub _ _]] => unfold Int64.sub
  | [ |- context [Int64.mul _ _]] => unfold Int64.mul
  | [ |- context [Int64.divu _ _]] => unfold Int64.divu
  | [ |- context [Int64.shl _ _]] => unfold Int64.shl
  | [ |- context [Int64.shr _ _]] => unfold Int64.shr
  | [ |- context [Int.cmpu _ _ _]] => unfold Int.cmpu
  | [ |- context [Int.ltu _ _]] => unfold Int.ltu
  | [ |- context [Int.eq _ _]] => unfold Int.eq
  | [ |- context [Int.and _ _]] => unfold Int.and
  | [ |- context [Int.or _ _]] => unfold Int.or
  | [ |- context [Int.add _ _]] => unfold Int.add
  | [ |- context [Int.sub _ _]] => unfold Int.sub
  | [ |- context [Int.mul _ _]] => unfold Int.mul
  | [ |- context [Int.divu _ _]] => unfold Int.divu
  | [ |- context [Int.shl _ _]] => unfold Int.shl
  | [ |- context [Int.shr _ _]] => unfold Int.shr
  | [ H: context [Int64.unsigned (cast_int_long Unsigned ?x)] |- _ ] => rewrite cast_u32_u64 in H
  | [ H: context [Int64.cmpu _ _ _] |- _ ] => unfold Int64.cmpu in H
  | [ H: context [Int64.ltu _ _] |- _ ] => unfold Int64.ltu in H
  | [ H: context [Int64.eq _ _] |- _ ] => unfold Int64.eq in H
  | [ H: context [Int64.and _ _] |- _ ] => unfold Int64.and in H
  | [ H: context [Int64.or _ _] |- _ ] => unfold Int64.or in H
  | [ H: context [Int64.add _ _] |- _ ] => unfold Int64.add in H
  | [ H: context [Int64.sub _ _] |- _ ] => unfold Int64.sub in H
  | [ H: context [Int64.mul _ _] |- _ ] => unfold Int64.mul in H
  | [ H: context [Int64.divu _ _] |- _ ] => unfold Int64.divu in H
  | [ H: context [Int64.shl _ _] |- _ ] => unfold Int64.shl in H
  | [ H: context [Int64.shr _ _] |- _ ] => unfold Int64.shr in H
  | [ H: context [Int.cmpu _ _ _] |- _ ] => unfold Int.cmpu in H
  | [ H: context [Int.ltu _ _] |- _ ] => unfold Int.ltu in H
  | [ H: context [Int.eq _ _] |- _ ] => unfold Int.eq in H
  | [ H: context [Int.and _ _] |- _ ] => unfold Int.and in H
  | [ H: context [Int.or _ _] |- _ ] => unfold Int.or in H
  | [ H: context [Int.add _ _] |- _ ] => unfold Int.add in H
  | [ H: context [Int.sub _ _] |- _ ] => unfold Int.sub in H
  | [ H: context [Int.mul _ _] |- _ ] => unfold Int.mul in H
  | [ H: context [Int.divu _ _] |- _ ] => unfold Int.divu in H
  | [ H: context [Int.shl _ _] |- _ ] => unfold Int.shl in H
  | [ H: context [Int.shr _ _] |- _ ] => unfold Int.shr in H
  | [|- _ <= _ <= _] => split
  | [|- _ < _ <= _] => split
  | [|- _ <= _ < _] => split
  | [|- _ < _ < _] => split
  | [ |- 0 <= Int.unsigned _ ] => apply int_bound
  | [ |- Int.unsigned _ <= 4294967295 ] => apply int_bound
  | [ |- Int.unsigned _ <= 18446744073709551615 ] => apply int_bound64
  | [ |- 0 <= Int64.unsigned _ ] => apply int64_bound
  | [ |- Int64.unsigned _ <= 18446744073709551615 ] => apply int64_bound
  | [ |- context [Int64.repr (Int64.unsigned _)]] => rewrite Int64.repr_unsigned
  | [ |- context [Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
  | [ H: context [Int64.repr (Int64.unsigned _)] |- _ ] => rewrite Int64.repr_unsigned in H
  | [ H: context [Int.repr (Int.unsigned _)] |- _ ] => rewrite Int.repr_unsigned in H
  | _ => idtac
  end.

Ltac somega :=
  repeat simpl_case_no_se;
  repeat (try omega; match goal with
                     | [|- 0 <= _ + _] => apply add_ge0_if
                     | [|- 0 <= _ - _] => apply sub_ge0_if
                     | [|- 0 <= _ * _] => apply mul_ge0_if
                     | [|- 0 <= _ / _] => apply divu_ge0_if
                     | [|- 0 <= Z.land _ _] => apply land_ge0_if
                     | [|- 0 <= Z.lor _ _] => apply lor_ge0_if
                     | [|- 0 <= Z.shiftl _ _] => apply shiftl_ge0_if
                     | [|- 0 <= Z.shiftr _ _] => apply shiftr_ge0_if
                     | [|- _ + _ <= _ ] => apply add_leN_if; const_div
                     | [|- _ - _ <= _ ] => apply sub_leN_if
                     | [|- _ * _ <= _ ] => apply mul_leN_if; const_div
                     | [|- _ / _ <= _ ] => apply divu_leN_if
                     | [|- Z.land _ _ <= _] => apply land_leN_if
                     | [|- Z.lor _ _ <= _ ] => apply lor_leN_if
                     | [|- Z.shiftl _ _ <= _] => apply shiftl_leN_if
                     | [|- Z.shiftr _ _ <= _] => apply shiftr_leN_if
                     end).

Ltac sstep :=
  repeat simpl_case_no_se;
  match goal with
  | [ |- context [Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr
  | [ |- context [Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr
  | [ H: context [Int64.unsigned (Int64.repr _)] |- _ ] => rewrite Int64.unsigned_repr in H
  | [ H: context [Int.unsigned (Int.repr _)] |- _ ] => rewrite Int.unsigned_repr in H
  | [|- _ <= _] => repeat (try omega; match goal with
                     | [|- _ <= _ <= _] => split
                     | [ |- 0 <= Int.unsigned _ ] => apply int_bound
                     | [ |- Int.unsigned _ <= Int.max_unsigned ] => apply int_bound
                     | [ |- Int.unsigned _ <= Int64.max_unsigned ] => apply int_bound64
                     | [ |- 0 <= Int64.unsigned _ ] => apply int64_bound
                     | [ |- Int64.unsigned _ <= Int64.max_unsigned ] => apply int_bound
                     | [|- 0 <= _ + _] => apply add_ge0_if
                     | [|- 0 <= _ - _] => apply sub_ge0_if
                     | [|- 0 <= _ * _] => apply mul_ge0_if
                     | [|- 0 <= _ / _] => apply divu_ge0_if
                     | [|- 0 <= Z.land _ _] => apply land_ge0_if
                     | [|- 0 <= Z.lor _ _] => apply lor_ge0_if
                     | [|- 0 <= Z.shiftl _ _] => apply shiftl_ge0_if
                     | [|- 0 <= Z.shiftr _ _] => apply shiftr_ge0_if
                     | [|- _ + _ <= _ ] => apply add_leN_if; const_div
                     | [|- _ - _ <= _ ] => apply sub_leN_if
                     | [|- _ * _ <= _ ] => apply mul_leN_if; const_div
                     | [|- _ / _ <= _ ] => apply divu_leN_if
                     | [|- Z.land _ _ <= _] => apply land_leN_if
                     | [|- Z.lor _ _ <= _ ] => apply lor_leN_if
                     | [|- Z.shiftl _ _ <= _] => apply shiftl_leN_if
                     | [|- Z.shiftr _ _ <= _] => apply shiftr_leN_if
                     end)
  | [ H: ?x < ?y |- context [zlt ?x ?y] ] => destruct zlt; [|omega]
  | [ H: ?x >= ?y |- context [zlt ?x ?y] ] => destruct zlt; [omega|]
  | [ H: ?x > ?y |- context [zlt ?y ?x] ] => destruct zlt; [|omega]
  | [ H: ?x <= ?y |- context [zlt ?y ?x] ] => destruct zlt; [omega|]
  | [ H: ?x = ?y |- context [zeq ?x ?y] ] => destruct zeq; [|omega]
  | [ H: ?x = ?y |- context [zeq ?y ?x] ] => destruct zeq; [|omega]
  | [ H: ?x <> ?y |- context [zeq ?x ?y] ] => destruct zeq; [omega|]
  | [ H: ?x <> ?y |- context [zeq ?y ?x] ] => destruct zeq; [omega|]
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e ?g] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a ?b ?c ?d] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a ?b ?c ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a ?b ] ] => rewrite H; reflexivity
  | [ H: ?f ?a = Some (?x, VZ64 Int64.unsigned ?r) |- context [?f ?a] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (?x, Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e ?g ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e = Some (?x, Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d = Some (?x, Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c = Some (?x, Int.unsigned ?r) |- context [?f ?a ?b ?c ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b = Some (?x, Int.unsigned ?r) |- context [?f ?a ?b ] ] => rewrite H; reflexivity
  | [ H: ?f ?a = Some (?x, Int.unsigned ?r) |- context [?f ?a] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e ?g ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e = Some (Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ?e ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d = Some (Int.unsigned ?r) |- context [?f ?a ?b ?c ?d ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c = Some (Int.unsigned ?r) |- context [?f ?a ?b ?c ] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b = Some (Int.unsigned ?r) |- context [?f ?a ?b ] ] => rewrite H; reflexivity
  | [ H: ?f ?a = Some (Int.unsigned ?r) |- context [?f ?a] ] => rewrite H; reflexivity
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (?x, VZ64 ?r) |- context [?f ?a ?b ?c ?d ?e ?g ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e = Some (?x, VZ64 ?r) |- context [?f ?a ?b ?c ?d ?e ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d = Some (?x, VZ64 ?r) |- context [?f ?a ?b ?c ?d ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c = Some (?x, VZ64 ?r) |- context [?f ?a ?b ?c ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b = Some (?x, VZ64 ?r) |- context [?f ?a ?b ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a = Some (?x, VZ64 ?r) |- context [?f ?a] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (VZ64 ?r) |- context [?f ?a ?b ?c ?d ?e ?g ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e = Some (VZ64 ?r) |- context [?f ?a ?b ?c ?d ?e ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d = Some (VZ64 ?r) |- context [?f ?a ?b ?c ?d ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c = Some (VZ64 ?r) |- context [?f ?a ?b ?c ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b = Some (VZ64 ?r) |- context [?f ?a ?b ] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a = Some (VZ64 ?r) |- context [?f ?a] ] => add_int64 H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some (?x, ?r) |- context [?f ?a ?b ?c ?d ?e ?g ] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e = Some (?x, ?r) |- context [?f ?a ?b ?c ?d ?e ] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d = Some (?x, ?r) |- context [?f ?a ?b ?c ?d ] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c = Some (?x, ?r) |- context [?f ?a ?b ?c ] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b = Some (?x, ?r) |- context [?f ?a ?b ] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a = Some (?x, ?r) |- context [?f ?a] ] => add_int H r; [rewrite H; reflexivity|]
  | [ H: ?f ?a ?b ?c ?d ?e ?g = Some ?r |- context [?f ?a ?b ?c ?d ?e ?g ] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [ H: ?f ?a ?b ?c ?d ?e = Some ?r |- context [?f ?a ?b ?c ?d ?e ] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [ H: ?f ?a ?b ?c ?d = Some ?r |- context [?f ?a ?b ?c ?d ] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [ H: ?f ?a ?b ?c = Some ?r |- context [?f ?a ?b ?c ] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [ H: ?f ?a ?b = Some ?r |- context [?f ?a ?b ] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [ H: ?f ?a = Some ?r |- context [?f ?a] ] => (try add_int H r); (try (rewrite H; reflexivity))
  | [H: ?x = Int.unsigned ?y |- ?y = Int.repr ?x] => rewrite H
  | [H: ?x = Int64.unsigned ?y |- ?y = Int64.repr ?x] => rewrite H
  | _ => idtac
  end.

Ltac solve_proof_low := repeat (repeat sstep; try big_vcgen).

Ltac prename' pat H name :=
  match type of H with
  | context[?pat'] => unify pat pat'; rename H into name
  end.

Tactic Notation "prename" open_constr(pat) "into" ident(name) :=
  lazymatch goal with
  | H: pat, H': pat |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: pat |- _ => prename' pat H name
  | H: context[pat], H': context[pat] |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: context[pat] |- _ => prename' pat H name
  | _ => fail 0 "No hypothesis matching" pat
  end.
```
