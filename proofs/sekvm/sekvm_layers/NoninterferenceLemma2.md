# NoninterferenceLemma2

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import GenSem.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import RealParams.
Require Import GenSem.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import PrimSemantics.
Require Import CompatClightSem.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import RData.
Require Import Constants.
Require Import HighSpecs.
Require Import HypsecCommLib.

Local Open Scope Z.

Lemma map_host_conf:
  forall addr s1 s2 s1' s2' a1 b1 a2 b2
    (ex1: local_map_host addr s1 = (s1', false, a1, b1))
    (ex2: local_map_host addr s2 = (s2', false, a2, b2))
    (Haddr: valid_addr addr)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_map_host in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq0 in ex1.
  destruct (s2_owner (addr / PAGE_SIZE) @ (s2page s2) =? INVALID) eqn:Hinvalid; simpl in *.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2. bool_rel.
  pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  repeat rewrite ZMap.gss. rewrite Hn1, Hn2. intros.
  pose proof (npt_eq0 gfn). destruct_zmap.
  rewrite host_pte_pfn_dev. autounfold. rewrite owner_eq0. rewrite Hinvalid. reflexivity.
  assumption. assumption.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2. bool_rel.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C2) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  repeat rewrite ZMap.gss. rewrite Hn1, Hn2. intros.
  pose proof (npt_eq0 gfn). destruct_zmap.
  rewrite host_pte_pfn_mem. rewrite owner_eq0. reflexivity. assumption.
  assumption.
Qed.

Lemma clear_vm_page_conf:
  forall vmid pfn s1 s2 s1' s2' a1 b1 c1 a2 b2 c2
    (ex1: local_clear_vm_page vmid pfn s1 = (s1', false, a1, b1, c1))
    (ex2: local_clear_vm_page vmid pfn s2 = (s2', false, a2, b2, c2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_clear_vm_page in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq0 in ex1.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2; try assumption.
  assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
  { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
    inv C2. destruct inv1. pose proof (host_flatmap0 _ _ _ _ C0).
    destruct (zeq z0 0). srewrite. repeat eexists.
    apply H in n. destruct n. srewrite. pose proof (host_npt_cons0 _ _ _ _ C0) as T.
   replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C2). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
  { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
    inv C6. destruct inv2. pose proof (host_flatmap0 _ _ _ _ C4).
    destruct (zeq z3 0). srewrite. repeat eexists.
    apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons0 _ _ _ _ C4) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C6). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hne1: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n) = pfn0 @ (pt HOSTVISOR @ (npts s1))).
  { intros. destruct (z =? 0). inv C2. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C2). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
    assert(Hne2: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n0) = pfn0 @ (pt HOSTVISOR @ (npts s2))).
  { intros. destruct (z2 =? 0). inv C6. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C6). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
  destruct Hnp1 as (l1 & e1 & Hnp1).
  destruct Hnp2 as (l2 & e2 & Hnp2).
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq0 gfn). repeat rewrite ZMap.gss.
  destruct (gfn =? pfn) eqn:Hgfn; bool_rel; srewrite.
  assert_gso. red. intro T. rewrite <- T in C. destruct inv2. rewrite page_0_invalid0 in C. autounfold in *; omega.
  repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq0. reflexivity.
  rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq0 in H.
  assert(T1: z6 = 0 \/ z6 = gfn).
  destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
  destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
  assert(T2: z9 = 0 \/ z9 = gfn).
  destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
  destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
  destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq0; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  rewrite <- H. destruct_if; destruct_if; reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct_if; destruct_if; reflexivity.
  assumption.
  intros. destruct_zmap. simpl. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. reflexivity. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn0) as Hmem. destruct_zmap. simpl.
  reflexivity. assumption.
Qed.

Lemma assign_pfn_to_vm_conf:
  forall vmid gfn pfn dorc logn s1 s2 s1' s2' n1 n2 a1 b1 c1 a2 b2 c2
    (ex1: local_assign_pfn_to_vm vmid gfn pfn dorc logn s1 = (s1', false, n1, a1, b1, c1))
    (ex2: local_assign_pfn_to_vm vmid gfn pfn dorc logn s2 = (s2', false, n2, a2, b2, c2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2' /\ n1 = n2.
Proof.
  intros. unfold local_assign_pfn_to_vm in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_owner in *. simpl_bool_eq. rewrite owner_eq0 in ex1. unfold observe_count in *.
  simpl_hyp ex1. bool_rel.
  pose proof (count_eq0 pfn) as Hcount. rewrite owner_eq0 in Hcount; rewrite C in Hcount.
  replace (HOSTVISOR =? INVALID) with false in Hcount by reflexivity; simpl_bool_eq.
  rewrite Hcount in ex1. simpl_hyp ex1. autounfold in *; simpl_bool_eq.
  repeat simpl_hyp ex1; try solve [inv ex1].
  repeat simpl_hyp ex2; try solve [inv ex2].
  assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
  { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
    inv C3. destruct inv1. pose proof (host_flatmap0 _ _ _ _ C1).
    destruct (zeq z0 0). srewrite. repeat eexists.
    apply H in n. destruct n. srewrite. pose proof (host_npt_cons0 _ _ _ _ C1) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
  { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
    inv C7. destruct inv2. pose proof (host_flatmap0 _ _ _ _ C5).
    destruct (zeq z3 0). srewrite. repeat eexists.
    apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons0 _ _ _ _ C5) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C7). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hne1: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n) = pfn0 @ (pt HOSTVISOR @ (npts s1))).
  { intros. destruct (z =? 0). inv C3. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
    assert(Hne2: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n0) = pfn0 @ (pt HOSTVISOR @ (npts s2))).
  { intros. destruct (z2 =? 0). inv C7. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C7). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
  destruct Hnp1 as (l1 & e1 & Hnp1).
  destruct Hnp2 as (l2 & e2 & Hnp2).
  inv ex1; inv ex2; split; auto.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq0 gfn0). repeat rewrite ZMap.gss.
  destruct (gfn0 =? pfn) eqn:Hgfn; bool_rel; srewrite.
  assert_gso. red. intro T. rewrite <- T in C. destruct inv2. rewrite page_0_invalid0 in C. autounfold in *; omega.
  repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq0. reflexivity.
  rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
  destruct (gfn0 @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn0 @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq0 in H.
  assert(T1: z6 = 0 \/ z6 = gfn0).
  destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
  destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
  assert(T2: z9 = 0 \/ z9 = gfn0).
  destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
  destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
  destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq0; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  rewrite <- H. destruct_if; destruct_if; reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct_if; destruct_if; reflexivity. assumption.
  intros. destruct_zmap. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl.
  replace (vmid =? 4294967295) with false by (symmetry; bool_rel; omega).
  replace (vmid =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
  apply count_eq0.
  intros. destruct_zmap. reflexivity. apply gfn_eq0.
  intros. destruct_zmap. reflexivity. apply mem_eq0.
  inv ex1. autounfold in *; simpl_bool_eq. rewrite gfn_eq0 in ex1.
  simpl_hyp ex1. bool_rel_all0.
  pose proof (count_eq0 pfn) as Hcount. rewrite owner_eq0 in Hcount; rewrite Hcond in Hcount.
  rewrite zmap_set_id in ex1. rewrite zmap_set_id in ex2.
  simpl_hyp ex1; simpl_hyp ex2; inv ex1; inv ex2; split; try reflexivity;
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  inv ex1.
Qed.

Lemma map_pfn_vm_conf:
  forall vmid addr pte level s1 s2 s1' s2' a1 a2
    (ex1: local_map_pfn_vm vmid addr pte level s1 = (s1', false, a1))
    (ex2: local_map_pfn_vm vmid addr pte level s2 = (s2', false, a2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_map_pfn_vm in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1. repeat simpl_hyp ex2; inv ex2.
  destruct (level =? 2) eqn:Hlevel.
  simpl in *.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq0.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq0.
Qed.

Lemma map_io_conf:
  forall vmid gpa pa s1 s2 s1' s2' a1 b1 c1 a2 b2 c2
    (ex1: local_map_io vmid gpa pa s1 = (s1', false, a1, b1, c1))
    (ex2: local_map_io vmid gpa pa s2 = (s2', false, a2, b2, c2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_map_io in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq0 in ex1.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  simpl in *.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq0.
  assumption.
Qed.

Lemma grant_vm_page_conf:
  forall vmid pfn s1 s2 s1' s2' a1 a2
    (ex1: local_grant_vm_page vmid pfn s1 = (s1', a1))
    (ex2: local_grant_vm_page vmid pfn s2 = (s2', a2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_grant_vm_page in *; simpl in *; duplicate obseq; destruct D.
  autounfold in *.
  replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  pose proof (owner_eq0 pfn).
  destruct (s2_owner pfn @ (s2page s1) =? vmid) eqn:Howner1, (s2_owner pfn @ (s2page s2) =? vmid) eqn:Howner2; simpl in *; try omega.
  bool_rel. pose proof (count_eq0 pfn) as Hcount. pose proof (gfn_eq0 pfn) as Hgfn.
  rewrite Howner1, Howner2 in *; simpl_bool_eq.
  replace (vmid =? 4294967295) with false in * by (symmetry; bool_rel; omega). rewrite Hcount in *.
  destruct (s2_count pfn @ (s2page s2) <? 100) eqn:Hcnt.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
Qed.

Lemma revoke_vm_page_conf:
  forall vmid pfn dorc logn s1 s2 s1' s2' a1 b1 c1 a2 b2 c2 n1 n2
    (ex1: local_revoke_vm_page vmid pfn dorc logn s1 = (s1', false, n1, a1, b1, c1))
    (ex2: local_revoke_vm_page vmid pfn dorc logn s2 = (s2', false, n2, a2, b2, c2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_revoke_vm_page in *; simpl in *; duplicate obseq; destruct D.
  autounfold in *.
  replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  pose proof (owner_eq0 pfn).
  destruct (s2_owner pfn @ (s2page s1) =? vmid) eqn:Howner1, (s2_owner pfn @ (s2page s2) =? vmid) eqn:Howner2; simpl in *; try omega.
  bool_rel. pose proof (count_eq0 pfn) as Hcount. pose proof (gfn_eq0 pfn) as Hgfn.
  rewrite Howner1, Howner2 in *; simpl_bool_eq.
  replace (vmid =? 4294967295) with false in * by (symmetry; bool_rel; omega). rewrite Hcount in *.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  assert_gso. omega. repeat rewrite(ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  assumption. inv ex1; inv ex2; assumption.
Qed.

Lemma set_vcpu_active_conf:
  forall vmid vcpuid s1 s2 s1' s2' a1 a2
    (ex1: local_set_vcpu_active vmid vcpuid s1 = (s1', false, a1))
    (ex2: local_set_vcpu_active vmid vcpuid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_set_vcpu_active in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma set_vcpu_inactive_conf:
  forall vmid vcpuid s1 s2 s1' s2' a1 a2
    (ex1: local_set_vcpu_inactive vmid vcpuid s1 = (s1', false, a1))
    (ex2: local_set_vcpu_inactive vmid vcpuid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_set_vcpu_inactive in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
  intros. pose proof (state_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H.
  destruct_if. reflexivity. simpl_bool_eq.
  inv H. reflexivity. assumption.
Qed.

Lemma register_vcpu_conf:
  forall vmid vcpuid s1 s2 s1' s2' a1 a2
    (ex1: local_register_vcpu vmid vcpuid s1 = (s1', false, a1))
    (ex2: local_register_vcpu vmid vcpuid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_register_vcpu in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma gen_vmid_conf:
  forall s1 s2 s1' s2' a1 a2
    (ex1: local_gen_vmid s1 = (s1', false, a1))
    (ex2: local_gen_vmid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_gen_vmid in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  inv core_data_eq0. reflexivity.
Qed.

Lemma register_kvm_conf:
  forall vmid s1 s2 s1' s2' a1 a2
    (ex1: local_register_kvm vmid s1 = (s1', false, a1))
    (ex2: local_register_kvm vmid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_register_kvm in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma set_boot_info_conf:
  forall vmid load_addr size s1 s2 s1' s2' a1 b1 a2 b2
    (ex1: local_set_boot_info vmid load_addr size s1 = (s1', false, a1, b1))
    (ex2: local_set_boot_info vmid load_addr size s2 = (s2', false, a2, b2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_set_boot_info in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_boot_info in *; simpl_bool_eq. pose proof (boot_eq0 vmid) as Hboot; simpl_some.
  rewrite Hboot in ex1. repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; try assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. destruct_zmap. simpl; srewrite. inv core_data_eq0. reflexivity.
  apply boot_eq0. inv core_data_eq0. reflexivity.
Qed.

Lemma remap_vm_image_conf:
  forall vmid pfn load_idx s1 s2 s1' s2' a1 b1 a2 b2
    (ex1: local_remap_vm_image vmid pfn load_idx s1 = (s1', false, a1, b1))
    (ex2: local_remap_vm_image vmid pfn load_idx s2 = (s2', false, a2, b2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_remap_vm_image in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_boot_info in *; simpl_bool_eq. pose proof (boot_eq0 vmid) as Hboot; simpl_some.
  rewrite Hboot in ex1. repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; try assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq0.
  intros. destruct_zmap. simpl; srewrite. inv core_data_eq0. reflexivity.
  apply boot_eq0.
Qed.

Lemma smmu_assign_page_conf:
  forall cbndx index pfn gfn s1 s2 s1' s2' a1 b1 c1 d1 a2 b2 c2 d2
    (ex1: local_smmu_assign_page cbndx index pfn gfn s1 = (s1', false, a1, b1, c1, d1))
    (ex2: local_smmu_assign_page cbndx index pfn gfn s2 = (s2', false, a2, b2, c2, d2))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_smmu_assign_page in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq0 in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1; [|inv ex1; inv ex2; auto].
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq0 in ex1.
  simpl_hyp ex1.
  - repeat simpl_hyp ex1; try inv ex1. repeat simpl_hyp ex2; try inv ex2.
    assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
    { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
      inv C7. destruct inv1. pose proof (host_flatmap0 _ _ _ _ C5).
      destruct (zeq z0 0). srewrite. repeat eexists.
      apply H in n. destruct n. srewrite. pose proof (host_npt_cons0 _ _ _ _ C5) as T.
      replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
      srewrite. repeat eexists.
      pose proof (local_mmap_level3 _ _ _ _ _ C7). rewrite H.
      rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
      autounfold; omega. }
    assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
    { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
      inv C10. destruct inv2. pose proof (host_flatmap0 _ _ _ _ C8).
      destruct (zeq z3 0). srewrite. repeat eexists.
      apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons0 _ _ _ _ C8) as T.
      replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
      srewrite. repeat eexists.
      pose proof (local_mmap_level3 _ _ _ _ _ C10). rewrite H.
      rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
      autounfold; omega. }
    assert(Hne1: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n) = pfn0 @ (pt HOSTVISOR @ (npts s1))).
    { intros. destruct (z =? 0). inv C7. reflexivity.
      pose proof (local_mmap_level3 _ _ _ _ _ C7). rewrite H0.
      rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
      autounfold; omega. }
      assert(Hne2: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n0) = pfn0 @ (pt HOSTVISOR @ (npts s2))).
    { intros. destruct (z2 =? 0). inv C10. reflexivity.
      pose proof (local_mmap_level3 _ _ _ _ _ C10). rewrite H0.
      rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
      autounfold; omega. }
    destruct Hnp1 as (l1 & e1 & Hnp1).
    destruct Hnp2 as (l2 & e2 & Hnp2).
    constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
    intros. pose proof (npt_eq0 gfn0). repeat rewrite ZMap.gss.
    destruct (gfn0 =? pfn) eqn:Hgfn; bool_rel; srewrite.
    assert_gso. red. intro T. rewrite <- T in C3. destruct inv2. rewrite page_0_invalid0 in C3. autounfold in *; omega.
    repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq0. reflexivity.
    rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
    destruct (gfn0 @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
    destruct (gfn0 @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
    rewrite owner_eq0 in H.
    assert(T1: z6 = 0 \/ z6 = gfn0).
    destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
    destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
    assert(T2: z9 = 0 \/ z9 = gfn0).
    destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
    destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
    destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq0; try reflexivity.
    destruct T1, T2; try omega; srewrite; try reflexivity.
    rewrite <- H. destruct_if; destruct_if; reflexivity.
    destruct T1, T2; try omega; srewrite; try reflexivity.
    destruct_if; destruct_if; reflexivity.
    assumption.
    intros. destruct_zmap. simpl. reflexivity. apply owner_eq0.
    intros. destruct_zmap. simpl. reflexivity. apply count_eq0.
    intros. destruct_zmap. simpl. reflexivity. apply gfn_eq0.
    intros. pose proof (mem_eq0 pfn0) as Hmem. destruct_zmap. simpl.
    rewrite owner_eq0 in Hmem. srewrite; simpl_bool_eq. rewrite Hmem. reflexivity. assumption.
  - simpl_hyp ex1; inv ex1; inv ex2; try assumption.
Qed.

Lemma smmu_map_page_conf:
  forall cbndx index iova pte s1 s2 s1' s2' a1 b1 c1 d1 a2 b2 c2 d2
    (ex1: local_smmu_map_page cbndx index iova pte s1 = (s1', false, a1, b1, c1, d1))
    (ex2: local_smmu_map_page cbndx index iova pte s2 = (s2', false, a2, b2, c2, d2))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_smmu_map_page in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq0 in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  simpl_hyp ex1; [|inv ex1]. simpl_hyp ex2; [|inv ex2].
  simpl_hyp ex1. destruct b. inv ex1.
  simpl_hyp ex2. destruct b. inv ex2.
  remember (phys_page pte / PAGE_SIZE) as pfn; symmetry in Heqpfn.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq0 in ex1.
  destruct (s2_owner pfn @ (s2page s2) =? HOSTVISOR) eqn:Howner; simpl in *.
  bool_rel. pose proof (count_eq0 pfn) as Hcount. autounfold in Hcount.
  rewrite owner_eq0, Howner in Hcount.
  autounfold in Hcount. replace (0 =? 4294967295) with false in Hcount by reflexivity.
  simpl_bool_eq. rewrite Hcount in ex1.
  destruct (s2_count pfn @ (s2page s2) <? EL2_SMMU_CFG_SIZE).
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq0 gfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  assert(T1: z0 = 0 \/ z0 = gfn).
  destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
  destruct (zeq z0 0). auto. apply H0 in n. right. symmetry. apply n.
  assert(T2: z3 = 0 \/ z3 = gfn).
  destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
  destruct (zeq z3 0). auto. apply H0 in n. right. symmetry. apply n.
  destruct_zmap. simpl. destruct_zmap. simpl. rewrite owner_eq0. reflexivity.
  simpl_bool_eq. destruct T1, T2; try omega. srewrite.
  destruct inv2. rewrite page_0_invalid0 in Howner. autounfold in Howner; omega.
  srewrite. reflexivity.
  destruct_zmap. simpl. destruct T1, T2; try omega. srewrite. reflexivity.
  srewrite. reflexivity. assumption.
  intros. destruct_zmap. simpl. apply owner_eq0. apply owner_eq0.
  intros. destruct_zmap. simpl. rewrite owner_eq0. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. apply gfn_eq0. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn) as Hmem. srewrite.
  destruct_zmap. simpl. rewrite Heq in Hmem. assumption. assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq0; assumption.
  apply spt_eq0; assumption.
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq0; assumption.
  apply spt_eq0; assumption.
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq0; assumption.
  apply spt_eq0; assumption.
Qed.

Lemma smmu_clear_conf:
  forall iova cbndx index s1 s2 s1' s2' a1 b1 c1 d1 a2 b2 c2 d2
    (ex1: local_smmu_clear iova cbndx index s1 = (s1', false, a1, b1, c1, d1))
    (ex2: local_smmu_clear iova cbndx index s2 = (s2', false, a2, b2, c2, d2))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_smmu_clear in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq0 in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  unfold observe_spt in spt_eq0; simpl_bool_eq. rewrite spt_eq0 in ex1; try assumption.
  simpl_hyp ex1. destruct (z0 =? 0) eqn:Hz0.
  unfold observe_owner, observe_count in *; simpl_bool_eq.
  rewrite owner_eq0 in ex1.
  destruct (s2_owner (phys_page z0 / PAGE_SIZE) @ (s2page s2) =? HOSTVISOR) eqn: Howner.
  bool_rel; srewrite. replace (phys_page 0 / PAGE_SIZE) with 0 in Howner by reflexivity.
  destruct inv2. rewrite page_0_invalid0 in Howner. autounfold in Howner; omega.
  simpl in *. inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  simpl_hyp ex1; simpl_hyp ex2. simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C3) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn2.
  unfold observe_owner, observe_count in *; simpl_bool_eq.
  rewrite owner_eq0 in ex1.
  destruct (s2_owner (phys_page z0 / PAGE_SIZE) @ (s2page s2) =? HOSTVISOR) eqn: Howner.
  bool_rel. pose proof (count_eq0 (phys_page z0 / PAGE_SIZE)) as Hcount.
  rewrite owner_eq0, Howner in Hcount.
  replace (HOSTVISOR =? INVALID) with false in Hcount by reflexivity. simpl_bool_eq.
  rewrite Hcount in ex1. simpl in *.
  destruct (s2_count (phys_page z0 / PAGE_SIZE) @ (s2page s2) >? 0) eqn:Hc.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq0 gfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq0 in H.
  assert(T1: z2 = 0 \/ z2 = gfn).
  destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
  destruct (zeq z2 0). auto. apply H0 in n. right. symmetry. apply n.
  assert(T2: z5 = 0 \/ z5 = gfn).
  destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
  destruct (zeq z5 0). auto. apply H0 in n. right. symmetry. apply n.
  destruct_zmap; destruct_zmap; simpl; rewrite owner_eq0. reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  assumption.
  intros. destruct_zmap. simpl. apply owner_eq0. apply owner_eq0.
  intros. destruct_zmap. simpl. rewrite owner_eq0. reflexivity. apply count_eq0.
  intros. destruct_zmap. simpl. apply gfn_eq0. apply gfn_eq0.
  intros. pose proof (mem_eq0 pfn) as Hmem. srewrite.
  replace z with (phys_page z0 / 4096) in *.
  destruct_zmap. simpl. rewrite Heq in Hmem. assumption. assumption.
  destruct inv2. symmetry. eapply spt_cons0; try eassumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq0 gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq0 gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq0 gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
Qed.

Lemma free_smmu_pgd_conf:
  forall cbndx index s1 s2 s1' s2' a1 b1 a2 b2
    (ex1: local_free_smmu_pgd cbndx index s1 = (s1', false, a1, b1))
    (ex2: local_free_smmu_pgd cbndx index s2 = (s2', false, a2, b2))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_free_smmu_pgd in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq0 in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1; [|inv ex1]. simpl_hyp ex2; [|inv ex2].
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (smmu_eq0 cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
Qed.

Lemma alloc_smmu_pgd_conf:
  forall cbndx vmid index num s1 s2 s1' s2' a1 b1 c1 a2 b2 c2
    (ex1: local_alloc_smmu_pgd cbndx vmid index num s1 = (s1', false, a1, b1, c1))
    (ex2: local_alloc_smmu_pgd cbndx vmid index num s2 = (s2', false, a2, b2, c2))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_alloc_smmu_pgd in *; simpl in *; duplicate obseq; destruct D.
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq0 in ex1; try assumption.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (smmu_eq0 cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
  intros. pose proof (spt_eq0 gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
Qed.

Lemma set_vm_poweroff_conf:
  forall vmid s1 s2 s1' s2' a1 a2
    (ex1: local_set_vm_poweroff vmid s1 = (s1', a1))
    (ex2: local_set_vm_poweroff vmid s2 = (s2', a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_set_vm_poweroff in *; simpl in *; autounfold in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0). destruct_if.
  destruct_zmap. inv H. destruct (0 @ (vminfos s1)). destruct (0 @ (vminfos s2)).
  simpl in H1. simpl. rewrite H1. reflexivity. assumption.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
  intros. pose proof (state_eq0 vmid0). destruct_if. reflexivity.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
Qed.

Lemma verify_vm_conf:
  forall vmid s1 s2 s1' s2' a1 a2
    (ex1: local_verify_vm vmid s1 = (s1', false, a1))
    (ex2: local_verify_vm vmid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_verify_vm in *; simpl in *; autounfold in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq0 vmid0). destruct_if.
  destruct_zmap. inv H. destruct (0 @ (vminfos s1)). destruct (0 @ (vminfos s2)).
  simpl in H1. simpl. rewrite H1. reflexivity. assumption.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
  intros. pose proof (state_eq0 vmid0). destruct_if. reflexivity.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
Qed.

Lemma load_encrypted_vcpu_conf:
  forall vmid vcpuid cregs cstates dorc logn s1 s2 s1' s2' cr1 cs1 cr2 cs2 n1 n2 a1 a2
    (ex1: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s1 = (s1', false, cr1, cs1, n1, a1))
    (ex2: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s2 = (s2', false, cr2, cs2, n2, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2' /\ cr1 = cr2 /\ cs1 = cs2 /\ n1 = n2.
Proof.
  intros. unfold local_load_encryted_vcpu in *; simpl in *; autounfold in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  split_and; try reflexivity.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. destruct_zmap. pose proof (boot_eq0 vmid). inv H.
  destruct (vmid @ (vminfos s1)), (vmid @ (vminfos s2)). simpl in *. rewrite H1. reflexivity.
  apply boot_eq0.
Qed.

Lemma load_save_encrypt_buf_conf:
  forall vmid inbuf outbuf dorc logn s1 s1' n1' a1 b1 s2 s2' n2' a2 b2
    (ex1: local_save_encrypt_buf vmid inbuf outbuf dorc logn s1 = (s1', false, n1', a1, b1))
    (ex2: local_save_encrypt_buf vmid inbuf outbuf dorc logn s2 = (s2', false, n2', a2, b2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2' /\ n1' = n2'.
Proof.
  intros. unfold local_save_encrypt_buf in *; simpl in *; autounfold in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  split_and; try reflexivity.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. destruct_zmap. rewrite owner_eq0. reflexivity. apply mem_eq0.
Qed.

Lemma load_load_decrypt_buf_conf:
  forall vmid inbuf dorc logn s1 s1' n1' a1 b1 c1 d1 s2 s2' n2' a2 b2 c2 d2
    (ex1: local_load_decrypt_buf vmid inbuf dorc logn s1 = (s1', false, n1', a1, b1, c1, d1))
    (ex2: local_load_decrypt_buf vmid inbuf dorc logn s2 = (s2', false, n2', a2, b2, c2, d2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2' /\ n1' = n2'.
Proof.
  intros. unfold local_load_decrypt_buf in *; simpl in *; autounfold in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  split_and; try reflexivity.
  remember (inbuf / 4096) as pfn. symmetry in Heqpfn.
  assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
  { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
    inv C3. destruct inv1. pose proof (host_flatmap0 _ _ _ _ C1).
    destruct (zeq z0 0). srewrite. repeat eexists.
    apply H in n. destruct n. srewrite. pose proof (host_npt_cons0 _ _ _ _ C1) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
  { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
    inv C9. destruct inv2. pose proof (host_flatmap0 _ _ _ _ C7).
    destruct (zeq z3 0). srewrite. repeat eexists.
    apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons0 _ _ _ _ C7) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C9). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hne1: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n) = pfn0 @ (pt HOSTVISOR @ (npts s1))).
  { intros. destruct (z =? 0). inv C3. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
    assert(Hne2: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n0) = pfn0 @ (pt HOSTVISOR @ (npts s2))).
  { intros. destruct (z2 =? 0). inv C9. reflexivity.
    pose proof (local_mmap_level3 _ _ _ _ _ C9). rewrite H0.
    rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
    autounfold; omega. }
  destruct Hnp1 as (l1 & e1 & Hnp1).
  destruct Hnp2 as (l2 & e2 & Hnp2).
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq0 gfn). repeat rewrite ZMap.gss.
  destruct (gfn =? pfn) eqn:Hgfn; bool_rel_all; srewrite.
  assert_gso. red. intro T. rewrite <- T in C1. destruct inv1. rewrite page_0_invalid0 in C1. autounfold in *; omega.
  repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq0. reflexivity.
  rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq0 in H.
  assert(T1: z6 = 0 \/ z6 = gfn).
  destruct inv1. pose proof (host_flatmap0 _ _ _ _ Hpt1).
  destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
  assert(T2: z9 = 0 \/ z9 = gfn).
  destruct inv2. pose proof (host_flatmap0 _ _ _ _ Hpt2).
  destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
  destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq0; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  rewrite <- H. destruct_if; destruct_if; reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct_if; destruct_if; reflexivity. assumption.
  intros. destruct_zmap. reflexivity. apply owner_eq0.
  intros. destruct_zmap. simpl. reflexivity. apply count_eq0.
  intros. destruct_zmap. reflexivity. apply gfn_eq0.
  intros. destruct_zmap. reflexivity. apply mem_eq0.
Qed.

Lemma prep_exit_conf:
  forall vmid d1 d2 d1' d2'
    (ex1: prep_exit_vm d1 = Some d1')
    (ex2: prep_exit_vm d2 = Some d2')
    (is_vm: HOSTVISOR < vmid < COREVISOR)
    (act1: cur_vmid d1 = vmid)
    (act2: cur_vmid d2 = vmid)
    (ic1: icore d1 = true)
    (ic2: icore d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (regs_eq: ctxt_regs (regs d1) = ctxt_regs (regs d2))
    (obseq: obs_eq vmid d1 d2),
    obs_eq vmid d1' d2' /\ cur_vmid d1' = vmid /\ cur_vmid d2' = vmid /\ cur_vcpuid d1' = cur_vcpuid d1.
Proof.
  Local Opaque query_oracle local_set_vcpu_inactive local_set_vm_poweroff.
  intros. unfold_spec ex1; unfold_spec ex2.
  simpl_hyp ex1. simpl_hyp ex2.
  match type of C with context[ec ?ctxt] => remember ctxt as cregs1 end.
  match type of C0 with context[ec ?ctxt] => remember ctxt as cregs2 end.
  symmetry in Heqcregs1, Heqcregs2. autounfold in *.
  assert(N0: vmid =? 0 = false) by (bool_rel; omega).
  duplicate obseq. destruct D. autounfold in *. srewrite; simpl_bool_eq; simpl in *; simpl_some. clear_hyp.
  assert(valid_vcpu1: valid_vcpu (cur_vcpuid d1)) by (destruct inv1; assumption).
  assert(valid_vcpu2: valid_vcpu (cur_vcpuid d2)) by (destruct inv2; assumption).
  pose proof (shadow_ctxt_eq0 _ valid_vcpu2) as shadow_eq0. repeat srewrite.
  assert(Hind: obs_eq vmid r r0 /\ cur_vmid r = vmid /\ cur_vmid r0 = vmid /\ cur_vcpuid r = cur_vcpuid r0 /\ cur_vcpuid r0 = cur_vcpuid d2 /\
               shared_inv (shared r) /\ shared_inv (shared r0)).
  { simpl_hyp C. simpl_hyp C. inv C; inv C0.
    simpl in *. split_and; try assumption; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    destruct inv1; assumption. destruct inv2; assumption.
    simpl_hyp C. unfold prep_hvc_spec_h in *. autounfold in *; simpl in *.
    repeat rewrite ZMap.gss in *; simpl in *.
    repeat simpl_hyp C; repeat simpl_hyp C0.
    extract_adt C6 d10'. extract_adt C8 d20'.
    assert(indisting vmid d10' d20').
    eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    apply indisting_obs_eq in H. split_and. symmetry in Heqd20', Heqd10'. duplicate H.
    destruct D; autounfold in *; srewrite; simpl_bool_eq; simpl in *; simpl_some. clear_hyp.
    rewrite <- C, <- C0.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    eapply (set_vm_poweroff_conf _ _ _ _ _ _ _ C6 C8).
    rewrite <- Heqd10'. apply oracle_inv. simpl. destruct inv1. assumption.
    rewrite <- Heqd20'. apply oracle_inv. simpl. destruct inv2. assumption.
    destruct H; assumption.
    Local Transparent query_oracle.
    inv C. reflexivity. inv C0; simpl. assumption. inv C; inv C0. simpl; assumption. inv C0; reflexivity.
    inv C. simpl. apply (set_vm_poweroff_inv _ _ _ _ C6). apply oracle_inv. simpl. destruct inv1; assumption.
    inv C0. simpl. apply (set_vm_poweroff_inv _ _ _ _ C8). apply oracle_inv. simpl. destruct inv2; assumption.
    rewrite Heqd10'; autounfold; simpl. rewrite act1, orb_comm; simpl_bool_eq; reflexivity.
    rewrite Heqd20'; autounfold; simpl. rewrite act2, orb_comm; simpl_bool_eq; reflexivity.
    split_and. inv C; inv C0.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    inv C; reflexivity. inv C0; simpl; assumption. inv C; inv C0; simpl; assumption. inv C0; reflexivity.
    repeat simpl_hyp C; inv C; inv C0; simpl in *; srewrite; destruct inv1; assumption.
    inv C0; simpl; destruct inv2; assumption.
    repeat simpl_hyp C; inv C; repeat simpl_hyp C0; inv C0. simpl in *.
    split_and; srewrite; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    rewrite <- act2. repeat rewrite ZMap.gss. reflexivity. inv ex2. inversion halt2'.
    destruct inv1; assumption. destruct inv2; assumption.
    simpl in *. inv ex1. inv halt1'.
    repeat simpl_hyp C; inv C; inv C0; simpl in *; srewrite.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    destruct inv1; assumption. destruct inv2; assumption. }
  destruct Hind as (Hind & cur1 & cur2 & vc1 & vc2 & inv1' & inv2').
  simpl_hyp ex1. inv ex1; contra.
  simpl_hyp ex2. inv ex2; contra. clear C C0.
  repeat simpl_hyp ex1; inv ex1. repeat simpl_hyp ex2; inv ex2.
  extract_adt C d10'. extract_adt C0 d20'.
  assert(indisting (cur_vmid d1) d10' d20').
  eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
  assumption. apply indisting_obs_eq in H.
  destruct H; autounfold in *; srewrite; simpl_bool_eq; simpl in *; simpl_some. clear_hyp.
  srewrite. split_and; try reflexivity.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  eapply (set_vcpu_inactive_conf _ _ _ _ _ _ _ _ C C0). rewrite <- curid_eq1. apply oracle_inv.
  assumption. apply oracle_inv. assumption. assumption.
  autounfold. srewrite. simpl. rewrite cur1; simpl_bool_eq; reflexivity.
  autounfold. srewrite. simpl. rewrite cur2; simpl_bool_eq; reflexivity.
Qed.

Lemma host_vcpu_run_confidentiality:
  forall vmid d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: host_vcpu_run_handler_spec d1 = Some d1')
    (ex2: host_vcpu_run_handler_spec d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  Local Opaque prot_and_map_vm_s2pt_spec_h.
  intros. unfold_spec ex1; unfold_spec ex2.
  repeat simpl_hyp ex1; contra; try solve[simpl_some; rewrite <- ex1 in halt1'; inversion halt1'; contra].
  repeat simpl_hyp ex2; contra; try solve[simpl_some; rewrite <- ex2 in halt2'; inversion halt2'; contra].
  clear_hyp.
  assert(cur_host1: cur_vmid d1 = HOSTVISOR).
  { destruct inv1. apply valid_host_vmid0; assumption. }
  assert(cur_host2: cur_vmid d2 = HOSTVISOR).
  { destruct inv2. apply valid_host_vmid0; assumption. }
  assert(is_host: vmid = HOSTVISOR).
  { unfold active in act1. rewrite cur_host1 in act1. bool_rel_all; auto. }
  rewrite is_host in *. clear is_host vmid.
  remember (vcpu_run_swith_to_core d1) as d1a.
  remember (vcpu_run_swith_to_core d2) as d2a.
  rename r into d1b. rename r0 into d2b.
  symmetry in Heqd1a, Heqd2a.
  assert(ind1: obs_eq HOSTVISOR d1a d2a /\ icore d1a = true /\ icore d2a = true /\
               exists vmid, cur_vmid d1a = vmid /\ cur_vmid d2a = vmid /\ valid_vm vmid /\
                       shared_inv (shared d1a) /\ shared_inv (shared d2a)).
  { unfold vcpu_run_swith_to_core in *.
    repeat simpl_hyp Heqd1a. repeat simpl_hyp Heqd2a. simpl in *.
    apply indisting_obs_eq in obseq; try assumption.
    duplicate obseq. destruct D. autounfold in *.
    pose proof (core_data_log_eq0 0) as core_log_eq0.
    assert(vc0: valid_vcpu (cur_vcpuid d2)).
    { destruct inv2. assumption. }
    pose proof (shadow_ctxt_eq0 _ vc0) as shadow_eq0.
    srewrite; simpl_some; simpl_bool_eq; simpl in *. simpl_some. srewrite. srewrite.
    rewrite <- Heqd1a, <- Heqd2a. clear Heqd1a Heqd2a. simpl.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0; assumption.
    intros. assert_gso. autounfold in *; omega. repeat rewrite (ZMap.gso _ _ Hneq).
    apply dirty_eq0; assumption.
    eexists. bool_rel_all0; split_and; try reflexivity; try omega.
    destruct inv1; assumption. destruct inv2; assumption.
    rewrite <- Heqd2a in *. simpl in *. contra.
    rewrite <- Heqd1a in *. simpl in *. contra. }
  destruct ind1 as (ind1 & ic1 & ic2 & vmid & cur1 & cur2 & vmid_valid & inv1' & inv2').
  assert(ind2: obs_eq HOSTVISOR d1b d2b /\ shared_inv (shared d1b) /\ shared_inv (shared d2b)).
  { duplicate ind1; destruct D; autounfold in *.
    pose proof (core_data_log_eq0 vmid) as core_log_eq0.
    srewrite; simpl_some; simpl_bool_eq; simpl in *. simpl_some. srewrite. srewrite.
    rename C3 into Heqd1b. rename C9 into Heqd2b.
    unfold_spec Heqd1b. unfold_spec Heqd2b. srewrite. srewrite. simpl_hyp Heqd1b.
    match type of C3 with
    | is_vcpu ?v = true => remember v as vcpuid; clear Heqvcpuid
    end.
    assert(T: valid_vcpu vcpuid) by (autounfold in *; bool_rel_all0; split; assumption).
    simpl_hyp Heqd1b. simpl_hyp Heqd1b. destruct b. inv Heqd1b. inversion C4.
    simpl_hyp Heqd2b. simpl_hyp Heqd2b. destruct b. inv Heqd2b. inversion C10.
    extract_adt C9 d1a1. extract_adt C12 d2a1.
    assert(ih11: ihost d1a1 = true).
    { rewrite Heqd1a1; rewrite <- Heqd1a; simpl.
      unfold vcpu_run_swith_to_core. simpl. destruct_if; assumption. }
    assert(ih21: ihost d2a1 = true).
    { rewrite Heqd2a1; rewrite <- Heqd2a; simpl.
      unfold vcpu_run_swith_to_core. simpl. destruct_if; assumption. }
    assert(Hind2: obs_eq HOSTVISOR d1a1 d2a1 /\ cur_vmid d1a1 = vmid /\ cur_vmid d2a1 = vmid /\
                  icore d1a1 = true /\ icore d2a1 = true  /\ shared_inv (shared d1a1) /\ shared_inv (shared d2a1)).
    { clear Heqd1b Heqd2b.
      assert(cur_vmid d1a1 = vmid).
      { rewrite Heqd1a1; autounfold; simpl; assumption. }
      assert(cur_vmid d2a1 = vmid).
      { rewrite Heqd2a1; autounfold; simpl; assumption. }
      assert(indisting HOSTVISOR d1a1 d2a1).
      { eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
        constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
        simpl. intros. repeat rewrite ZMap.gss.
        destruct_zmap. reflexivity. apply core_data_log_eq0. }
      apply indisting_obs_eq in H1.
      split_and; try assumption.
      rewrite Heqd1a1; simpl; assumption.
      rewrite Heqd2a1; simpl; assumption.
      rewrite Heqd1a1; simpl. apply oracle_inv. assumption.
      rewrite Heqd2a1; simpl. apply oracle_inv. assumption.
      autounfold; rewrite ih11; simpl_bool_eq; reflexivity.
      autounfold; rewrite ih21; simpl_bool_eq; reflexivity. }
    destruct Hind2 as (Hind2 & cur11 & cur21 & ic11 & ic21 & inv11 & inv21).
    duplicate Hind2. destruct D. autounfold in *.
    symmetry in Heqd1a1, Heqd2a1.
    srewrite. pose proof (core_data_log_eq1 vmid) as core_data_eq2.
    Local Opaque query_oracle.
    simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
    pose proof (shadow_ctxt_eq1 vcpuid T) as shadow_eq1.
    pose proof (dirty_eq1 vmid vcpuid vmid_valid T) as dirty1.
    srewrite. simpl_hyp Heqd1b.
    - simpl_hyp Heqd1b. simpl_hyp Heqd2b.
      extract_adt C15 d1a2. extract_adt C16 d2a2.
      assert(Hind3: obs_eq HOSTVISOR d1a2 d2a2 \
                    icore d1a2 = true /\ icore d2a2 = true /\ shared_inv (shared d1a2) /\ shared_inv (shared d2a2)).
      { assert(indisting HOSTVISOR d1a2 d2a2).
        eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
        symmetry in Heqd1a2, Heqd2a2. clear Heqd1b Heqd2b.
        constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
        eapply set_vcpu_active_conf; try eassumption.
        Local Transparent query_oracle.
        rewrite Heqd1a2, Heqd2a2 in *; simpl in *. split_and; try assumption.
        eapply indisting_obs_eq in H. assumption.
        autounfold; simpl. rewrite ih11; reflexivity.
        autounfold; simpl. rewrite ih21; reflexivity.
        match type of Heqd1a2 with
        | context[query_oracle ?a] => pose proof (oracle_inv a)
        end. simpl in H0. apply H0. apply (set_vcpu_active_inv _ _ _ _ _ C9). assumption.
        match type of Heqd2a2 with
        | context[query_oracle ?a] => pose proof (oracle_inv a)
        end. simpl in H0. apply H0. apply (set_vcpu_active_inv _ _ _ _ _ C12). assumption. }
      destruct Hind3 as (Hind3 & cur12 & cur22 & ic12 & ic22 & inv12 & inv22).
      duplicate Hind3. destruct D. autounfold in *.
      symmetry in Heqd1a2, Heqd2a2.
      srewrite. pose proof (core_data_log_eq2 vmid) as core_data_eq3.
      Local Opaque query_oracle.
      simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
      duplicate sh_eq2. destruct D; autounfold in *. simpl_bool_eq.
      pose proof (boot_eq0 vmid). simpl_some. rewrite H in Heqd1b.
      simpl_hyp Heqd1b.
      extract_adt Heqd1b d1a3. extract_adt Heqd2b d2a3.
      simpl_hyp Heqd1b; simpl_hyp Heqd2b.
      assert(Hind3: shared_eq HOSTVISOR d1a3 d2a3 /\ icore d1a2 = true /\ icore d2a2 = true /\ shared_inv (shared d1a2) /\ shared_inv (shared d2a2)).
      { assert(indisting HOSTVISOR d1a2 d2a2).
        eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
        symmetry in Heqd1a2, Heqd2a2. clear Heqd1b Heqd2b.
        constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
        eapply set_vcpu_active_conf; try eassumption.
        Local Transparent query_oracle.
        rewrite Heqd1a2, Heqd2a2 in *; simpl in *. split_and; try assumption.
        eapply indisting_obs_eq in H. assumption.
        autounfold; simpl. rewrite ih11; reflexivity.
        autounfold; simpl. rewrite ih21; reflexivity.
        match type of Heqd1a2 with
        | context[query_oracle ?a] => pose proof (oracle_inv a)
        end. simpl in H0. apply H0. apply (set_vcpu_active_inv _ _ _ _ _ C9). assumption.
        match type of Heqd2a2 with
        | context[query_oracle ?a] => pose proof (oracle_inv a)
        end. simpl in H0. apply H0. apply (set_vcpu_active_inv _ _ _ _ _ C12). assumption. }
      destruct Hind3 as (Hind3 & cur12 & cur22 & ic12 & ic22 & inv12 & inv22).
      destruct_zmap. simpl. bool_rel_all0. rewrite Hcond, Hcond1.
      rewrite Heq in H; rewrite Hcond, Hcond1 in H.
      Local Transparent Z.eqb. autounfold in *. simpl. simpl in H. Local Opaque Z.eqb.
      simpl_some. rewrite H. reflexivity. assumption.
      unfold mset2. repeat rewrite ZMap.gss.
      assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). assumption.
      apply indisting_obs_eq in H. split_and; try assumption.
      rewrite Heqd1a2. rewrite oracle_cur_vmid. simpl. assumption.
      rewrite Heqd2a2. rewrite oracle_cur_vmid. simpl. assumption.
      rewrite Heqd1a2; rewrite oracle_icore; simpl. assumption.
      rewrite Heqd2a2; rewrite oracle_icore; simpl. assumption.
      unfold active. rewrite ih12; simpl_bool_eq. reflexivity.
      unfold active. rewrite ih22; simpl_bool_eq. reflexivity. }
      destruct Hind3 as (Hind3 & cur12 & cur22 & ic12 & ic22 & inv12 & inv22).
      split_and.
      destruct Hind3. autounfold in *. symmetry in Heqd1a2, Heqd2a2.
      assert(T1: 0 =? vmid = false) by (bool_rel; omega).
      assert(T2: vmid =? 0 = false) by (bool_rel; omega).
      repeat srewrite. pose proof (core_data_log_eq2 vmid) as core_log_eq3.
      simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
      pose proof (shadow_ctxt_eq2 vcpuid T) as shadow_eq2.
      repeat srewrite. simpl_hyp Heqd1b. simpl_hyp Heqd2b.
      rewrite <- Heqd1b, <- Heqd2b. clear Heqd1b Heqd2b.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply shadow_ctxt_eq2. assumption.
      intros. destruct_zmap. simpl. reflexivity. apply (dirty_eq2 _ _ Hvm Hvcpu).
      unfold mset2. repeat rewrite ZMap.gss. assert_gso. omega.
      repeat rewrite (ZMap.gso _ _ Hneq). apply data_log_eq2.
    - assert(T1: 0 =? vmid = false) by (bool_rel; omega).
      assert(T2: vmid =? 0 = false) by (bool_rel; omega).
      repeat srewrite. simpl in *; simpl_some; clear_hyp.
      simpl_hyp Heqd1b. simpl_hyp Heqd1b. simpl_hyp Heqd1b. simpl_hyp Heqd2b. simpl_hyp Heqd2b. split_and.
      rewrite <- Heqd1b, <- Heqd2b. clear Heqd1b Heqd2b.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply shadow_ctxt_eq1. assumption.
      intros. destruct_zmap. simpl. reflexivity. apply (dirty_eq1 _ _ Hvm Hvcpu).
      unfold mset2. repeat rewrite ZMap.gss. assert_gso. omega.
      repeat rewrite (ZMap.gso _ _ Hneq). apply data_log_eq1.
      intros. simpl. unfold mset2. repeat rewrite ZMap.gss.
      destruct_zmap. reflexivity. apply core_data_log_eq1.
      simpl_hyp Heqd2b. simpl_hyp Heqd2b.
      split_and.
      apply (prot_and_map_conf _ _ _ _ _ _ _ _ Heqd1b Heqd2b vmid_valid); simpl; try assumption.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply shadow_ctxt_eq1. assumption.
      intros. destruct_zmap. simpl. reflexivity. apply (dirty_eq1 _ _ Hvm Hvcpu).
      unfold mset2. repeat rewrite ZMap.gss. assert_gso. omega.
      repeat rewrite (ZMap.gso _ _ Hneq). apply data_log_eq1.
      intros. simpl. unfold mset2. repeat rewrite ZMap.gss.
      destruct_zmap. reflexivity. apply core_data_log_eq1.
    - rewrite <- Heqd1b in *; simpl in C3; contra. }
  destruct ind2 as (ind2 & inv12 & inv22).
  pose proof (vm_run_cur_same1 _ _ Heqd1b). pose proof (vm_run_cur_same1 _ _ Heqd2b). srewrite.
  destruct ind2; autounfold in *.
  srewrite; simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
  clear Heqd1a Heqd2a Heqd1b Heqd2b.
  hsimpl_func ex1; hsimpl_func ex2. apply OBS_EQ. srewrite.
  constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
  replace (cur_vmid d1a =? 0) with false. reflexivity.
  symmetry; bool_rel. omega.

Lemma vm_exit_confidentiality:
  forall vmid d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: vm_exit_handler_spec d1 = Some d1')
    (ex2: vm_exit_handler_spec d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex1; contra.
  simpl_hyp ex2; simpl_hyp ex2; simpl_hyp ex2; simpl_hyp ex2; contra.
  destruct p, p0. clear_hyp.
  assert(cur1: cur_vmid d1 = vmid).
  { autounfold in act1; rewrite C in act1; rewrite andb_comm in act1; simpl in act1.
    bool_rel; assumption. }
  assert(cur2: cur_vmid d2 = vmid).
  { autounfold in act2; rewrite C3 in act2; rewrite andb_comm in act2; simpl in act2.
    bool_rel; assumption. }
  assert(vmid_r: HOSTVISOR < vmid < COREVISOR).
  { destruct inv1. rewrite <- cur1. apply valid_vm_vmid0; assumption. }
  assert(valid_vcpu1: valid_vcpu (cur_vcpuid d1)).
  { destruct inv1. assumption. }
  assert(valid_vcpu2: valid_vcpu (cur_vcpuid d2)).
  { destruct inv2. assumption. }
  autounfold in *.
  assert(N0: vmid =? 0 = false) by (bool_rel; omega).
  apply indisting_obs_eq in obseq; try assumption.
  assert(Hind1: forall d'1 d'2 ret1 ret2 (ex1: vm_exit_pre_process d1 = Some (d'1, ret1))
                  (ex2: vm_exit_pre_process d2 = Some (d'2, ret2))
                  (hlt1: halt d'1 = false) (hlt2: halt d'2 = false),
                obs_eq vmid d'1 d'2 /\ ret1 = ret2 /\ cur_vmid d'1 = vmid /\ cur_vmid d'2 = vmid).
  { clear ex1 ex2. intros.
    duplicate obseq. destruct D; autounfold in *; srewrite; simpl_bool_eq; simpl in *.
    pose proof (shadow_ctxt_eq0 _ valid_vcpu2).
    simpl_some; clear_hyp.
    unfold vm_exit_pre_process in *; unfold vm_exit_dispatcher_spec_h in *; autounfold in *.
    repeat srewrite; clear_hyp.
    simpl_hyp ex1. simpl_hyp ex1. simpl_hyp ex2. simpl in *. repeat rewrite ZMap.gss in *. simpl in *.
    simpl_hyp C8. inv C8; inv C9. simpl_bool_eq. inv ex1; inv ex2; simpl in *. inv C2; inv C6.
    simpl in *. split.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    simpl. repeat rewrite ZMap.gss. simpl. reflexivity.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption. subst.
    split_and; try reflexivity. assumption.
    simpl_hyp C8. simpl_hyp C8. simpl_hyp C8. simpl_hyp C9. destruct p1, p2.
    exploit (grant_conf _ _ _ _ _ _ _ _ _ C13 C14); autounfold; simpl; try assumption; try reflexivity.
    destruct inv1. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. destruct inv2; bool_rel. assumption. assumption.
    destruct inv2. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. assumption. assumption.
    inv C8. simpl_bool_eq. inv ex1. inv C2. simpl in hlt1. assumption.
    inv C9. simpl_bool_eq. inv ex2. inv C6. simpl in hlt2. assumption.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    intros (Hind3 & cur31 & cur32 & vc3 & reg31 & reg32).
    inv C8; inv C9; simpl_bool_eq; inv ex1; inv ex2; inv C2; inv C6; simpl in *.
    destruct Hind3; autounfold in *; repeat srewrite; simpl_bool_eq; simpl in *.
    pose proof (shadow_ctxt_eq1 _ valid_vcpu1). srewrite.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    simpl_hyp C8. simpl_hyp C8. simpl_hyp C9. destruct p1, p2. inv C8; inv C9.
    simpl_bool_eq. inv ex1; inv ex2. inv C2; inv C6.
    exploit (revoke_conf _ _ _ _ _ _ _ _ _ C14 C15); autounfold; simpl; try assumption; try reflexivity.
    destruct inv1. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. destruct inv2; bool_rel. assumption. assumption.
    destruct inv2. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. assumption. assumption.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    intros (Hind3 & cur31 & cur32 & vc3 & reg31 & reg32).
    destruct Hind3; autounfold in *; repeat srewrite; simpl_bool_eq; simpl in *.
    pose proof (shadow_ctxt_eq1 _ valid_vcpu1). srewrite.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    inv C8; inv C9. replace (1 =? 0) with false in * by reflexivity.
    repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2; inv C2; inv C6.
    exploit (prep_exit_conf (cur_vmid d1) _ _ _ _ C8 C9); autounfold; simpl; try assumption; try reflexivity.
    destruct inv1. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. destruct inv2; bool_rel. assumption. assumption.
    destruct inv2. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. assumption. assumption.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    intros (Hind3 & cur31 & cur32 & vc3).
    srewrite; split_and; try reflexivity. assumption.
    inv C8; inv C9. simpl_bool_eq. inv ex1; inv ex2; inv C2; inv C6; simpl in *.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    assumption.
    repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2; inv C2; inv C6.
    exploit (prep_exit_conf (cur_vmid d1) _ _ _ _ C9 C10); autounfold; simpl; try assumption; try reflexivity.
    destruct inv1. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. destruct inv2; bool_rel. assumption. assumption.
    destruct inv2. constructor; simpl; try assumption. intros; contra. intros; contra.
    destruct_zmap; simpl. rewrite <- cur2. assumption. assumption.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    intros (Hind3 & cur31 & cur32 & vc3).
    srewrite; split_and; try reflexivity. assumption.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq0. assumption.
    simpl. assumption. }
  simpl_hyp ex1. simpl_hyp ex1. inv ex1. contra.
  simpl_hyp ex2. simpl_hyp ex2. inv ex2. contra.
  exploit Hind1; try reflexivity; try eassumption. intros (Hind2 & ret2 & cur1' & cur2').
  inv ret2. simpl_hyp ex1. simpl_some; subst. apply OBS_EQ. assumption.
  inv ex1; inv ex2; unfold switch_to_host. apply OBS_EQ.
  destruct Hind2. autounfold in *. simpl in *.
  assert(0 =? cur_vmid d1 = false) by (bool_rel; omega). simpl in H.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
Qed.

Lemma mem_load_confidentiality:
  forall vmid gfn reg d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: mem_load_spec gfn reg d1 = Some d1')
    (ex2: mem_load_spec gfn reg d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2; autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  assert(Hcur_eq1: cur_vmid d1 = vmid).
  apply orb_true_iff in act1. destruct act1; bool_rel_all0.
  destruct inv1. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  extract_adt ex1 d1q. extract_adt ex2 d2q.
  assert(inv_d1q: shared_inv (shared d1q)).
  rewrite Heqd1q. apply oracle_inv. destruct inv1; assumption.
  assert(inv_d2q: shared_inv (shared d2q)).
  rewrite Heqd2q. apply oracle_inv. destruct inv2; assumption.
  assert(Hind1: indisting vmid d1q d2q).
  eapply LOCAL_UNC. eapply obseq. apply ORACLE; assumption. apply ORACLE; assumption.
  apply indisting_obs_eq in Hind1. apply OBS_EQ.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *.
  repeat srewrite. destruct Hind1. duplicate sh_eq0. destruct D; autounfold in *; repeat (srewrite; simpl in *; simpl_bool_eq); clear_hyp.
  assert(z0 = z1).
  simpl_hyp C. pose proof (npt_eq0 z). simpl_hyp C; simpl_hyp C2. destruct p; destruct p0.
  simpl_hyp C; contra. simpl_hyp C2; contra. rewrite owner_eq0 in C2, H.
  simpl_hyp C; simpl_hyp C2. inv H. inv C; inv C2.
  pose proof (mem_eq0 z4). rewrite owner_eq0 in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). rewrite C11 in H. assumption.
  rewrite <- H in C11. destruct inv_d2q. rewrite page_0_invalid0 in C11. inversion C11.
  rewrite H in C12. destruct inv_d2q. rewrite page_0_invalid0 in C12. inversion C12.
  inv C; inv C2. reflexivity.
  pose proof (npt_eq0 z) as n1. simpl_hyp C. simpl_hyp C; simpl_hyp C2. simpl_hyp C; simpl_hyp C2.
  destruct p; destruct p0.
  destruct inv_d1q; destruct inv_d2q.
  pose proof (vm_iso0 (cur_vmid d1) z z8 z9 z5 C11) as vmi1.
  pose proof (vm_iso1 (cur_vmid d1) z z3 z4 z2 C8) as vmi2.
  inv n1. simpl_hyp C; contra. pose proof (count_eq0 z3). pose proof (owner_eq0 z3).
  exploit vmi1; autounfold in *; bool_rel. destruct role1' as [R|[R1 R2]]. contra. apply R1.
  destruct role1' as [R|[R1 R2]]. contra. rewrite R2. auto with zarith. assumption.
  intros (so1 & sg1).
  exploit vmi2; autounfold in *; bool_rel. destruct role2' as [R|[R1 R2]]. contra. apply R1.
  destruct role2' as [R|[R1 R2]]. contra. rewrite R2. auto with zarith. assumption.
  intros (so2 & sg2).
  rewrite so1, so2 in H. replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  rewrite H in C2. simpl_hyp C.
  inv C; inv C2.
  pose proof (mem_eq0 z3). rewrite so1, so2 in H1. simpl_bool_eq. assumption.
  inv C; inv C2. reflexivity.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  inv H. rewrite shadow_ctxt_eq0 in C4. rewrite C4 in C5. inv C5.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite shadow_ctxt_eq0. reflexivity. destruct inv2. assumption.
  apply shadow_ctxt_eq0. assumption.
  intros. destruct_zmap. simpl. reflexivity. apply dirty_eq0; assumption.
  destruct inv2; assumption.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma mem_store_confidentiality:
  forall vmid gfn reg d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: mem_store_spec gfn reg d1 = Some d1')
    (ex2: mem_store_spec gfn reg d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2; autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  assert(Hcur_eq1: cur_vmid d1 = vmid).
  apply orb_true_iff in act1. destruct act1; bool_rel_all0.
  destruct inv1. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  extract_adt ex1 d1q. extract_adt ex2 d2q.
  assert(inv_d1q: shared_inv (shared d1q)).
  rewrite Heqd1q. apply oracle_inv. destruct inv1; assumption.
  assert(inv_d2q: shared_inv (shared d2q)).
  rewrite Heqd2q. apply oracle_inv. destruct inv2; assumption.
  assert(Hind1: indisting vmid d1q d2q).
  eapply LOCAL_UNC. eapply obseq. apply ORACLE; assumption. apply ORACLE; assumption.
  apply indisting_obs_eq in Hind1. apply OBS_EQ.
  rewrite Heqd1q in ex1. rewrite Heqd2q in ex2. simpl in *.
  srewrite. simpl_hyp ex1.
  destruct Hind1. duplicate sh_eq0. destruct D. autounfold in *.
  pose proof (npt_eq0 z). srewrite; simpl_bool_eq; simpl in *.
  simpl_hyp ex1. simpl_hyp ex2. destruct p, p0. simpl_hyp ex1; contra. simpl_hyp ex2; contra.
  rewrite owner_eq0 in ex1, H. bool_rel.
  simpl_hyp ex1; simpl_hyp ex2. inv H. inv ex1; inv ex2; simpl in *.
  pose proof (mem_eq0 z4). rewrite owner_eq0 in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). rewrite C8 in H.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite owner_eq0. rewrite shadow_ctxt_eq0. reflexivity.
  destruct inv2. assumption. apply mem_eq0.
  rewrite H in C7. destruct inv_d2q. rewrite page_0_invalid0 in C7. inversion C7.
  rewrite <- H in C8. destruct inv_d2q. rewrite page_0_invalid0 in C8. inversion C8.
  inv ex1; inv ex2. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl_hyp ex1; simpl_hyp ex2. destruct Hind1. duplicate sh_eq0. destruct D.
  autounfold in *. pose proof (npt_eq0 z) as n1.
  replace (vmid =? 0) with false in n1 by (symmetry; bool_rel; assumption). simpl in n1.
  simpl_hyp ex1; simpl_hyp ex2. destruct p, p0. simpl_hyp ex1; simpl_hyp ex2; contra. inv n1.
  pose proof (count_eq0 z4). pose proof (owner_eq0 z4).
  destruct inv_d1q; destruct inv_d2q.
  pose proof (vm_iso0 (cur_vmid d1) z z4 z3 z0 C5) as vmi1.
  pose proof (vm_iso1 (cur_vmid d1) z z4 z5 z1 C6) as vmi2.
  exploit vmi1; autounfold in *; bool_rel. destruct role1' as [R|[R1 R2]]. contra. apply R1.
  destruct role1' as [R|[R1 R2]]. contra. simpl. repeat simpl_hyp ex1; inv ex1; simpl in R2; rewrite R2.
  auto with zarith. auto with zarith. assumption.
  intros (so1 & sg1).
  exploit vmi2; autounfold in *; bool_rel. destruct role2' as [R|[R1 R2]]. contra. apply R1.
  destruct role2' as [R|[R1 R2]]. contra. simpl. repeat simpl_hyp ex2; inv ex2; simpl in R2; rewrite R2.
  auto with zarith. auto with zarith. assumption.
  intros (so2 & sg2).
  rewrite so1, so2 in H. replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  simpl in H. rewrite H in ex1. simpl_hyp ex1.
  pose proof (mem_eq0 z4). rewrite so1, so2 in H1. simpl_bool_eq.
  inv ex1; inv ex2.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. simpl in so1, so2. rewrite so1, so2, shadow_ctxt_eq0. simpl_bool_eq.
  simpl. simpl in cur_vcpu_eq0. rewrite Hcur_eq2 in cur_vcpu_eq0. simpl_bool_eq. rewrite cur_vcpu_eq0.
  reflexivity. destruct inv1. assumption. apply mem_eq0.
  simpl. simpl in regs_eq0. srewrite. simpl_bool_eq; simpl in regs_eq0. assumption.
  srewrite; simpl in cur_vcpu_eq0; simpl_bool_eq. rewrite Hcur_eq2 in cur_vcpu_eq0. simpl_bool_eq. assumption.
  inv ex1; inv ex2; constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl. simpl in regs_eq0. srewrite. simpl_bool_eq; simpl in regs_eq0. assumption.
  srewrite; simpl in cur_vcpu_eq0; simpl_bool_eq. rewrite Hcur_eq2 in cur_vcpu_eq0. simpl_bool_eq. assumption.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma dev_load_confidentiality:
  forall vmid gfn reg cbndx index d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: dev_load_spec gfn reg cbndx index d1 = Some d1')
    (ex2: dev_load_spec gfn reg cbndx index d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2; autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  assert(Hcur_eq1: cur_vmid d1 = vmid).
  apply orb_true_iff in act1. destruct act1; bool_rel_all0.
  destruct inv1. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  extract_adt ex1 d1q. extract_adt ex2 d2q.
  assert(inv_d1q: shared_inv (shared d1q)).
  rewrite Heqd1q. apply oracle_inv. destruct inv1; assumption.
  assert(inv_d2q: shared_inv (shared d2q)).
  rewrite Heqd2q. apply oracle_inv. destruct inv2; assumption.
  assert(Hind1: indisting vmid d1q d2q).
  eapply LOCAL_UNC. eapply obseq. apply ORACLE; assumption. apply ORACLE; assumption.
  apply indisting_obs_eq in Hind1. apply OBS_EQ.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *.
  bool_rel_all0.
  repeat srewrite. destruct Hind1. duplicate sh_eq0. destruct D; autounfold in *; repeat (srewrite; simpl in *; simpl_bool_eq); clear_hyp.
  assert(z0 = z1).
  simpl_hyp C. exploit (spt_eq0 z cbndx index); try (split; assumption). intros Hspt.
  bool_rel. autounfold in Hspt. rewrite C, C4 in Hspt. simpl_bool_eq.
  simpl_hyp C5. rewrite Hspt in C5. simpl_hyp C5. simpl_hyp C5; contra.
  rewrite owner_eq0 in C5. pose proof (mem_eq0 z2). rewrite owner_eq0 in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). simpl_hyp C5.
  inv C5; inv C8. assumption. inv C5; inv C8; reflexivity.
  simpl_hyp C5; simpl_hyp C8; contra.
  rewrite Hspt in C5. simpl_hyp C5. simpl_hyp C5; contra.
  destruct inv_d1q; destruct inv_d2q.
  exploit (smmu_iso0 cbndx index z z2 z3); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. rewrite C4. omega.  simpl; intros (so1 & sg1).
  exploit (smmu_iso1 cbndx index z z2 z3); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. rewrite C. omega.  simpl; intros (so2 & sg2).
  pose proof (count_eq0 z2). rewrite so1, so2 in H.
  replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  autounfold in H; rewrite C, C4 in H. simpl_bool_eq.
  replace (cur_vmid d1 =? 4294967295) with false in H by (symmetry; bool_rel; omega).
  rewrite H in C5. simpl_hyp C5.
  inv C5; inv C8.
  pose proof (mem_eq0 z2). rewrite so1, so2 in H0. simpl_bool_eq.
  autounfold in H0; rewrite C, C4 in H0. simpl_bool_eq. assumption.
  inv C5; inv C8. reflexivity.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  inv H. rewrite shadow_ctxt_eq0 in C7. rewrite C7 in C9. inv C9.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite shadow_ctxt_eq0. reflexivity. destruct inv2. assumption.
  apply shadow_ctxt_eq0. assumption.
  intros. destruct_zmap. simpl. reflexivity. apply dirty_eq0; assumption.
  destruct inv2; assumption.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma dev_store_confidentiality:
  forall vmid gfn reg cbndx index d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = true)
    (act2: active vmid d2 = true)
    (inv1: state_inv d1)
    (inv2: state_inv d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: dev_store_spec gfn reg cbndx index d1 = Some d1')
    (ex2: dev_store_spec gfn reg cbndx index d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2; autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  assert(Hcur_eq1: cur_vmid d1 = vmid).
  apply orb_true_iff in act1. destruct act1; bool_rel_all0.
  destruct inv1. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid0; assumption. assumption.
  extract_adt ex1 d1q. extract_adt ex2 d2q.
  assert(inv_d1q: shared_inv (shared d1q)).
  rewrite Heqd1q. apply oracle_inv. destruct inv1; assumption.
  assert(inv_d2q: shared_inv (shared d2q)).
  rewrite Heqd2q. apply oracle_inv. destruct inv2; assumption.
  assert(Hind1: indisting vmid d1q d2q).
  eapply LOCAL_UNC. eapply obseq. apply ORACLE; assumption. apply ORACLE; assumption.
  apply indisting_obs_eq in Hind1. apply OBS_EQ.
  rewrite Heqd1q in ex1. rewrite Heqd2q in ex2. simpl in *.
  srewrite. simpl_hyp ex1.
  destruct Hind1. duplicate sh_eq0. destruct D. autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  exploit (spt_eq0 z cbndx index). bool_rel_all0; omega. bool_rel_all0; omega.
  intro Hspt.
  simpl_hyp ex1. srewrite; simpl_bool_eq; simpl in *.
  rewrite Hspt in ex1. simpl_hyp ex1. simpl_hyp ex1; contra.
  rewrite owner_eq0 in ex1.
  simpl_hyp ex1. inv ex1; inv ex2; simpl in *.
  pose proof (mem_eq0 z0). rewrite owner_eq0 in H. bool_rel; srewrite; simpl_bool_eq.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite owner_eq0. rewrite shadow_ctxt_eq0. reflexivity.
  destruct inv2. assumption. apply mem_eq0.
  inv ex1; inv ex2. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl_hyp ex1; simpl_hyp ex2.
  bool_rel_all0. autounfold in *. simpl in *. srewrite. rewrite Hspt in ex1.
  simpl_hyp ex1. simpl_hyp ex1; contra.
  destruct inv_d1q; destruct inv_d2q. autounfold in *.
  exploit (smmu_iso0 cbndx index z z0 z1); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. omega. simpl; intros (so1 & sg1). autounfold in *; rewrite C4 in so1.
  exploit (smmu_iso1 cbndx index z z0 z1); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. omega. simpl; intros (so2 & sg2). autounfold in *; rewrite C5 in so2.
  pose proof (count_eq0 z0). rewrite so1, so2 in H.
  replace (vmid =? 4294967295) with false in H. simpl_bool_eq.
  rewrite H in ex1. simpl_hyp ex1. inv ex1; inv ex2.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  destruct sh_eq0.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite so1, so2, shadow_ctxt_eq0. reflexivity.
  destruct inv2. assumption. apply mem_eq0.
  simpl in *. srewrite; simpl_bool_eq.
  intros. rewrite <- Hcur_eq1. replace (cur_vmid d1 =? 0) with false. reflexivity.
  symmetry; bool_rel; omega. intros. rewrite <- Hcur_eq1.
  replace (cur_vmid d1 =? 0) with false. rewrite Hcur_eq1. apply core_data_log_eq0.
  symmetry; bool_rel; omega.
  inv ex1; inv ex2; constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. rewrite <- Hcur_eq1. replace (cur_vmid d1 =? 0) with false. reflexivity.
  symmetry; bool_rel; omega. intros. rewrite <- Hcur_eq1.
  replace (cur_vmid d1 =? 0) with false. rewrite Hcur_eq1. apply core_data_log_eq0.
  symmetry; bool_rel; omega.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

```
