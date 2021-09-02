# Noninterference

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
Require Import TrapHandler.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import AbstractMachine.Spec.
Require Import Invs.
Require Import InvProofs.
Require Import SecurityDef.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.ltb Z.geb Z.gtb.

Lemma map_host_integ:
  forall vmid addr s s' a b
    (ex: local_map_host addr s = (s', false, a, b))
    (Haddr: valid_addr addr)
    (Hvm: valid_vm vmid)
    (Hstate: vm_state (VS (vmid @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid s s'.
Proof.
  intros. unfold local_map_host in *; autounfold in*; simpl in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold in *; intros;
    try replace (vmid =? 0) with false by (symmetry; bool_rel; omega); simpl;
      try rewrite Hn; srewrite; try reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
  reflexivity.
Qed.

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
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq in ex1.
  destruct (s2_owner (addr / PAGE_SIZE) @ (s2page s2) =? INVALID) eqn:Hinvalid; simpl in *.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2. bool_rel.
  pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  repeat rewrite ZMap.gss. rewrite Hn1, Hn2. intros.
  pose proof (npt_eq gfn). destruct_zmap.
  rewrite host_pte_pfn_dev. autounfold. rewrite owner_eq. rewrite Hinvalid. reflexivity.
  assumption. assumption.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2. bool_rel.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C2) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  repeat rewrite ZMap.gss. rewrite Hn1, Hn2. intros.
  pose proof (npt_eq gfn). destruct_zmap.
  rewrite host_pte_pfn_mem. rewrite owner_eq. reflexivity. assumption.
  assumption.
Qed.

Lemma clear_vm_page_integ:
  forall vmid0 vmid pfn s s' a b c
    (ex: local_clear_vm_page vmid pfn s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (valid_state': vm_state (VS (vmid @ (vminfos s))) = POWEROFF)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_clear_vm_page in *; autounfold in*; simpl in *.
  repeat simpl_hyp ex; inv ex.
  intros. assert(vm_neq: vmid0 <> vmid).
  red. intro T; subst. omega.
  constructor; autounfold in *; intros; bool_rel;
    try replace (vmid0 =? 0) with false by (symmetry; bool_rel; omega); simpl;
      try rewrite Hn; srewrite; try reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
  reflexivity.
  destruct_zmap. srewrite.
  replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (0 =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  destruct_zmap. srewrite.
  replace (vmid =? 4294967295) with false by (symmetry; bool_rel; omega).
  simpl. replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega).
  replace (0 =? 4294967295) with false by reflexivity.
  destruct_if; reflexivity. reflexivity.
  destruct_zmap. srewrite.
  replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (0 =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  destruct_zmap. srewrite.
  replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (0 =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  constructor; intros; reflexivity.
Qed.

Lemma Z_div_le_le:
  forall a b c d, 0 < d -> a <= b <= c -> a / d <= b / d <= c / d.
Proof.
  intros. destruct H0; split; apply Z_div_le; assumption.
Qed.

Lemma assign_pfn_to_vm_integ:
  forall vmid0 vmid gfn pfn dorc logn s s' n a b c
    (ex: local_assign_pfn_to_vm vmid gfn pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hvm: valid_vm vmid0)
    (Hvm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_assign_pfn_to_vm in *; autounfold in*; simpl in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold in *; intros; bool_rel;
    try replace (vmid0 =? 0) with false by (symmetry; bool_rel; omega); simpl;
      try rewrite Hn; srewrite; try reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
  reflexivity.
  destruct_zmap. srewrite
.
  replace (0 =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  destruct_zmap. srewrite.
  replace (0 =? 4294967295) with false by reflexivity.
  simpl. replace (0 =? vmid0) with false by (symmetry; bool_rel; omega).
  replace (vmid =? 4294967295) with false by  (symmetry; bool_rel; omega).
  destruct_if; reflexivity. reflexivity.
  destruct_zmap. srewrite.
  replace (0 =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  destruct_zmap. srewrite.
  replace (0 =? vmid0) with false by (symmetry; bool_rel; omega).
  simpl. replace (vmid =? vmid0) with false by (symmetry; bool_rel; omega). reflexivity.
  reflexivity.
  rewrite zmap_set_id. constructor; intros; reflexivity.
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
  unfold observe_owner in *. simpl_bool_eq. rewrite owner_eq in ex1. unfold observe_count in *.
  simpl_hyp ex1. bool_rel.
  pose proof (count_eq pfn) as Hcount. rewrite owner_eq in Hcount; rewrite C in Hcount.
  replace (HOSTVISOR =? INVALID) with false in Hcount by reflexivity; simpl_bool_eq.
  rewrite Hcount in ex1. simpl_hyp ex1. autounfold in *; simpl_bool_eq.
  repeat simpl_hyp ex1; try solve [inv ex1].
  repeat simpl_hyp ex2; try solve [inv ex2].
  assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
  { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
    inv C3. destruct inv1. pose proof (host_flatmap _ _ _ _ C1).
    destruct (zeq z0 0). srewrite. repeat eexists.
    apply H in n. destruct n. srewrite. pose proof (host_npt_cons _ _ _ _ C1) as T.
    replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
    srewrite. repeat eexists.
    pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H.
    rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
    autounfold; omega. }
  assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
  { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
    inv C7. destruct inv2. pose proof (host_flatmap _ _ _ _ C5).
    destruct (zeq z3 0). srewrite. repeat eexists.
    apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons _ _ _ _ C5) as T.
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
  intros. pose proof (npt_eq gfn0). repeat rewrite ZMap.gss.
  destruct (gfn0 =? pfn) eqn:Hgfn; bool_rel; srewrite.
  assert_gso. red. intro T. rewrite <- T in C. destruct inv2. rewrite page_0_invalid in C. autounfold in *; omega.
  repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq. reflexivity.
  rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
  destruct (gfn0 @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn0 @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq in H.
  assert(T1: z6 = 0 \/ z6 = gfn0).
  destruct inv1. pose proof (host_flatmap _ _ _ _ Hpt1).
  destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
  assert(T2: z9 = 0 \/ z9 = gfn0).
  destruct inv2. pose proof (host_flatmap _ _ _ _ Hpt2).
  destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
  destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  rewrite <- H. destruct_if; destruct_if; reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct_if; destruct_if; reflexivity. assumption.
  intros. destruct_zmap. reflexivity. apply owner_eq.
  intros. destruct_zmap. simpl.
  replace (vmid =? 4294967295) with false by (symmetry; bool_rel; omega).
  replace (vmid =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
  apply count_eq.
  intros. destruct_zmap. reflexivity. apply gfn_eq.
  intros. destruct_zmap. reflexivity. apply mem_eq.
  inv ex1. autounfold in *; simpl_bool_eq. rewrite gfn_eq in ex1.
  simpl_hyp ex1. bool_rel_all0.
  pose proof (count_eq pfn) as Hcount. rewrite owner_eq in Hcount; rewrite Hcond in Hcount.
  rewrite zmap_set_id in ex1. rewrite zmap_set_id in ex2.
  simpl_hyp ex1; simpl_hyp ex2; inv ex1; inv ex2; split; try reflexivity;
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  inv ex1.
Qed.

Lemma assign_pfn_to_vm_conf_res:
  forall vmid gfn pfn dorc logn s1 s2 s1' s2' n1 n2 a1 b1 c1 a2 b2 c2
    (ex1: local_assign_pfn_to_vm vmid gfn pfn dorc logn s1 = (s1', false, n1, a1, b1, c1))
    (ex2: local_assign_pfn_to_vm vmid gfn pfn dorc logn s2 = (s2', false, n2, a2, b2, c2))
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2' /\ n1 = n2.
Proof.
  intros. unfold local_assign_pfn_to_vm in *; simpl in *; duplicate obseq; destruct D.
  autounfold in *. replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  pose proof (owner_eq pfn) as Howner.
  pose proof (count_eq pfn) as Hcount.
  pose proof (gfn_eq pfn) as Hgfn.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2;
    bool_rel; srewrite; try replace (0 =? vmid) with false in * by (symmetry; bool_rel; omega);
      try replace (0 =? 4294967295) with false in * by (symmetry; bool_rel; omega); simpl in *.
  split; auto.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. reflexivity. apply owner_eq.
  intros. destruct_zmap. reflexivity. apply count_eq.
  intros. destruct_zmap. reflexivity. apply gfn_eq.
  intros. destruct_zmap. reflexivity. apply mem_eq.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  repeat rewrite zmap_set_id. split; auto.
  destruct s1; destruct s2; simpl in *; assumption.
Qed.

Lemma map_pfn_vm_integ:
  forall vmid0 vmid addr pte level s s' a
    (ex: local_map_pfn_vm vmid addr pte level s = (s', false, a))
    (valid_vm': valid_vm vmid)
    (Hvm: HOSTVISOR <= vmid0 < COREVISOR)
    (Hvm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_map_pfn_vm in *; simpl in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold in *; simpl in *; repeat rewrite (ZMap.gso _ _ Hvm_neq); try reflexivity.
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
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq.
Qed.

Lemma map_pfn_vm_conf_res:
  forall vmid addr pte level s1 s2 s1' s2' a1 a2
    (ex1: local_map_pfn_vm vmid addr pte level s1 = (s1', false, a1))
    (ex2: local_map_pfn_vm vmid addr pte level s2 = (s2', false, a2))
    (owner1: forall pfn, (if level =? 2 then phys_page pte / PAGE_SIZE <= pfn < phys_page pte / PAGE_SIZE + 512
                    else pfn = phys_page pte / PAGE_SIZE) -> s2_owner (pfn @ (s2page s1)) = vmid)
    (valid_vm: valid_vm vmid)
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_map_pfn_vm in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1. repeat simpl_hyp ex2; inv ex2.
  destruct (level =? 2) eqn:Hlevel.
  simpl in *; autounfold in *.
  bool_rel; srewrite; try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    try assumption.
  intros. repeat rewrite ZMap.gss.
  pose proof (local_mmap_level2 _ _ _ _ _ C gfn) as Hn1.
  pose proof (local_mmap_level2 _ _ _ _ _ C0 gfn) as Hn2.
  destruct in_range_n in *. rewrite Hn1, Hn2. reflexivity. srewrite. apply npt_eq.
  bool_rel; srewrite; try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    try assumption.
  intros. repeat rewrite ZMap.gss.
  pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn2.
  rewrite Hn1, Hn2. destruct_zmap. reflexivity. apply npt_eq.
Qed.

Lemma map_io_integ:
  forall vmid0 vmid gpa pa s s' a b c
    (ex: local_map_io vmid gpa pa s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_map_io in *; simpl in *.
  repeat simpl_hyp ex; inv ex.
  assert(vmid0 <> vmid).
  red; intro; srewrite; bool_rel; autounfold in *; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  repeat rewrite (ZMap.gso _ _ H). reflexivity.
  constructor; intros; reflexivity.
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
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq in ex1.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  simpl in *.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq.
  assumption.
Qed.

Lemma grant_vm_page_integ:
  forall vmid0 vmid pfn s s' a
    (ex1: local_grant_vm_page vmid pfn s = (s', a))
    (valid_vm': valid_vm vmid)
    (vm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_grant_vm_page in *; simpl in *; autounfold in *.
  inv ex1. destruct_if. bool_rel_all.
  constructor; autounfold; intros; try reflexivity.
  destruct_if; bool_rel. destruct (gfn @ (pt vmid0 @ (npts s))).
  destruct p. destruct_zmap; subst; simpl; reflexivity. reflexivity.
  destruct_if; bool_rel. destruct_zmap; subst; simpl; reflexivity.
  destruct_zmap; subst; simpl; reflexivity.
  destruct_if; bool_rel. destruct_zmap; subst; simpl;
  rewrite Case0; simpl_bool_eq; reflexivity.
  destruct_zmap; subst; simpl.
  destruct_if. bool_rel; omega. destruct_if. bool_rel; omega. reflexivity.
  replace (s2_owner pfn0 @ (s2page s) =? 4294967295) with false by (symmetry; bool_rel; omega).
  reflexivity.
  destruct_if; bool_rel. destruct_zmap; subst; simpl; reflexivity.
  destruct_zmap; subst; simpl; reflexivity.
  destruct_if. destruct_zmap; simpl; srewrite; simpl_bool_eq; reflexivity.
  destruct_zmap; simpl; destruct_if; bool_rel; try omega; reflexivity.
  constructor; autounfold; intros; reflexivity.
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
  pose proof (owner_eq pfn).
  destruct (s2_owner pfn @ (s2page s1) =? vmid) eqn:Howner1, (s2_owner pfn @ (s2page s2) =? vmid) eqn:Howner2; simpl in *; try omega.
  bool_rel. pose proof (count_eq pfn) as Hcount. pose proof (gfn_eq pfn) as Hgfn.
  rewrite Howner1, Howner2 in *; simpl_bool_eq.
  replace (vmid =? 4294967295) with false in * by (symmetry; bool_rel; omega). rewrite Hcount in *.
  destruct (s2_count pfn @ (s2page s2) <? 100) eqn:Hcnt.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq.
  intros. pose proof (mem_eq pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
Qed.

Lemma revoke_vm_page_integ:
  forall vmid0 vmid pfn dorc logn s s' a b c n
    (ex1: local_revoke_vm_page vmid pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (vm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_revoke_vm_page in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex1; inv ex1. bool_rel_all.
  - assert(Hnp: exists l e, pfn @ (pt n0) = (0, l, e)).
    { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
      inv C3. destruct inv1. pose proof (host_flatmap _ _ _ _ C1).
      destruct (zeq z0 0). srewrite. repeat eexists.
      apply H in n. destruct n. srewrite. pose proof (host_npt_cons _ _ _ _ C1) as T.
      replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
      srewrite. repeat eexists.
      pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H.
      rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
      autounfold; omega. }
    assert(Hne: forall pfn0, pfn0 <> pfn -> pfn0 @ (pt n0) = pfn0 @ (pt HOSTVISOR @ (npts s))).
    { intros. destruct (z =? 0). inv C3. reflexivity.
      pose proof (local_mmap_level3 _ _ _ _ _ C3). rewrite H0.
      rewrite Z_div_mult_full. rewrite (ZMap.gso _ _ H). reflexivity.
      autounfold; omega. }
    destruct Hnp as (l1 & e1 & Hnp).
    constructor; intros; autounfold; try reflexivity;
      match goal with
      | [|- context [vmid0 =? 0]] =>
        destruct (vmid0 =? 0) eqn:Hhost; bool_rel; [srewrite; simpl; repeat rewrite ZMap.gss |]
      | [ |- _] => idtac
      end.
    destruct (gfn =? pfn) eqn:Hgfn; bool_rel. srewrite.
    destruct_zmap. rewrite <- Heq in Hcond. destruct inv1. rewrite page_0_invalid in Hcond.
    autounfold in Hcond; omega. destruct_if. bool_rel.
    destruct (zeq z0 0). srewrite. destruct_if; reflexivity.
    destruct inv1. assert (pfn = z0). eapply host_flatmap; try eassumption.
    srewrite. omega. destruct_if; reflexivity. rewrite Hne; try assumption.
    autounfold. destruct (gfn @ (pt 0 @ (npts s))) eqn:Hn. destruct p.
    destruct_zmap. simpl. reflexivity. reflexivity.
    simpl. rewrite (ZMap.gso _ _ Hhost). reflexivity.
    destruct_zmap; simpl; reflexivity.
    simpl. destruct_zmap; simpl. reflexivity. reflexivity.
    simpl. destruct_zmap. simpl. destruct_if. reflexivity.
    destruct_if. bool_rel; omega. reflexivity.
    reflexivity. destruct_zmap; reflexivity.
    simpl. destruct_zmap; reflexivity.
    simpl. destruct_zmap. simpl. destruct_if.
    bool_rel; omega. reflexivity. reflexivity.
  - bool_rel_all.
    constructor; autounfold; intros; try reflexivity.
    destruct_if; bool_rel. destruct (gfn @ (pt vmid0 @ (npts s))).
    destruct p. destruct_zmap; subst; simpl; reflexivity. reflexivity.
    destruct_if; bool_rel. destruct_zmap; subst; simpl; reflexivity.
    destruct_zmap; subst; simpl; reflexivity.
    destruct_if; bool_rel. destruct_zmap; subst; simpl; rewrite Case; simpl_bool_eq; reflexivity.
    destruct_zmap; subst; simpl.
    destruct_if. bool_rel; omega. destruct_if. bool_rel; omega. reflexivity.
    replace (s2_owner pfn0 @ (s2page s) =? 4294967295) with false by (symmetry; bool_rel; omega).
    reflexivity.
    destruct_if; bool_rel. destruct_zmap; subst; simpl; reflexivity.
    destruct_zmap; subst; simpl; reflexivity.
    destruct_if. destruct_zmap; simpl; srewrite; simpl_bool_eq; reflexivity.
    destruct_zmap; simpl; destruct_if; bool_rel; try omega; reflexivity.
  - constructor; autounfold; intros; reflexivity.
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
  pose proof (owner_eq pfn).
  destruct (s2_owner pfn @ (s2page s1) =? vmid) eqn:Howner1, (s2_owner pfn @ (s2page s2) =? vmid) eqn:Howner2; simpl in *; try omega.
  bool_rel. pose proof (count_eq pfn) as Hcount. pose proof (gfn_eq pfn) as Hgfn.
  rewrite Howner1, Howner2 in *; simpl_bool_eq.
  replace (vmid =? 4294967295) with false in * by (symmetry; bool_rel; omega). rewrite Hcount in *.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  assert_gso. omega. repeat rewrite(ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq.
  intros. pose proof (mem_eq pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (s2_owner pfn @ (s2page s1) =? 0) with false by (symmetry; bool_rel; omega);
    try assumption.
  intros. destruct_zmap. simpl. srewrite; simpl_bool_eq. reflexivity. apply owner_eq.
  intros. destruct_zmap. simpl. srewrite. destruct_if. bool_rel; omega. simpl_bool_eq. reflexivity. apply count_eq.
  intros. destruct_zmap. simpl. srewrite. simpl_bool_eq. reflexivity. apply gfn_eq.
  intros. pose proof (mem_eq pfn0). destruct_zmap. simpl. srewrite.  simpl_bool_eq. reflexivity. assumption.
  assumption. inv ex1; inv ex2; assumption.
Qed.

Lemma set_vcpu_active_integ:
  forall vmid0 vmid vcpuid s s' a
    (ex: local_set_vcpu_active vmid vcpuid s = (s', false, a))
    (vm_neq: vmid0 <> vmid)
    (inv2: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_set_vcpu_active in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all. autounfold in *.
  constructor; intros; autounfold;
    repeat rewrite (ZMap.gso _ _ vm_neq); simpl; try reflexivity.
  destruct_if. destruct_zmap. simpl. reflexivity. reflexivity.
  destruct_if. bool_rel; srewrite; rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
  destruct_if. reflexivity.
  destruct_if. bool_rel; srewrite; rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma set_vcpu_active_conf_res:
  forall vmid vcpuid s1 s2 s1' s2' a1 a2
    (ex1: local_set_vcpu_active vmid vcpuid s1 = (s1', false, a1))
    (ex2: local_set_vcpu_active vmid vcpuid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq vmid s1 s2),
    shared_eq vmid s1' s2'.
Proof.
  intros. unfold local_set_vcpu_active in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
  intros. pose proof (state_eq vmid0).
  destruct_if. reflexivity. destruct_if. bool_rel. srewrite.
  repeat rewrite ZMap.gss. simpl. inv H. reflexivity. reflexivity.
Qed.

Lemma set_vcpu_inactive_integ:
  forall vmid0 vmid vcpuid s s' a
    (ex: local_set_vcpu_inactive vmid vcpuid s = (s', false, a))
    (vm_neq: vmid0 <> vmid)
    (inv2: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_set_vcpu_inactive in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all. autounfold in *.
  constructor; intros; autounfold;
    repeat rewrite (ZMap.gso _ _ vm_neq); simpl; try reflexivity.
  destruct_if. destruct_zmap. simpl. reflexivity. reflexivity.
  destruct_if. bool_rel; srewrite; rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
  destruct_if. reflexivity.
  destruct_if. bool_rel; srewrite; rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
  intros. pose proof (state_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H.
  destruct_if. reflexivity. simpl_bool_eq.
  inv H. reflexivity. assumption.
Qed.

Lemma set_vcpu_inactive_conf_res:
  forall vmid vcpuid s1 s2 s1' s2' a1 a2
    (ex1: local_set_vcpu_inactive vmid vcpuid s1 = (s1', false, a1))
    (ex2: local_set_vcpu_inactive vmid vcpuid s2 = (s2', false, a2))
    (inv1: shared_inv s1)
    (inv2: shared_inv s2)
    (obseq: shared_eq HOSTVISOR s1 s2),
    shared_eq HOSTVISOR s1' s2'.
Proof.
  intros. unfold local_set_vcpu_inactive in *; simpl in *; duplicate obseq; destruct D.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma register_vcpu_integ:
  forall vmid0 vmid vcpuid s s' a
    (ex: local_register_vcpu vmid vcpuid s = (s', false, a))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_register_vcpu in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all.
  assert(vmid0 <> vmid). red; intro. inv H. autounfold in *; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma gen_vmid_integ:
  forall vmid0 s s' a
    (ex: local_gen_vmid s = (s', false, a))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_gen_vmid in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
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
  inv core_data_eq. reflexivity.
Qed.

Lemma register_kvm_integ:
  forall vmid0 vmid s s' a
    (ex: local_register_kvm vmid s = (s', false, a))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_register_kvm in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all.
  assert(vmid0 <> vmid). red; intro. inv H. autounfold in *; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma set_boot_info_integ:
  forall vmid0 vmid load_addr size s s' a b
    (ex: local_set_boot_info vmid load_addr size s = (s', false, a, b))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_set_boot_info in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all.
  assert(vmid0 <> vmid). red; intro. inv H. autounfold in *; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  constructor; intros; reflexivity.
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
  unfold observe_boot_info in *; simpl_bool_eq. pose proof (boot_eq vmid) as Hboot; simpl_some.
  rewrite Hboot in ex1. repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; try assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. destruct_zmap. simpl; srewrite. inv core_data_eq. reflexivity.
  apply boot_eq. inv core_data_eq. reflexivity.
Qed.

Lemma remap_vm_image_integ:
  forall vmid0 vmid pfn load_idx s s' a b
    (ex: local_remap_vm_image vmid pfn load_idx s = (s', false, a, b))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_remap_vm_image in *; simpl in *.
  repeat simpl_hyp ex; inv ex. bool_rel_all.
  assert(vmid0 <> vmid). red; intro. inv H. autounfold in *; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  destruct_if; bool_rel; subst. repeat rewrite (ZMap.gso _ _ H). reflexivity. reflexivity.
  constructor; intros; reflexivity.
  constructor; intros; reflexivity.
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
  unfold observe_boot_info in *; simpl_bool_eq. pose proof (boot_eq vmid) as Hboot; simpl_some.
  rewrite Hboot in ex1. repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; try assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). apply npt_eq.
  intros. destruct_zmap. simpl; srewrite. inv core_data_eq. reflexivity.
  apply boot_eq.
Qed.

Lemma smmu_assign_page_integ:
  forall vmid cbndx index pfn gfn s s' a b c d
    (ex: local_smmu_assign_page cbndx index pfn gfn s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid)
    (Hstate: vm_state (VS (vmid @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid s s'.
Proof.
  intros. unfold local_smmu_assign_page in *.
  autounfold in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold; reflexivity.
  simpl_hyp C6. inv C6. rewrite zmap_set_id.
  constructor; autounfold; srewrite; simpl;
    try replace (vmid =? 0) with false by (symmetry; bool_rel; omega);
    try reflexivity.
  intros. destruct_zmap. inv Heq. simpl. rewrite C2.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  assert ((index * 8 + cbndx) @ (smmu_vmid s) =? vmid = false).
  bool_rel. red. intro. rewrite H in C1. omega. rewrite H. reflexivity. reflexivity.
  intros. destruct_zmap. simpl. inv Heq. rewrite C2.
  replace (0 =? 4294967295) with false by reflexivity.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  destruct_if. bool_rel; omega. destruct_if. bool_rel. rewrite Case0 in C1. omega.
  reflexivity. reflexivity.
  intros. destruct_zmap. simpl. srewrite.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  destruct_if. bool_rel. rewrite Case in C1. omega. reflexivity. reflexivity.
  intros. destruct_zmap. simpl. srewrite.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  destruct_if. bool_rel. rewrite Case in C1. omega. reflexivity. reflexivity.
  pose proof (local_mmap_level3 _ _ _ _ _ C6) as Hn.
  bool_rel.
  constructor; autounfold in *; intros;
    try replace (vmid =? 0) with false by (symmetry; bool_rel; omega); simpl;
      try rewrite Hn; srewrite; try reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  destruct_zmap. inv Heq. simpl. srewrite.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  assert ((index * 8 + cbndx) @ (smmu_vmid s) =? vmid = false).
  bool_rel. red. intro. rewrite H in C1. omega. rewrite H. reflexivity.
  replace (vmid =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
  destruct_zmap. inv Heq. simpl. srewrite.
  replace (0 =? 4294967295) with false by reflexivity.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  destruct_if. bool_rel; omega. destruct_if. bool_rel. rewrite Case0 in C1. omega.
  reflexivity. reflexivity.
  destruct_zmap. inv Heq. simpl. srewrite.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  assert ((index * 8 + cbndx) @ (smmu_vmid s) =? vmid = false).
  bool_rel. red. intro. rewrite H in C1. omega. rewrite H. reflexivity.
  replace (vmid =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
  destruct_zmap. inv Heq. simpl. srewrite.
  replace (0 =? vmid) with false by (symmetry; bool_rel; omega).
  assert ((index * 8 + cbndx) @ (smmu_vmid s) =? vmid = false).
  bool_rel. red. intro. rewrite H in C1. omega. rewrite H. reflexivity.
  replace (vmid =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
  constructor; autounfold; intros; reflexivity.
  constructor; autounfold; intros; reflexivity.
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
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1; [|inv ex1; inv ex2; auto].
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq in ex1.
  simpl_hyp ex1.
  - repeat simpl_hyp ex1; try inv ex1. repeat simpl_hyp ex2; try inv ex2.
    assert(Hnp1: exists l e, pfn @ (pt n) = (0, l, e)).
    { destruct (z =? 0) eqn: Hz; bool_rel; srewrite.
      inv C7. destruct inv1. pose proof (host_flatmap _ _ _ _ C5).
      destruct (zeq z0 0). srewrite. repeat eexists.
      apply H in n. destruct n. srewrite. pose proof (host_npt_cons _ _ _ _ C5) as T.
      replace (phys_page 0 / PAGE_SIZE) with 0 in T by reflexivity.
      srewrite. repeat eexists.
      pose proof (local_mmap_level3 _ _ _ _ _ C7). rewrite H.
      rewrite Z_div_mult_full. rewrite ZMap.gss. repeat eexists.
      autounfold; omega. }
    assert(Hnp2: exists l e, pfn @ (pt n0) = (0, l, e)).
    { destruct (z2 =? 0) eqn: Hz; bool_rel; srewrite.
      inv C10. destruct inv2. pose proof (host_flatmap _ _ _ _ C8).
      destruct (zeq z3 0). srewrite. repeat eexists.
      apply H in n0. destruct n0. srewrite. pose proof (host_npt_cons _ _ _ _ C8) as T.
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
    intros. pose proof (npt_eq gfn0). repeat rewrite ZMap.gss.
    destruct (gfn0 =? pfn) eqn:Hgfn; bool_rel; srewrite.
    assert_gso. red. intro T. rewrite <- T in C3. destruct inv2. rewrite page_0_invalid in C3. autounfold in *; omega.
    repeat rewrite (ZMap.gso _ _ Hneq). rewrite owner_eq. reflexivity.
    rewrite (Hne1 _ Hgfn). rewrite (Hne2 _ Hgfn).
    destruct (gfn0 @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
    destruct (gfn0 @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
    rewrite owner_eq in H.
    assert(T1: z6 = 0 \/ z6 = gfn0).
    destruct inv1. pose proof (host_flatmap _ _ _ _ Hpt1).
    destruct (zeq z6 0). auto. apply H0 in n1. right. symmetry. apply n1.
    assert(T2: z9 = 0 \/ z9 = gfn0).
    destruct inv2. pose proof (host_flatmap _ _ _ _ Hpt2).
    destruct (zeq z9 0). auto. apply H0 in n1. right. symmetry. apply n1.
    destruct_zmap; destruct_zmap; simpl; try rewrite owner_eq; try reflexivity.
    destruct T1, T2; try omega; srewrite; try reflexivity.
    rewrite <- H. destruct_if; destruct_if; reflexivity.
    destruct T1, T2; try omega; srewrite; try reflexivity.
    destruct_if; destruct_if; reflexivity.
    assumption.
    intros. destruct_zmap. simpl. reflexivity. apply owner_eq.
    intros. destruct_zmap. simpl. reflexivity. apply count_eq.
    intros. destruct_zmap. simpl. reflexivity. apply gfn_eq.
    intros. pose proof (mem_eq pfn0) as Hmem. destruct_zmap. simpl.
    rewrite owner_eq in Hmem. srewrite; simpl_bool_eq. rewrite Hmem. reflexivity. assumption.
  - simpl_hyp ex1; inv ex1; inv ex2; try assumption.
Qed.

Lemma smmu_map_page_integ:
  forall vmid0 cbndx index iova pte s s' a b c d
    (ex: local_smmu_map_page cbndx index iova pte s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_smmu_map_page in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex. constructor; intros; reflexivity.
  assert((index * 8 + cbndx) @ (smmu_vmid s) <> vmid0).
  red. intro T. srewrite. clear C1; simpl_bool_eq. bool_rel_all; omega.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn. autounfold in *.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  destruct ((s2_owner (phys_page pte / 4096) @ (s2page s) =? 0) && (s2_count (phys_page pte / 4096) @ (s2page s) <? 16)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct ((s2_owner (phys_page pte / 4096) @ (s2page s) =? 0) && (s2_count (phys_page pte / 4096) @ (s2page s) <? 16)) eqn:Case.
  destruct_zmap. simpl. destruct_if. reflexivity. destruct_if. clear C0 C1. bool_rel_all. omega. reflexivity.
  reflexivity. reflexivity.
  destruct ((s2_owner (phys_page pte / 4096) @ (s2page s) =? 0) && (s2_count (phys_page pte / 4096) @ (s2page s) <? 16)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct ((s2_owner (phys_page pte / 4096) @ (s2page s) =? 0) && (s2_count (phys_page pte / 4096) @ (s2page s) <? 16)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct_if. rewrite Hn. assert_gso.
  red; intro. assert ((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
  autounfold in *; srewrite; bool_rel. omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
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
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  simpl_hyp ex1; [|inv ex1]. simpl_hyp ex2; [|inv ex2].
  simpl_hyp ex1. destruct b. inv ex1.
  simpl_hyp ex2. destruct b. inv ex2.
  remember (phys_page pte / PAGE_SIZE) as pfn; symmetry in Heqpfn.
  unfold observe_owner in *; simpl_bool_eq. rewrite owner_eq in ex1.
  destruct (s2_owner pfn @ (s2page s2) =? HOSTVISOR) eqn:Howner; simpl in *.
  bool_rel. pose proof (count_eq pfn) as Hcount. autounfold in Hcount.
  rewrite owner_eq, Howner in Hcount.
  autounfold in Hcount. replace (0 =? 4294967295) with false in Hcount by reflexivity.
  simpl_bool_eq. rewrite Hcount in ex1.
  destruct (s2_count pfn @ (s2page s2) <? EL2_SMMU_CFG_SIZE).
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq gfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  assert(T1: z0 = 0 \/ z0 = gfn).
  destruct inv1. pose proof (host_flatmap _ _ _ _ Hpt1).
  destruct (zeq z0 0). auto. apply H0 in n. right. symmetry. apply n.
  assert(T2: z3 = 0 \/ z3 = gfn).
  destruct inv2. pose proof (host_flatmap _ _ _ _ Hpt2).
  destruct (zeq z3 0). auto. apply H0 in n. right. symmetry. apply n.
  destruct_zmap. simpl. destruct_zmap. simpl. rewrite owner_eq. reflexivity.
  simpl_bool_eq. destruct T1, T2; try omega. srewrite.
  destruct inv2. rewrite page_0_invalid in Howner. autounfold in Howner; omega.
  srewrite. reflexivity.
  destruct_zmap. simpl. destruct T1, T2; try omega. srewrite. reflexivity.
  srewrite. reflexivity. assumption.
  intros. destruct_zmap. simpl. apply owner_eq. apply owner_eq.
  intros. destruct_zmap. simpl. rewrite owner_eq. reflexivity. apply count_eq.
  intros. destruct_zmap. simpl. apply gfn_eq. apply gfn_eq.
  intros. pose proof (mem_eq pfn) as Hmem. srewrite.
  destruct_zmap. simpl. rewrite Heq in Hmem. assumption. assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq; assumption.
  apply spt_eq; assumption.
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq; assumption.
  apply spt_eq; assumption.
  inv ex1; inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C5) as Hn2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. rewrite Hn1, Hn2. destruct_zmap. destruct_zmap. reflexivity. apply spt_eq; assumption.
  apply spt_eq; assumption.
Qed.

Lemma smmu_clear_integ:
  forall vmid0 iova cbndx index s s' a b c d
    (ex: local_smmu_clear iova cbndx index s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_smmu_clear in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex. constructor; intros; reflexivity.
  assert((index * 8 + cbndx) @ (smmu_vmid s) <> vmid0).
  red. intro T. srewrite. clear C1; simpl_bool_eq. bool_rel_all; omega.
  destruct (z0 =? 0) eqn:Hz0; bool_rel. inv C2.
  replace (phys_page 0 / 4096) with 0 by reflexivity.
  destruct inv1. rewrite page_0_invalid.
  replace (INVALID =? 0) with false by reflexivity. simpl.
  constructor; intros; reflexivity.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn. autounfold in *.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity.
  destruct ((s2_owner (phys_page z0 / 4096) @ (s2page s) =? 0) && (s2_count (phys_page z0 / 4096) @ (s2page s) >? 0)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct ((s2_owner (phys_page z0 / 4096) @ (s2page s) =? 0) && (s2_count (phys_page z0 / 4096) @ (s2page s) >? 0)) eqn:Case.
  destruct_zmap. simpl. destruct_if. reflexivity. destruct_if. clear C0 C1. bool_rel_all. omega. reflexivity.
  reflexivity. reflexivity.
  destruct ((s2_owner (phys_page z0 / 4096) @ (s2page s) =? 0) && (s2_count (phys_page z0 / 4096) @ (s2page s) >? 0)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct ((s2_owner (phys_page z0 / 4096) @ (s2page s) =? 0) && (s2_count (phys_page z0 / 4096) @ (s2page s) >? 0)) eqn:Case.
  destruct_zmap. reflexivity. reflexivity. reflexivity.
  destruct_if. rewrite Hn. assert_gso.
  red; intro. assert ((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
  autounfold in *; srewrite; bool_rel. omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
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
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  unfold observe_spt in spt_eq; simpl_bool_eq. rewrite spt_eq in ex1; try assumption.
  simpl_hyp ex1. destruct (z0 =? 0) eqn:Hz0.
  unfold observe_owner, observe_count in *; simpl_bool_eq.
  rewrite owner_eq in ex1.
  destruct (s2_owner (phys_page z0 / PAGE_SIZE) @ (s2page s2) =? HOSTVISOR) eqn: Howner.
  bool_rel; srewrite. replace (phys_page 0 / PAGE_SIZE) with 0 in Howner by reflexivity.
  destruct inv2. rewrite page_0_invalid in Howner. autounfold in Howner; omega.
  simpl in *. inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  simpl_hyp ex1; simpl_hyp ex2. simpl_hyp ex1. inv ex1. simpl_hyp ex2. inv ex2.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C3) as Hn1.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C4) as Hn2.
  unfold observe_owner, observe_count in *; simpl_bool_eq.
  rewrite owner_eq in ex1.
  destruct (s2_owner (phys_page z0 / PAGE_SIZE) @ (s2page s2) =? HOSTVISOR) eqn: Howner.
  bool_rel. pose proof (count_eq (phys_page z0 / PAGE_SIZE)) as Hcount.
  rewrite owner_eq, Howner in Hcount.
  replace (HOSTVISOR =? INVALID) with false in Hcount by reflexivity. simpl_bool_eq.
  rewrite Hcount in ex1. simpl in *.
  destruct (s2_count (phys_page z0 / PAGE_SIZE) @ (s2page s2) >? 0) eqn:Hc.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (npt_eq gfn).
  destruct (gfn @ (pt 0 @ (npts s1))) eqn:Hpt1. destruct p.
  destruct (gfn @ (pt 0 @ (npts s2))) eqn:Hpt2. destruct p.
  rewrite owner_eq in H.
  assert(T1: z2 = 0 \/ z2 = gfn).
  destruct inv1. pose proof (host_flatmap _ _ _ _ Hpt1).
  destruct (zeq z2 0). auto. apply H0 in n. right. symmetry. apply n.
  assert(T2: z5 = 0 \/ z5 = gfn).
  destruct inv2. pose proof (host_flatmap _ _ _ _ Hpt2).
  destruct (zeq z5 0). auto. apply H0 in n. right. symmetry. apply n.
  destruct_zmap; destruct_zmap; simpl; rewrite owner_eq. reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  destruct T1, T2; try omega; srewrite; try reflexivity.
  assumption.
  intros. destruct_zmap. simpl. apply owner_eq. apply owner_eq.
  intros. destruct_zmap. simpl. rewrite owner_eq. reflexivity. apply count_eq.
  intros. destruct_zmap. simpl. apply gfn_eq. apply gfn_eq.
  intros. pose proof (mem_eq pfn) as Hmem. srewrite.
  replace z with (phys_page z0 / 4096) in *.
  destruct_zmap. simpl. rewrite Heq in Hmem. assumption. assumption.
  destruct inv2. symmetry. eapply spt_cons; try eassumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  rewrite Hn1, Hn2. intros. pose proof (spt_eq gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. destruct_zmap. reflexivity. rewrite Heq in H. assumption. assumption.
Qed.

Lemma free_smmu_pgd_integ:
  forall vmid0 cbndx index s s' a b
    (ex: local_free_smmu_pgd cbndx index s = (s', false, a, b))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_free_smmu_pgd in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex. constructor; intros; reflexivity.
  assert((index * 8 + cbndx) @ (smmu_vmid s) <> vmid0).
  red. intro T. srewrite. bool_rel_all; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity; autounfold.
  destruct_zmap. destruct_if. bool_rel. srewrite. omega.
  destruct_if. bool_rel; omega. reflexivity. reflexivity.
  destruct_zmap. destruct_if. bool_rel. srewrite. omega.
  destruct_if. bool_rel; omega. reflexivity. reflexivity.
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
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq in ex1; try assumption.
  simpl_hyp ex1. inv ex1; inv ex2; auto.
  simpl_hyp ex1; [|inv ex1]. simpl_hyp ex2; [|inv ex2].
  inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (smmu_eq cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
Qed.

Lemma alloc_smmu_pgd_integ:
  forall vmid0 cbndx vmid index num s s' a b c
    (ex: local_alloc_smmu_pgd cbndx vmid index num s = (s', false, a, b, c))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_alloc_smmu_pgd in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex.
  assert((index * 8 + cbndx) @ (smmu_vmid s) <> vmid0).
  red. intro T. srewrite. bool_rel_all; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    try replace (vmid0 =? 0) with false in * by (symmetry; bool_rel; omega);
    intros; try reflexivity; autounfold.
  destruct_zmap. destruct_if. bool_rel. srewrite. omega.
  destruct_if. bool_rel_all; srewrite; omega. reflexivity. reflexivity.
  destruct_zmap. destruct_if. bool_rel. srewrite. omega.
  destruct_if. bool_rel_all; srewrite; omega. reflexivity.
  assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  constructor; intros; reflexivity.
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
  unfold observe_smmu in *. simpl_bool_eq. rewrite smmu_eq in ex1; try assumption.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
  intros. pose proof (smmu_eq cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
  intros. pose proof (spt_eq gfn cbndx0 index0 Hcb Hsmmu).
  destruct_zmap. reflexivity. assumption.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id; try assumption.
Qed.

Lemma set_vm_poweroff_integ:
  forall vmid0 vmid s s' a
    (ex: local_set_vm_poweroff vmid s = (s', a))
    (vm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_set_vm_poweroff in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    repeat rewrite (ZMap.gso _ _ vm_neq);
    intros; try reflexivity; autounfold.
  destruct_if. destruct_zmap; reflexivity.
  destruct_if. assert_gso. bool_rel. srewrite. assumption.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
  destruct_if. reflexivity.
  destruct_if. assert_gso. bool_rel. srewrite. assumption.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0). destruct_if.
  destruct_zmap. inv H. destruct (0 @ (vminfos s1)). destruct (0 @ (vminfos s2)).
  simpl in H1. simpl. rewrite H1. reflexivity. assumption.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
  intros. pose proof (state_eq vmid0). destruct_if. reflexivity.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
Qed.

Lemma verify_vm_integ:
  forall vmid0 vmid s s' a
    (ex: local_verify_vm vmid s = (s', false, a))
    (vm_neq: vmid0 <> vmid)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_verify_vm in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    repeat rewrite (ZMap.gso _ _ vm_neq);
    intros; try reflexivity; autounfold.
  destruct_if. destruct_zmap; reflexivity.
  destruct_if. assert_gso. bool_rel. srewrite. assumption.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
  destruct_if. reflexivity.
  destruct_if. assert_gso. bool_rel. srewrite. assumption.
  rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
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
  intros. pose proof (boot_eq vmid0). destruct_if.
  destruct_zmap. inv H. destruct (0 @ (vminfos s1)). destruct (0 @ (vminfos s2)).
  simpl in H1. simpl. rewrite H1. reflexivity. assumption.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
  intros. pose proof (state_eq vmid0). destruct_if. reflexivity.
  destruct_if. destruct_zmap. srewrite. inv H.
  destruct (vmid @ (vminfos s1)). destruct (vmid @ (vminfos s2)). simpl in *.
  rewrite H1. reflexivity. assumption. reflexivity.
Qed.

Lemma load_encrypted_vcpu_integ:
  forall vmid0 vmid vcpuid cregs cstates dorc logn s s' cr cs n' a
    (ex: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s = (s', false, cr, cs, n', a))
    (Hvm: valid_vm vmid0)
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_load_encryted_vcpu in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex; bool_rel_all.
  assert(vm_neq: vmid0 <> vmid). red; intro T; inv T; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    repeat rewrite (ZMap.gso _ _ vm_neq);
    intros; try reflexivity; autounfold.
  destruct_if. bool_rel; omega. destruct_if. bool_rel; inv Case0.
  rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
  destruct_if. bool_rel; omega. destruct_if. bool_rel; inv Case0.
  rewrite (ZMap.gso _ _ vm_neq). reflexivity. reflexivity.
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
  intros. destruct_zmap. pose proof (boot_eq vmid). inv H.
  destruct (vmid @ (vminfos s1)), (vmid @ (vminfos s2)). simpl in *. rewrite H1. reflexivity.
  apply boot_eq.
Qed.

Lemma load_save_encrypt_buf_integ:
  forall vmid0 vmid inbuf outbuf dorc logn s s' n' a b
    (ex: local_save_encrypt_buf vmid inbuf outbuf dorc logn s = (s', false, n', a, b))
    (Hvm: valid_vm vmid0)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_save_encrypt_buf in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex; bool_rel_all.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    intros; try reflexivity; autounfold.
  destruct_zmap. destruct_if. bool_rel; omega. reflexivity. reflexivity.
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
  intros. destruct_zmap. rewrite owner_eq. reflexivity. apply mem_eq.
Qed.

Lemma load_load_decrypt_buf_integ:
  forall vmid0 vmid inbuf dorc logn s s' n' a b c d
    (ex: local_load_decrypt_buf vmid inbuf dorc logn s = (s', false, n', a, b, c, d))
    (Hstate: vm_state (VS (vmid0 @ (vminfos s))) = VERIFIED)
    (Hvm: valid_vmid vmid)
    (Hvm: valid_vm vmid0)
    (inv1: shared_inv s),
    shared_eq vmid0 s s'.
Proof.
  intros. unfold local_load_decrypt_buf in *; simpl in *; autounfold in *.
  repeat simpl_hyp ex; inv ex; bool_rel_all.
  assert(vm_neq: vmid0 <> vmid). red; intro T; inv T; omega.
  constructor; autounfold in *; simpl in *; simpl_bool_eq;
    intros; try reflexivity; autounfold.
  destruct_if. bool_rel; omega. bool_rel. rewrite (ZMap.gso _ _ Case). reflexivity.
  destruct_if. bool_rel; omega. destruct_zmap. srewrite. simpl.
  repeat destruct_if; bool_rel; try omega. srewrite. contra. reflexivity.
  destruct_zmap. simpl. srewrite.
  repeat destruct_if; bool_rel; try omega. srewrite. contra. reflexivity.
  destruct_zmap. simpl. srewrite.
  repeat destruct_if; bool_rel; try omega. srewrite. contra. reflexivity.
  destruct_zmap. simpl. srewrite.
  repeat destruct_if; bool_rel; try omega. srewrite. contra. reflexivity.
Qed.

Lemma eqb_comm:
  forall a b, (a =? b) = (b =? a).
Proof.
  intros. destruct (a =? b) eqn:A, (b =? a) eqn:B; bool_rel; try reflexivity; try omega.
Qed.

Lemma shiftl32:
  forall n, Z.shiftl 1 (n mod 32) <> INVALID64.
Proof.
  intros. exploit (Z.mod_pos_bound n 32). omega. intros.
  repeat match goal with
         | [H: ?a <= ?n < ?b |- _] =>
           let H' := fresh "C" in
           let H1 := fresh "T" in
           first[omega| assert (H': n = a \/ a + 1 <= n < b) by omega; clear H;
                        simpl in H'; destruct H' as [H' | H1]; [srewrite; red; intro K; inversion K|]]
         end.
Qed.

Lemma vm_run_cur_same1:
  forall adt adt' (Hspec: vcpu_run_process adt = Some adt'), cur_vmid adt' = cur_vmid adt.
Proof.
  intros. unfold_spec Hspec.
  match type of Hspec with context[is_vcpu ?x] => remember x as vcpu end. symmetry in Heqvcpu.
  simpl_hyp Hspec. simpl_hyp Hspec. extract_adt C0 d0'. symmetry in Heqd0'.
  destruct p. destruct b. inv Hspec. reflexivity.
  simpl_hyp Hspec.
  autounfold in Hspec. repeat simpl_hyp Hspec; inv Hspec; reflexivity.
  repeat simpl_hyp Hspec; inv Hspec; try reflexivity.
  assert(prot: forall a b c d adt adt', prot_and_map_vm_s2pt_spec_h a b c d adt = Some adt' -> cur_vmid adt' = cur_vmid adt).
  { repeat match goal with | [H:_|-_] => clear H end.
    intros. unfold_spec H. autounfold in H.
    assert(protloop: forall n a b c d d' e f, prot_and_map_vm_loop_h n a b c d = Some (e, f, d') -> cur_vmid d' = cur_vmid d).
    { repeat match goal with | [H:_|-_] => clear H end.
      induction n. intros. simpl in H. inv H. reflexivity.
      intros. simpl in H; autounfold in H.
      repeat simpl_hyp H; inv H; simpl; apply (IHn _ _ _ _ _ _ _ C). }
    repeat simpl_hyp H; inv H; try reflexivity; simpl; eapply protloop; eassumption. }
  rewrite (prot _ _ _ _ _ _ H0). reflexivity.
  inv Hspec; reflexivity.
Qed.

Lemma vm_run_cur_same2:
  forall adt adt' (Hspec: vcpu_run_switch_to_vm adt = Some adt'), cur_vmid adt' = cur_vmid adt.
Proof.
  intros. hsimpl_func Hspec. simpl. reflexivity.
Qed.

Lemma prep_ex_vm_integ:
  forall vmid d d'
    (spec: prep_exit_vm d = Some d')
    (role: valid_role vmid d)
    (act: cur_vmid d <> vmid)
    (cur_r: HOSTVISOR < cur_vmid d < COREVISOR)
    (vcpu: valid_vcpu (cur_vcpuid d))
    (Hinv: state_inv d)
    (halt1: halt d = false)
    (halt': halt d' = false),
    local_unchanged vmid d d' /\ cur_vmid d' = cur_vmid d /\ ihost d' = ihost d /\ icore d' = icore d /\ curid d' = curid d /\ state_inv d'.
Proof.
  Local Opaque query_oracle local_set_vcpu_inactive local_set_vm_poweroff.
  intros. unfold_spec spec.
  simpl_hyp spec.
  match type of C with context[ec ?ctxt] => remember ctxt as cregs end.
  symmetry in Heqcregs; autounfold in *.
  assert(N0: cur_vmid d =? 0 = false) by (bool_rel; omega).
  assert(local_unchanged vmid d r /\ cur_vmid r = cur_vmid d /\ ihost r = ihost d /\ icore r = icore d /\ curid r = curid d /\ state_inv r).
  { simpl_hyp C. simpl_hyp C.
    inv C. simpl in *. split_and; try assumption; try reflexivity.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros. destruct_if. destruct_zmap. simpl.
    match goal with | |- _ = ?x => replace x with false by reflexivity end.
    destruct Hinv. bool_rel; assumption. reflexivity. reflexivity.
    destruct Hinv. constructor; simpl; try assumption.
    destruct_zmap; simpl. autounfold; omega. assumption.
    simpl_hyp C. unfold_spec C. autounfold in *; simpl in *.
    repeat rewrite ZMap.gss in *; simpl in *.
    repeat simpl_hyp C. inv C. simpl in *. extract_adt C4 d1'.
    assert(local_unchanged vmid d d1').
    { eapply TRANS; [|eapply ORACLE; eassumption].
      apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
      constructor; intros; reflexivity.
      intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
      intros. destruct_if. destruct_zmap. simpl. reflexivity. reflexivity. reflexivity. }
    rewrite Heqd1'. Local Transparent query_oracle.
    simpl in *. split_and; try reflexivity. rewrite <- Heqd1'. symmetry in Heqd1'.
    eapply TRANS. eapply H. rewrite <- Heqd1'.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    rewrite <- Heqd1' in C5. simpl in C5. eapply set_vm_poweroff_integ; try eassumption. auto with arith.
    eapply oracle_inv. destruct Hinv. assumption.
    destruct Hinv. constructor; simpl; try assumption.
    apply (set_vm_poweroff_inv _ _ _ _ C5). rewrite Heqd1'. simpl. apply oracle_inv. assumption.
    destruct_zmap; simpl. assumption. assumption.
    inv C. simpl in *. split_and; try reflexivity.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros. destruct_if. destruct_zmap. simpl. reflexivity. reflexivity. reflexivity.
    destruct Hinv; constructor; simpl; try assumption.
    destruct_zmap; simpl. assumption. assumption.
    repeat simpl_hyp C; inv C; simpl in *.
    split_and; try reflexivity.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros. destruct_if. destruct_zmap. simpl.
    unfold_spec C4. repeat simpl_hyp C4; inv C4; simpl; try reflexivity.
    match goal with | |- _ = ?x => replace x with false end.
    destruct Hinv. apply run_vcpu_dirty. symmetry. bool_rel. apply shiftl32.
    match goal with | |- _ = ?x => replace x with false by reflexivity end.
    destruct Hinv. apply run_vcpu_dirty. reflexivity. reflexivity.
    assert_gso. auto with zarith. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    destruct Hinv; constructor; simpl; try assumption.
    destruct_zmap; simpl.
    unfold_spec C4. repeat simpl_hyp C4; inv C4; simpl; try reflexivity. apply shiftl32.
    autounfold; omega. assumption. assumption.
    inv spec. simpl in *; contra.
    inv C. simpl in *.
    split_and; try reflexivity.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros. destruct_if. destruct_zmap. simpl. reflexivity. reflexivity. reflexivity.
    destruct Hinv; constructor; simpl; try assumption.
    destruct_zmap; simpl. assumption. assumption. }
  Local Opaque query_oracle.
  repeat simpl_hyp spec; inv spec; simpl in *. contra.
  destruct H as (Hind & cur1 & host1 & cur2 & cur3 & inv1).
  extract_adt C1 r'. assert(local_unchanged vmid r r').
  eapply ORACLE; assumption. Local Transparent query_oracle.
  srewrite. split_and.
  eapply TRANS. eapply Hind. eapply TRANS. eapply H.
  apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl in *; srewrite. eapply set_vcpu_inactive_integ; try eapply C1; autounfold; try eassumption; try omega.
  auto with zarith. rewrite <- cur3. eapply oracle_inv. destruct inv1. assumption.
  simpl. assumption. simpl. assumption. simpl. assumption. rewrite <- cur3. reflexivity.
  destruct inv1; constructor; simpl; try assumption. apply (set_vcpu_inactive_inv _ _ _ _ _ C1).
  apply oracle_inv. assumption.
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
  pose proof (shadow_ctxt_eq _ valid_vcpu2) as shadow_eq0. repeat srewrite.
  assert(Hind: obs_eq vmid r r0 /\ cur_vmid r = vmid /\ cur_vmid r0 = vmid /\ cur_vcpuid r = cur_vcpuid r0 /\ cur_vcpuid r0 = cur_vcpuid d2 /\
               shared_inv (shared r) /\ shared_inv (shared r0)).
  { simpl_hyp C. simpl_hyp C. inv C; inv C0.
    simpl in *. split_and; try assumption; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq. assumption.
    destruct inv1; assumption. destruct inv2; assumption.
    simpl_hyp C. unfold prep_hvc_spec_h in *. autounfold in *; simpl in *.
    repeat rewrite ZMap.gss in *; simpl in *.
    repeat simpl_hyp C; repeat simpl_hyp C0.
    extract_adt C6 d10'. extract_adt C8 d20'.
    assert(indisting vmid d10' d20').
    eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq. assumption.
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
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq. assumption.
    inv C; reflexivity. inv C0; simpl; assumption. inv C; inv C0; simpl; assumption. inv C0; reflexivity.
    repeat simpl_hyp C; inv C; inv C0; simpl in *; srewrite; destruct inv1; assumption.
    inv C0; simpl; destruct inv2; assumption.
    repeat simpl_hyp C; inv C; repeat simpl_hyp C0; inv C0. simpl in *.
    split_and; srewrite; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq. assumption.
    rewrite <- act2. repeat rewrite ZMap.gss. reflexivity. inv ex2. inversion halt2'.
    destruct inv1; assumption. destruct inv2; assumption.
    simpl in *. inv ex1. inv halt1'.
    repeat simpl_hyp C; inv C; inv C0; simpl in *; srewrite.
    split_and; try reflexivity.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq. assumption.
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
  eapply (set_vcpu_inactive_conf _ _ _ _ _ _ _ _ C C0). rewrite <- curid_eq0. apply oracle_inv.
  assumption. apply oracle_inv. assumption. assumption.
  autounfold. srewrite. simpl. rewrite cur1; simpl_bool_eq; reflexivity.
  autounfold. srewrite. simpl. rewrite cur2; simpl_bool_eq; reflexivity.
Qed.

Lemma set_shadow_ctxt_dirty:
  forall index val cregs cstates cregs' cstates',
    set_shadow_ctxt_specx index val cregs cstates = (cregs', cstates') ->
    index <> DIRTY ->
    dirty cstates' = dirty cstates.
Proof.
  intros. hsimpl_func H; try reflexivity.
  bool_rel; autounfold in *; omega.
Qed.

Lemma mem_load_integrity:
  forall vmid d d' gfn reg
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (Hinv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: mem_load_spec gfn reg d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros; autounfold in *.
  assert(Hcur_ne: cur_vmid d <> vmid).
  red. intro T; inv T. simpl_bool_eq. rewrite orb_comm in act; inv act.
  unfold_spec spec; autounfold in spec. repeat simpl_hyp spec; inv spec.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  repeat simpl_hyp C1; inv C1; simpl in *; bool_rel.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C3). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C3). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C3). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C3). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
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
  apply valid_host_vmid; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid; assumption. assumption.
  extract_adt ex1 d1q. extract_adt ex2 d2q.
  assert(inv_d1q: shared_inv (shared d1q)).
  rewrite Heqd1q. apply oracle_inv. destruct inv1; assumption.
  assert(inv_d2q: shared_inv (shared d2q)).
  rewrite Heqd2q. apply oracle_inv. destruct inv2; assumption.
  assert(Hind1: indisting vmid d1q d2q).
  eapply LOCAL_UNC. eapply obseq. apply ORACLE; assumption. apply ORACLE; assumption.
  apply indisting_obs_eq in Hind1. apply OBS_EQ.
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *.
  repeat srewrite. destruct Hind1. duplicate sh_eq. destruct D; autounfold in *; repeat (srewrite; simpl in *; simpl_bool_eq); clear_hyp.
  assert(z0 = z1).
  simpl_hyp C. pose proof (npt_eq z). simpl_hyp C; simpl_hyp C2. destruct p; destruct p0.
  simpl_hyp C; contra. simpl_hyp C2; contra. rewrite owner_eq in C2, H.
  simpl_hyp C; simpl_hyp C2. inv H. inv C; inv C2.
  pose proof (mem_eq z4). rewrite owner_eq in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). rewrite C11 in H. assumption.
  rewrite <- H in C11. destruct inv_d2q. rewrite page_0_invalid in C11. inversion C11.
  rewrite H in C12. destruct inv_d2q. rewrite page_0_invalid in C12. inversion C12.
  inv C; inv C2. reflexivity.
  pose proof (npt_eq z) as n1. simpl_hyp C; simpl_hyp C2. simpl_hyp C; simpl_hyp C2. simpl_hyp C; simpl_hyp C2.
  simpl_hyp C; simpl_hyp C2; contra. simpl_hyp C; simpl_hyp C2; contra.
  destruct p; destruct p0.
  destruct inv_d1q; destruct inv_d2q.
  pose proof (vm_iso (cur_vmid d1) z z6 z7 z3 C10) as vmi1.
  pose proof (vm_iso0 (cur_vmid d1) z z4 z5 z2 C9) as vmi2.
  inv n1. pose proof (count_eq z4). pose proof (owner_eq z4).
  exploit vmi1; autounfold in *; bool_rel. destruct role1' as [R|[R1 R2]]. contra. apply R1.
  destruct role1' as [R|[R1 R2]]. contra. rewrite R2. auto with zarith. assumption. assumption.
  intros so1.
  exploit vmi2; autounfold in *; bool_rel. destruct role2' as [R|[R1 R2]]. contra. apply R1.
  destruct role2' as [R|[R1 R2]]. contra. rewrite R2. auto with zarith. assumption. assumption.
  intros so2.
  rewrite so1, so2 in H. replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  rewrite H in C2. simpl_hyp C.
  inv C; inv C2.
  pose proof (mem_eq z4). rewrite so1, so2 in H1. simpl_bool_eq. assumption.
  inv C; inv C2. reflexivity.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  inv H. rewrite shadow_ctxt_eq in C4. rewrite C4 in C5. inv C5.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite shadow_ctxt_eq. reflexivity. destruct inv2. assumption.
  apply shadow_ctxt_eq. assumption.
  intros. destruct_zmap. simpl. reflexivity. apply dirty_eq; assumption.
  destruct inv2; assumption.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma mem_load_confidentiality_restore:
  forall vmid gfn reg d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = false)
    (act2: active vmid d2 = false)
    (act1': active vmid d1' = true)
    (act2': active vmid d2' = true)
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
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *.
  contra.
Qed.

Lemma mem_store_integrity:
  forall vmid d d' gfn reg
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (Hinv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: mem_store_spec gfn reg d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros; autounfold in *.
  assert(Hcur_ne: cur_vmid d <> vmid).
  red. intro T; inv T. simpl_bool_eq. rewrite orb_comm in act; inv act.
  unfold_spec spec; autounfold in spec. repeat simpl_hyp spec; inv spec.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  assert(inv_dq: shared_inv (shared dq)).
  rewrite Heqdq. apply oracle_inv. destruct Hinv; assumption.
  simpl in *; bool_rel. apply SAME_OB. simpl in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold in *; intros; bool_rel; simpl; srewrite; try reflexivity.
  simpl in *. destruct inv_dq. pose proof (host_flatmap z z1 z2 z0 C2 C4). destruct H; subst.
  destruct_zmap. rewrite C5. replace (0 =? vmid) with false. reflexivity.
  symmetry; bool_rel; omega. reflexivity.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  assert(inv_dq: shared_inv (shared dq)).
  rewrite Heqdq. apply oracle_inv. destruct Hinv; assumption.
  simpl in *; bool_rel. apply SAME_OB. simpl in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold in *; intros; bool_rel; simpl; srewrite; try reflexivity.
  simpl in *. destruct inv_dq. pose proof (vm_iso (cur_vmid d) z z1 z2 z0 C3).
  exploit H. autounfold.
  destruct Hinv. destruct (ihost d) eqn:Hh. rewrite valid_host_vmid in C1.
  autounfold in C1; contra. reflexivity. assumption. apply valid_vm_vmid. reflexivity. assumption.
  rewrite C2. autounfold. omega. assumption. assumption.
  simpl. intros so1. destruct_zmap.
  rewrite so1. replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; assumption).
  reflexivity. reflexivity.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
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
  apply valid_host_vmid; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid; assumption. assumption.
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
  destruct Hind1. duplicate sh_eq. destruct D. autounfold in *.
  pose proof (npt_eq z). srewrite; simpl_bool_eq; simpl in *.
  simpl_hyp ex1. simpl_hyp ex2. destruct p, p0. simpl_hyp ex1; contra. simpl_hyp ex2; contra.
  rewrite owner_eq in ex1, H. bool_rel.
  simpl_hyp ex1; simpl_hyp ex2. inv H. inv ex1; inv ex2; simpl in *.
  pose proof (mem_eq z4). rewrite owner_eq in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). rewrite C8 in H.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite owner_eq. rewrite shadow_ctxt_eq. reflexivity.
  destruct inv2. assumption. apply mem_eq.
  rewrite H in C7. destruct inv_d2q. rewrite page_0_invalid in C7. inversion C7.
  rewrite <- H in C8. destruct inv_d2q. rewrite page_0_invalid in C8. inversion C8.
  inv ex1; inv ex2. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl_hyp ex1; simpl_hyp ex2. destruct Hind1. duplicate sh_eq. destruct D.
  autounfold in *. pose proof (npt_eq z) as n1.
  replace (vmid =? 0) with false in n1 by (symmetry; bool_rel; assumption). simpl in n1.
  simpl_hyp ex1; simpl_hyp ex2. destruct p, p0. simpl_hyp ex1; simpl_hyp ex2; contra. inv n1.
  pose proof (count_eq z4). pose proof (owner_eq z4).
  destruct inv_d1q; destruct inv_d2q.
  pose proof (vm_iso (cur_vmid d1) z z4 z3 z0 C5) as vmi1.
  pose proof (vm_iso0 (cur_vmid d1) z z4 z5 z1 C6) as vmi2.
  simpl_hyp ex1; simpl_hyp ex2; contra.
  exploit vmi1; autounfold in *; bool_rel. destruct role1' as [R|[R1 R2]]. contra. apply R1.
  destruct role1' as [R|[R1 R2]]. contra. simpl. repeat simpl_hyp ex1; inv ex1; simpl in R2; rewrite R2.
  auto with zarith. auto with zarith. assumption. assumption.
  intros so1.
  exploit vmi2; autounfold in *; bool_rel. destruct role2' as [R|[R1 R2]]. contra. apply R1.
  destruct role2' as [R|[R1 R2]]. contra. simpl. repeat simpl_hyp ex2; inv ex2; simpl in R2; rewrite R2.
  auto with zarith. auto with zarith. assumption. assumption.
  intros so2.
  rewrite so1, so2 in H. replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  simpl in H. rewrite H in ex1. simpl_hyp ex1.
  pose proof (mem_eq z4). rewrite so1, so2 in H1. simpl_bool_eq.
  inv ex1; inv ex2.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. simpl in so1, so2. rewrite so1, so2, shadow_ctxt_eq. simpl_bool_eq.
  simpl. simpl in cur_vcpu_eq. rewrite Hcur_eq2 in cur_vcpu_eq. simpl_bool_eq. rewrite cur_vcpu_eq.
  reflexivity. destruct inv1. assumption. apply mem_eq.
  simpl. simpl in regs_eq. srewrite. simpl_bool_eq; simpl in regs_eq. assumption.
  srewrite; simpl in cur_vcpu_eq; simpl_bool_eq. rewrite Hcur_eq2 in cur_vcpu_eq. simpl_bool_eq. assumption.
  inv ex1; inv ex2; constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl. simpl in regs_eq. srewrite. simpl_bool_eq; simpl in regs_eq. assumption.
  srewrite; simpl in cur_vcpu_eq; simpl_bool_eq. rewrite Hcur_eq2 in cur_vcpu_eq. simpl_bool_eq. assumption.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma mem_store_confidentiality_restore:
  forall vmid gfn reg d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = false)
    (act2: active vmid d2 = false)
    (act1': active vmid d1' = true)
    (act2': active vmid d2' = true)
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
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *;
  contra.
Qed.

Lemma dev_load_integrity:
  forall vmid d d' gfn reg cbndx index
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (Hinv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: dev_load_spec gfn reg cbndx index d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros; autounfold in *.
  assert(Hcur_ne: cur_vmid d <> vmid).
  red. intro T; inv T. simpl_bool_eq. rewrite orb_comm in act; inv act.
  unfold_spec spec; autounfold in spec. repeat simpl_hyp spec; inv spec.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  repeat simpl_hyp C4; inv C4; simpl in *; bool_rel.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C6). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C6). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C6). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
  apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
  rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap. simpl.
  erewrite (set_shadow_ctxt_dirty _ _ _ _ _ _ C6). reflexivity.
  autounfold; omega. reflexivity. reflexivity.
Qed.

Ltac keep_only H :=
  generalize H;
  repeat match goal with
         | [H: _ |- _] => clear H
         end;
  intro H.

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
  apply valid_host_vmid; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid; assumption. assumption.
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
  repeat srewrite. destruct Hind1. duplicate sh_eq. destruct D; autounfold in *; repeat (srewrite; simpl in *; simpl_bool_eq); clear_hyp.
  assert(z0 = z1).
  simpl_hyp C. exploit (spt_eq z cbndx index); try (split; assumption). intros Hspt.
  bool_rel. autounfold in Hspt. rewrite C, C4 in Hspt. simpl_bool_eq.
  simpl_hyp C5. rewrite Hspt in C5. simpl_hyp C5. simpl_hyp C5; contra.
  rewrite owner_eq in C5. pose proof (mem_eq z2). rewrite owner_eq in H.
  replace (cur_vmid d1) with 0 in H by (symmetry; bool_rel; assumption). simpl_hyp C5.
  inv C5; inv C8. assumption. inv C5; inv C8; reflexivity.
  simpl_hyp C5; simpl_hyp C8; contra.
  rewrite Hspt in C5. simpl_hyp C5. simpl_hyp C5; contra.
  destruct inv_d1q; destruct inv_d2q.
  exploit (smmu_iso (cur_vmid d1) cbndx index z z2 z3); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. keep_only role1'. omega. simpl; intros (so1 & sg1).
  exploit (smmu_iso0 (cur_vmid d1) cbndx index z z2 z3); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. keep_only role2'; omega.  simpl; intros (so2 & sg2).
  pose proof (count_eq z2). rewrite so1, so2 in H.
  replace (cur_vmid d1 =? 4294967295) with false in H. simpl_bool_eq.
  autounfold in H; rewrite C, C4 in H. simpl_bool_eq.
  replace (cur_vmid d1 =? 4294967295) with false in H by (symmetry; bool_rel; omega).
  rewrite H in C5. simpl_hyp C5; contra. simpl_hyp C8; contra.
  simpl_hyp C5; simpl_hyp C8; contra.
  inv C5; inv C8.
  pose proof (mem_eq z2). rewrite so1, so2 in H0. simpl_bool_eq.
  autounfold in H0; rewrite C, C4 in H0. simpl_bool_eq. assumption.
  inv C5; inv C8. reflexivity.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  inv H. rewrite shadow_ctxt_eq in C7. rewrite C7 in C9. inv C9.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite shadow_ctxt_eq. reflexivity. destruct inv2. assumption.
  apply shadow_ctxt_eq. assumption.
  intros. destruct_zmap. simpl. reflexivity. apply dirty_eq; assumption.
  destruct inv2; assumption.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma dev_load_confidentiality_restore:
  forall vmid gfn reg cbndx index d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = false)
    (act2: active vmid d2 = false)
    (act1': active vmid d1' = true)
    (act2': active vmid d2' = true)
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
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *.
  contra.
Qed.

Lemma dev_store_integrity:
  forall vmid d d' gfn reg cbndx index
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (Hinv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: dev_store_spec gfn reg cbndx index d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros; autounfold in *.
  assert(Hcur_ne: cur_vmid d <> vmid).
  red. intro T; inv T. simpl_bool_eq. rewrite orb_comm in act; inv act.
  unfold_spec spec; autounfold in spec. repeat simpl_hyp spec; inv spec.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  assert(inv_dq: shared_inv (shared dq)).
  rewrite Heqdq. apply oracle_inv. destruct Hinv; assumption.
  simpl in *; bool_rel. apply SAME_OB. simpl in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold in *; intros; bool_rel; simpl; srewrite; try reflexivity.
  simpl in C7. destruct_zmap. rewrite C7. replace (0 =? vmid) with false. reflexivity.
  symmetry; bool_rel. simpl in C4. omega. reflexivity.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  assert(inv_dq: shared_inv (shared dq)).
  rewrite Heqdq. apply oracle_inv. destruct Hinv; assumption.
  simpl in *; bool_rel. apply SAME_OB. simpl in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold in *; intros; bool_rel; simpl; srewrite; try reflexivity.
  simpl in *. destruct inv_dq. bool_rel_all0.
  exploit (smmu_iso (cur_vmid d) cbndx index z z0 z1);
    try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. rewrite C5. destruct Hinv. autounfold in *.
  destruct (zeq (cur_vmid d) 0). left; assumption. right. split.
  destruct (ihost d) eqn:Hihost. rewrite valid_host_vmid in n; contra.
  reflexivity. assumption. apply valid_vm_vmid. reflexivity. assumption. auto with zarith.
  intros (so1 & sg1). autounfold in *. rewrite C3 in so1. destruct_zmap.
  rewrite so1. replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; assumption).
  reflexivity. reflexivity.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
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
  apply valid_host_vmid; assumption. assumption.
  assert(Hcur_eq2: cur_vmid d2 = vmid).
  apply orb_true_iff in act2. destruct act2; bool_rel_all0.
  destruct inv2. rewrite Hcond.
  apply valid_host_vmid; assumption. assumption.
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
  destruct Hind1. duplicate sh_eq. destruct D. autounfold in *.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex2; contra.
  exploit (spt_eq z cbndx index). bool_rel_all0; omega. bool_rel_all0; omega.
  intro Hspt.
  simpl_hyp ex1. srewrite; simpl_bool_eq; simpl in *.
  rewrite Hspt in ex1. simpl_hyp ex1. simpl_hyp ex1; contra.
  rewrite owner_eq in ex1.
  simpl_hyp ex1. inv ex1; inv ex2; simpl in *.
  pose proof (mem_eq z0). rewrite owner_eq in H. bool_rel; srewrite; simpl_bool_eq.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite owner_eq. rewrite shadow_ctxt_eq. reflexivity.
  destruct inv2. assumption. apply mem_eq.
  inv ex1; inv ex2. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  simpl_hyp ex1; simpl_hyp ex2.
  bool_rel_all0. autounfold in *. simpl in *. srewrite. rewrite Hspt in ex1.
  simpl_hyp ex1. simpl_hyp ex1; contra.
  destruct inv_d1q; destruct inv_d2q. autounfold in *.
  simpl_hyp ex1; simpl_hyp ex2; contra.
  exploit (smmu_iso (cur_vmid d1) cbndx index z z0 z1); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. omega. rewrite Hcur_eq1. repeat simpl_hyp ex1; inv ex1. keep_only role1'. simpl in *. omega.
  srewrite; keep_only role1'; simpl in *. omega.
  simpl; intros (so1 & sg1). autounfold in *; rewrite C4 in so1.
  exploit (smmu_iso0 (cur_vmid d1) cbndx index z z0 z1); try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold. omega. rewrite Hcur_eq1. repeat simpl_hyp ex2; inv ex2. keep_only role2'. simpl in *. omega.
  srewrite; keep_only role2'; simpl in *. omega.
  simpl; intros (so2 & sg2). autounfold in *; rewrite C5 in so2.
  pose proof (count_eq z0). rewrite so1, so2 in H.
  replace (vmid =? 4294967295) with false in H. simpl_bool_eq.
  rewrite H in ex1. simpl_hyp ex1. inv ex1; inv ex2.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  destruct sh_eq.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. destruct_zmap. rewrite so1, so2, shadow_ctxt_eq. reflexivity.
  destruct inv2. assumption. apply mem_eq.
  intros. rewrite <- Hcur_eq1. replace (cur_vmid d1 =? 0) with false. reflexivity.
  symmetry; bool_rel; omega. intros. rewrite <- Hcur_eq1.
  replace (cur_vmid d1 =? 0) with false. rewrite Hcur_eq1. apply core_data_log_eq.
  symmetry; bool_rel; omega.
  inv ex1; inv ex2; constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  intros. rewrite <- Hcur_eq1. replace (cur_vmid d1 =? 0) with false. reflexivity.
  symmetry; bool_rel; omega. intros. rewrite <- Hcur_eq1.
  replace (cur_vmid d1 =? 0) with false. rewrite Hcur_eq1. apply core_data_log_eq.
  symmetry; bool_rel; omega.
  symmetry; bool_rel. destruct role1' as [R|[R1 R2]]. contra.
  generalize R1. repeat match goal with | [H:_ |- _] => clear H end.
  intros. omega.
  rewrite Heqd1q. autounfold; simpl; assumption.
  rewrite Heqd2q. autounfold; simpl; assumption.
Qed.

Lemma dev_store_confidentiality_restore:
  forall vmid gfn reg cbndx index d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = false)
    (act2: active vmid d2 = false)
    (act1': active vmid d1' = true)
    (act2': active vmid d2' = true)
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
  repeat simpl_hyp ex1; inv ex1; repeat simpl_hyp ex2; inv ex2; simpl in *;
  contra.
Qed.
```
