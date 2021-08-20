# NoninterferenceLemma1

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
Local Opaque query_oracle_h.

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
      inv C3. destruct inv1. pose proof (host_flatmap0 _ _ _ _ C1).
      destruct (zeq z0 0). srewrite. repeat eexists.
      apply H in n. destruct n. srewrite. pose proof (host_npt_cons0 _ _ _ _ C1) as T.
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
    destruct_zmap. rewrite <- Heq in Hcond. destruct inv1. rewrite page_0_invalid0 in Hcond.
    autounfold in Hcond; omega. destruct_if. bool_rel.
    destruct (zeq z0 0). srewrite. destruct_if; reflexivity.
    destruct inv1. assert (pfn = z0). eapply host_flatmap0; try eassumption.
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
  destruct inv1. rewrite page_0_invalid0.
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

Lemma host_vcpu_run_integrity:
  forall vmid d d'
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (Hinv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: host_vcpu_run_handler_spec d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros. unfold_spec spec.
  repeat simpl_hyp spec; contra; try solve[simpl_some; rewrite <- spec in halt'; inversion halt'; contra].
  clear_hyp.
  assert(cur_host: cur_vmid d = HOSTVISOR).
  { destruct Hinv. apply valid_host_vmid0; assumption. }
  assert(vm_nh: vmid <> HOSTVISOR).
  { autounfold in *. intro T. rewrite T in *. srewrite. inversion act. }
  remember (vcpu_run_swith_to_core d) as d1.
  symmetry in Heqd1.
  assert(ind1: local_unchanged vmid d d1 /\ icore d1 = true /\ exists vmid0, cur_vmid d1 = vmid0 /\ valid_vm vmid0 /\ vmid <> vmid0 /\ shared_inv (shared d1)).
  { unfold vcpu_run_swith_to_core in *.
    repeat simpl_hyp Heqd1. simpl in *.
    assert(valid_vm (cur_vmid d1)) by (rewrite <- Heqd1; simpl; autounfold in *; bool_rel_all0; omega).
    assert(cur_vmid d' = cur_vmid d1).
    { pose proof (vm_run_cur_same2 _ _ spec) as T. rewrite T. apply vm_run_cur_same1. assumption. }
    autounfold in *.
    assert(0 =? vmid = false) by (bool_rel; omega). assert(vmid =? 0 = false) by (bool_rel; omega).
    assert(vmid <> cur_vmid d1).
    { autounfold in *. srewrite. simpl in act'. bool_rel. omega. }
    assert((cur_vmid d1) =? vmid = false) by (bool_rel; omega). assert(vmid =? (cur_vmid d1) = false) by (bool_rel; omega).
    rewrite <- Heqd1. simpl.  split_and. apply SAME_OB. rewrite <- Heqd1 in *; simpl in H4, H5.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; simpl; reflexivity.
    intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
    bool_rel_all0. rewrite <- Heqd1 in *; simpl in H4, H5. eexists; split_and; try reflexivity; try omega.
    destruct Hinv; assumption. rewrite <- Heqd1 in *. simpl in *. contra. }
  assert(Hvmid1: valid_vm (cur_vmid d1)).
  { unfold_spec Heqd1. repeat simpl_hyp Heqd1; inv Heqd1. autounfold in *; simpl in *. bool_rel_all; omega.
    inversion C2. }
  destruct ind1 as (ind1 & ic1 & vmid0 & cur1 & vmid0_valid & vmid_nz & Hinv1).
  assert(ind2: local_unchanged vmid d1 r).
  { autounfold in *.
    assert(0 =? vmid = false) by (bool_rel; omega). assert(vmid =? 0 = false) by (bool_rel; omega).
    assert(vmid0 =? vmid = false) by (bool_rel; omega). assert(vmid =? vmid0 = false) by (bool_rel; omega).
    unfold_spec C3; simpl_hyp C3.
    match type of C5 with
    | context[is_vcpu ?v] => remember v as vcpuid0; clear Heqvcpuid0
    end.
    assert(T: valid_vcpu vcpuid0) by (autounfold in *; bool_rel_all0; split; assumption).
    extract_adt C3 d0'; symmetry in Heqd0'.
    assert(local_unchanged vmid d1 d0').
    eapply TRANS; [apply SAME_OB | eapply ORACLE; symmetry; eassumption].
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. simpl. destruct_if. bool_rel. rewrite <- Case. rewrite (ZMap.gso _ _ H2). reflexivity. reflexivity.
    simpl_hyp C3. destruct p. destruct b. inv C3. simpl in C4; contra.
    autounfold in C3; simpl_hyp C3. extract_adt C3 d1'; symmetry in Heqd1'.
    assert(local_unchanged vmid d0' d1').
    eapply TRANS; [apply SAME_OB | eapply ORACLE; symmetry; eassumption].
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    eapply set_vcpu_active_integ; try eapply C6; try eassumption.
    rewrite <- Heqd0'. apply oracle_inv. simpl. destruct Hinv. assumption.
    extract_adt C3 d2'; symmetry in Heqd2'.
    assert(local_unchanged vmid d1' d2').
    eapply TRANS; [apply SAME_OB | eapply ORACLE; symmetry; eassumption].
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    assert_gso. bool_rel; omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    repeat simpl_hyp C3. inversion C3.
    eapply TRANS. apply H3. eapply TRANS. apply H4. eapply TRANS. apply H5.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    eapply TRANS. apply H3. inversion C3.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    eapply set_vcpu_active_integ; try eapply C6; try eassumption.
    rewrite <- Heqd0'. apply oracle_inv. simpl. destruct Hinv. assumption.
    intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). rewrite <- Heqd2', <- Heqd1'. reflexivity.
    assert_gso. bool_rel; omega. rewrite (ZMap.gso _ _ Hneq). rewrite <- Heqd2', <- Heqd1'. simpl.
    rewrite (ZMap.gso _ _ Hneq). reflexivity.
    eapply TRANS. apply H3. eapply TRANS. apply H4. inversion C3.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity.
    repeat simpl_hyp C3.
    exploit (prot_and_map_integ vmid _ _ _ _ _ _ C3); autounfold. assumption. destruct role. contra. apply H4. omega.
    simpl. eapply set_vcpu_active_inv; try eassumption. rewrite <- Heqd0'. apply oracle_inv. simpl. destruct Hinv; assumption.
    simpl. reflexivity. assumption. intro K. eapply TRANS. apply H3. eapply TRANS; [|eapply K].
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    eapply set_vcpu_active_integ; try eapply C6; try eassumption.
    rewrite <- Heqd0'. apply oracle_inv. simpl. destruct Hinv. assumption.
    intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity.
    assert_gso. bool_rel; omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros; destruct_if. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
    eapply TRANS. eapply H3. inversion C3.
    apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    eapply set_vcpu_active_integ; try eapply C6; try eassumption.
    rewrite <- Heqd0'. apply oracle_inv. simpl. destruct Hinv. assumption.
    intros. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity.
    assert_gso. bool_rel; omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    intros; destruct_if. assert_gso. destruct Hinv. autounfold in *; bool_rel; omega.
    rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
    inv C3; inversion C4. }
  apply (TRANS _ _ _ r). apply (TRANS _ _ _ d1). assumption. assumption.
  pose proof (vm_run_cur_same1 _ _ C3).
  hsimpl_func spec. apply SAME_OB.
  constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  replace (cur_vmid (vcpu_run_swith_to_core d) =? vmid) with false. reflexivity.
  symmetry. bool_rel. omega.
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
    destruct Hinv. apply run_vcpu_dirty0. symmetry. bool_rel. apply shiftl32.
    match goal with | |- _ = ?x => replace x with false by reflexivity end.
    destruct Hinv. apply run_vcpu_dirty0. reflexivity. reflexivity.
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

Lemma vm_exit_pre_integ:
  forall vmid d d' r
    (spec: vm_exit_pre_process d = Some (d', r))
    (role: valid_role vmid d)
    (act: cur_vmid d <> vmid)
    (cur_r: HOSTVISOR < cur_vmid d < COREVISOR)
    (Hinv: state_inv d)
    (ihost1: ihost d = false)
    (halt1: halt d = false)
    (halt': halt d' = false),
    local_unchanged vmid d d' /\ cur_vmid d' = cur_vmid d /\ ihost d' = false /\ curid d' = curid d /\
    (r <> 0 -> icore d' = true /\ state_inv d').
Proof.
  intros. unfold_spec spec.
  assert(curv: valid_vcpu (cur_vcpuid d)).
  { destruct Hinv. assumption. }
  autounfold in curv.
  simpl_hyp spec. simpl_hyp spec.
  unfold_spec C0. simpl_hyp C0. inv C0. simpl_bool_eq. inv spec.
  simpl. split_and; try reflexivity; try assumption.
  apply SAME_OB. assert(cur_vmid d =? vmid = false) by (bool_rel; assumption).
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; simpl; reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  intro T. contra.
  simpl_hyp C0. simpl_hyp C0. simpl_hyp C0. simpl_hyp C0. destruct p. inv C0.
  simpl_bool_eq. inv spec. simpl in halt'.
  exploit (grant_integ vmid _ _ _ _ _ _ C4); simpl; try reflexivity; try assumption.
  destruct Hinv; constructor; simpl; try assumption; intros; contra.
  rewrite ZMap.gss. simpl. assumption.
  intros (lc1 & ? & ? & ? & ?). split_and; try assumption.
  eapply TRANS; [|eapply TRANS; [eapply lc1|]].
  apply SAME_OB. assert(cur_vmid d =? vmid = false) by (bool_rel; assumption).
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  apply SAME_OB. assert(cur_vmid d =? vmid = false) by (bool_rel; assumption).
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity. intro; contra.
  simpl_hyp C0. simpl_hyp C0. simpl_hyp C0. destruct p.
  inv C0. simpl_bool_eq. inv spec. simpl in halt'.
  exploit (revoke_integ vmid _ _ _ _ _ _ C5); simpl; try reflexivity; try assumption.
  destruct Hinv; constructor; simpl; try assumption; intros; contra.
  rewrite ZMap.gss. simpl. assumption.
  intros (lc1 & ? & ? & ? & ?). split_and; try assumption.
  eapply TRANS; [|eapply TRANS; [eapply lc1|]].
  apply SAME_OB. assert(cur_vmid d =? vmid = false) by (bool_rel; assumption).
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  apply SAME_OB. assert(cur_vmid d =? vmid = false) by (bool_rel; assumption).
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity. intro; contra.
  destruct p. inv C0. replace (1 =? 0) with false in spec by (symmetry; bool_rel; omega).
  repeat simpl_hyp spec; inv spec.
  exploit (prep_ex_vm_integ vmid _ _ C0); simpl; try reflexivity; try assumption.
  destruct Hinv; constructor; simpl; try assumption; intros; contra.
  rewrite ZMap.gss. simpl; assumption.
  intros (lc1 & ? & ? & ? & ? & ?). split_and; try assumption.
  eapply TRANS; [|eapply lc1]. apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; omega). reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  srewrite; reflexivity. intros. split. srewrite; reflexivity. assumption.
  destruct p. inv C0. simpl_bool_eq; simpl in *. inv spec; simpl.
  split_and; try reflexivity; try assumption; try intros; contra.
  apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; omega). reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  repeat simpl_hyp spec; inv spec.
  exploit (prep_ex_vm_integ vmid _ _ C1); simpl; try reflexivity; try assumption.
  destruct Hinv; constructor; simpl; try assumption; intros; contra.
  rewrite ZMap.gss. simpl; assumption.
  intros (lc1 & ? & ? & ? & ? & ?). split_and; try assumption.
  eapply TRANS; [|eapply lc1]. apply SAME_OB.
  constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; omega). reflexivity.
  intros. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
  intros. destruct_if. destruct_zmap; simpl; reflexivity. reflexivity.
  srewrite; reflexivity. intros. split. srewrite; reflexivity. assumption.
  simpl in *. contra.
Qed.

Lemma vm_exit_integrity:
  forall vmid d d'
    (role: valid_role vmid d)
    (role': valid_role vmid d')
    (act: active vmid d = false)
    (act': active vmid d' = false)
    (inv: state_inv d)
    (halt0: halt d = false)
    (halt': halt d' = false)
    (spec: vm_exit_handler_spec d = Some d'),
    local_unchanged vmid d d'.
Proof.
  intros. unfold_spec spec.
  simpl_hyp spec; simpl_hyp spec; simpl_hyp spec; contra.
  assert(cur_r: HOSTVISOR < cur_vmid d < COREVISOR).
  { destruct inv. apply valid_vm_vmid0; assumption. }
  assert(vmid_nz: vmid <> cur_vmid d).
  { autounfold in *. intro T. rewrite <- T in *. simpl_bool_eq.
    rewrite orb_comm in act. inversion act. }
  repeat simpl_hyp spec; inv spec; contra.
  exploit(vm_exit_pre_integ vmid _ _ _ C2); try assumption; try omega.
  intros (? & cur & ih & ? & cic). assumption.
  autounfold in *; simpl in *.
  exploit(vm_exit_pre_integ vmid _ _ _ C2); try assumption; try omega.
  intros (lc & cur & ih & crd & cic).
  bool_rel. apply cic in C5. destruct C5.
  assert(host: vmid <> 0).
  { red. intro T. rewrite T in act'. simpl_bool_eq. inversion act'. }
  eapply TRANS. eapply lc.
  assert(vmid =? cur_vmid d = false) by (bool_rel; omega).
  assert(cur_vmid d =? vmid = false) by (bool_rel; omega).
  assert(vmid =? 0 = false) by (bool_rel; omega).
  assert(0 =? vmid = false) by (bool_rel; omega).
  apply SAME_OB. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  constructor; intros; reflexivity.
  simpl in act'. rewrite act'. reflexivity.
  simpl in act'. rewrite eqb_comm. rewrite act'. reflexivity.
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
  simpl in *. destruct inv_dq. pose proof (host_flatmap0 z z1 z2 z0 C2 C4). destruct H; subst.
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
  simpl in *. destruct inv_dq. pose proof (vm_iso0 (cur_vmid d) z z1 z2 z0 C3).
  exploit H. autounfold.
  destruct Hinv. destruct (ihost d) eqn:Hh. rewrite valid_host_vmid0 in C1.
  autounfold in C1; contra. reflexivity. assumption. apply valid_vm_vmid0. reflexivity. assumption.
  rewrite C2. autounfold. omega. assumption.
  simpl. intros (so1 & sg1). destruct_zmap.
  rewrite so1. replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; assumption).
  reflexivity. reflexivity.
  extract_adt C1 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
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
  exploit (smmu_iso0 cbndx index z z0 z1);
    try (autounfold; first [eassumption|split; eassumption|bool_rel; eassumption]).
  autounfold; rewrite C3. destruct Hinv. autounfold in *; omega.
  intros (so1 & sg1). autounfold in *. rewrite C3 in so1. destruct_zmap.
  rewrite so1. replace (cur_vmid d =? vmid) with false by (symmetry; bool_rel; assumption).
  reflexivity. reflexivity.
  extract_adt C3 dq. eapply TRANS. eapply ORACLE; eassumption.
  apply SAME_OB. constructor; intros; try reflexivity.
  constructor; intros; try reflexivity.
Qed.
```
