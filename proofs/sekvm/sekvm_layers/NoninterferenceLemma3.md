# NoninterferenceLemma3

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
  pose proof (owner_eq0 pfn) as Howner.
  pose proof (count_eq0 pfn) as Hcount.
  pose proof (gfn_eq0 pfn) as Hgfn.
  repeat simpl_hyp ex1; repeat simpl_hyp ex2; inv ex1; inv ex2;
    bool_rel; srewrite; try replace (0 =? vmid) with false in * by (symmetry; bool_rel; omega);
      try replace (0 =? 4294967295) with false in * by (symmetry; bool_rel; omega); simpl in *.
  split; auto.
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    try assumption.
  assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. reflexivity. apply owner_eq0.
  intros. destruct_zmap. reflexivity. apply count_eq0.
  intros. destruct_zmap. reflexivity. apply gfn_eq0.
  intros. destruct_zmap. reflexivity. apply mem_eq0.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  bool_rel_all; srewrite. omega.
  repeat rewrite zmap_set_id. split; auto.
  destruct s1; destruct s2; simpl in *; assumption.
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
  destruct in_range_n in *. rewrite Hn1, Hn2. reflexivity. srewrite. apply npt_eq0.
  bool_rel; srewrite; try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
  constructor; autounfold in *; simpl in *; simpl_bool_eq; try rewrite zmap_set_id;
    try replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega);
    try assumption.
  intros. repeat rewrite ZMap.gss.
  pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn1.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn2.
  rewrite Hn1, Hn2. destruct_zmap. reflexivity. apply npt_eq0.
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
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
  intros. pose proof (state_eq0 vmid0).
  destruct_if. reflexivity. destruct_if. bool_rel. srewrite.
  repeat rewrite ZMap.gss. simpl. inv H. reflexivity. reflexivity.
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
  intros. pose proof (boot_eq0 vmid0).
  destruct_zmap. simpl. rewrite Heq in H. assumption. assumption.
Qed.

Lemma host_vcpu_run_confidentiality_restore:
  forall vmid d1 d2 d1' d2'
    (role1: valid_role vmid d1)
    (role2: valid_role vmid d2)
    (role1': valid_role vmid d1')
    (role2': valid_role vmid d2')
    (act1: active vmid d1 = false)
    (act2: active vmid d2 = false)
    (act1': active vmid d1' = true)
    (act2': active vmid d2' = true)
    (inv1: invariant d1)
    (inv2: invariant d2)
    (halt1: halt d1 = false)
    (halt2: halt d2 = false)
    (halt1': halt d1' = false)
    (halt2': halt d2' = false)
    (ex1: host_vcpu_run_handler_spec d1 = Some d1')
    (ex2: host_vcpu_run_handler_spec d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  Local Opaque prot_and_map_vm_s2pt_spec Z.eqb.
  intros. unfold_spec ex1; unfold_spec ex2.
  repeat simpl_hyp ex1; try solve[simpl_some; rewrite <- ex1 in halt1'; inversion halt1'; contra].
  repeat simpl_hyp ex2; try solve[simpl_some; rewrite <- ex2 in halt2'; inversion halt2'; contra].
  clear_hyp.
  assert(cur_host1: cur_vmid d1 = HOSTVISOR).
  { destruct inv1. rewrite C1 in valid_state0; simpl_local. destruct Hlocal.
    apply valid_host_vmid0; assumption. }
  assert(cur_host2: cur_vmid d2 = HOSTVISOR).
  { destruct inv2. rewrite C6 in valid_state0; simpl_local. destruct Hlocal.
    apply valid_host_vmid0; assumption. }
  assert(vm_nh: vmid <> HOSTVISOR).
  { autounfold in *. intro T. rewrite T in *. srewrite. simpl in act2. inversion act2. }
  remember (vcpu_run_swith_to_core d1) as d1a.
  remember (vcpu_run_swith_to_core d2) as d2a.
  remember (vcpu_run_process d1a) as d1b.
  remember (vcpu_run_process d2a) as d2b.
  symmetry in Heqd1a, Heqd1b, Heqd2a, Heqd2b.
  assert(ind1: indisting vmid d1a d2a /\ cur_vmid d1a = vmid /\ cur_vmid d2a = vmid /\
               icore d1a = true /\ icore d2a = true /\ valid_vm vmid).
  { unfold vcpu_run_swith_to_core in *.
    repeat simpl_hyp Heqd1a. repeat simpl_hyp Heqd2a. simpl in *.
    assert(valid_vm (cur_vmid d1a)) by (rewrite <- Heqd1a; simpl; autounfold in *; bool_rel_all0; omega).
    assert(valid_vm (cur_vmid d2a)) by (rewrite <- Heqd2a; simpl; autounfold in *; bool_rel_all0; omega).
    assert(cur_vmid d1' = cur_vmid d1a).
    { pose proof (vm_run_cur_same2 _ _ ex1) as T. rewrite T. apply vm_run_cur_same1. assumption. }
    assert(cur_vmid d2' = cur_vmid d2a).
    { pose proof (vm_run_cur_same2 _ _ ex2) as T. rewrite T. apply vm_run_cur_same1. assumption. }
    autounfold in *. replace (vmid =? 0) with false in * by (symmetry; bool_rel; omega).
    simpl in *. bool_rel. srewrite. split_and; try reflexivity; try omega.
    clear_hyp. apply (LOCAL_UNC _ _ _ _ _ obseq).
    apply SAME_OB. rewrite <- Heqd1a in act1'. simpl in act1'. rewrite act1' in Heqd1a. rewrite <- Heqd1a.
    assert(0 =? vmid = false) by (bool_rel; omega). assert(vmid =? 0 = false) by (bool_rel; omega).
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. assert_gso. destruct inv1. rewrite C1 in *; simpl_local. destruct Hlocal0; autounfold in *.
    omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    apply SAME_OB. rewrite <- Heqd2a in act2'. simpl in act2'. rewrite act2' in Heqd2a. rewrite <- Heqd2a.
    assert(0 =? vmid = false) by (bool_rel; omega). assert(vmid =? 0 = false) by (bool_rel; omega).
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    intros. assert_gso. destruct inv2. rewrite C6 in *; simpl_local. destruct Hlocal0; autounfold in *.
    omega. rewrite (ZMap.gso _ _ Hneq). reflexivity.
    rewrite <- Heqd1a. reflexivity. rewrite <- Heqd2a. reflexivity.
    rewrite <- Heqd2a in *. simpl in *. contra.
    rewrite <- Heqd1a in *. simpl in *. contra.
  }
  destruct ind1 as (ind1 & cur1 & cur2 & ic1 & ic2 & vmid_valid).
  assert(act1a: active vmid d1a = true).
  { autounfold. rewrite cur1. simpl_bool_eq. rewrite orb_comm. reflexivity. }
  assert(act2a: active vmid d2a = true).
  { autounfold. rewrite cur2. simpl_bool_eq. rewrite orb_comm. reflexivity. }
  apply indisting_obs_eq in ind1; try assumption.
  assert(ind2: obs_eq vmid d1b d2b /\ invariant d1b /\ invariant d2b).
  { duplicate ind1. destruct D. autounfold in *.
    assert(vmid =? 0 = false) by (bool_rel; omega). srewrite. clear_hyp.
    pose proof (core_data_log_eq0 vmid) as core_data_eq0.
    simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
    unfold_spec Heqd1b. unfold_spec Heqd2b. srewrite. srewrite. simpl_hyp Heqd1b.
    match type of C9 with
    | is_vcpu ?v = true => remember v as vcpuid; clear Heqvcpuid
    end.
    assert(T: valid_vcpu vcpuid) by (autounfold in *; bool_rel_all0; split; assumption).
    pose proof (shadow_ctxt_eq0 vcpuid T) as shadow_eq0.
    simpl_hyp Heqd1b. rewrite <- Heqd1b in *; contra.
    simpl_hyp Heqd2b. rewrite <- Heqd2b in *; contra.
    simpl_hyp Heqd1b. simpl_hyp Heqd1b. rewrite <- Heqd1b in *; simpl in C3; contra.
    simpl_hyp Heqd2b. simpl_hyp Heqd2b. rewrite <- Heqd2b in *; simpl in C8; contra.
    extract_adt C10 d1a1. extract_adt C11 d2a1.
    assert(Hind2: obs_eq vmid d1a1 d2a1 /\ cur_vmid d1a1 = vmid /\ cur_vmid d2a1 = vmid /\
               icore d1a1 = true /\ icore d2a1 = true /\ invariant d1a1 /\ invariant d2a1).
    { clear Heqd1b Heqd2b.
      assert(cur_vmid d1a1 = vmid).
      { rewrite Heqd1a1; autounfold; simpl; rewrite oracle_cur_vmid; simpl; assumption. }
      assert(cur_vmid d2a1 = vmid).
      { rewrite Heqd2a1; autounfold; simpl; rewrite oracle_cur_vmid; simpl; assumption. }
      assert(indisting vmid d1a1 d2a1).
      { eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
        constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
        intros; simpl; destruct_if; bool_rel. unfold mset2; rewrite Case; repeat rewrite ZMap.gss. reflexivity.
        reflexivity. }
      apply indisting_obs_eq in H2.
      split_and; try assumption.
      rewrite Heqd1a1; rewrite oracle_icore; simpl; assumption.
      rewrite Heqd2a1; rewrite oracle_icore; simpl; assumption.
      eassumption. eassumption.
      autounfold; rewrite H0; simpl_bool_eq; rewrite orb_comm; reflexivity.
      autounfold; rewrite H1; simpl_bool_eq; rewrite orb_comm; reflexivity. }
    destruct Hind2 as (Hind2 & cur11 & cur21 & ic11 & ic21 & inv11 & inv21).
    duplicate Hind2. destruct D. autounfold in *.
    assert(vmid =? 0 = false) by (bool_rel; omega).
    symmetry in Heqd1a1, Heqd2a1.
    srewrite. pose proof (core_data_log_eq1 vmid) as core_data_eq2.
    simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
    pose proof (shadow_ctxt_eq1 vcpuid T) as shadow_eq1.
    srewrite.
    simpl_hyp Heqd1b.
    - simpl_hyp Heqd1b. rewrite <- Heqd1b in *; simpl in C3; contra.
      simpl_hyp Heqd2b. rewrite <- Heqd2b in *; simpl in C8; contra.
      extract_adt C17 d1a2. extract_adt C18 d2a2.
      simpl_hyp Heqd1b. rewrite <- Heqd1b in *; simpl in C3; contra.
      simpl_hyp Heqd2b. rewrite <- Heqd2b in *; simpl in C8; contra.
      assert(Hind3: obs_eq vmid d1a2 d2a2 /\ cur_vmid d1a2 = vmid /\ cur_vmid d2a2 = vmid /\
                    icore d1a2 = true /\ icore d2a2 = true /\ invariant d1a2 /\ invariant d2a2).
      { assert(indisting vmid d1a2 d2a2).
        eapply LOCAL_UNC; [apply OBS_EQ |eapply ORACLE; eassumption|eapply ORACLE; eassumption].
        unfold_spec C12. simpl_hyp C12; inversion C12. unfold_spec C14; simpl_hyp C14; inversion C14.
        symmetry in Heqd1a2, Heqd2a2.
        constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
        simpl. intros. destruct_if. bool_rel; rewrite Case; repeat rewrite ZMap.gss.
        pose proof (vminfo_eq1 vmid0 Hvm). rewrite Case in H; simpl_bool_eq; simpl_some.
        rewrite H. reflexivity. reflexivity.
        unfold mset2. repeat rewrite ZMap.gss. reflexivity.
        assert(cur_vmid d1a2 = vmid).
        rewrite Heqd1a2. rewrite oracle_cur_vmid. simpl. assumption.
        assert(cur_vmid d2a2 = vmid).
        rewrite Heqd2a2. rewrite oracle_cur_vmid. simpl. assumption.
        split_and; try assumption.
        apply indisting_obs_eq in H. assumption.
        unfold active; rewrite orb_comm; rewrite H1; simpl_bool_eq; reflexivity.
        unfold active; rewrite orb_comm; rewrite H2; simpl_bool_eq; reflexivity.
        rewrite Heqd1a2; rewrite oracle_icore; simpl. assumption.
        rewrite Heqd2a2; rewrite oracle_icore; simpl. assumption.
        eassumption. eassumption. }
      destruct Hind3 as (Hind3 & cur12 & cur22 & ic12 & ic22 & inv12 & inv22).
      split_and.
      destruct Hind3. autounfold in *. symmetry in Heqd1a2, Heqd2a2.
      srewrite. pose proof (core_data_log_eq2 vmid) as core_data_eq3.
      simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
      pose proof (shadow_ctxt_eq2 vcpuid T) as shadow_eq2.
      srewrite. simpl_hyp Heqd1b. rewrite <- Heqd1b, <- Heqd2b. clear Heqd1b Heqd2b.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq2. assumption.
      unfold mset2. repeat rewrite ZMap.gss. reflexivity.
      eassumption. eassumption.
    - simpl_hyp Heqd1b. simpl_hyp Heqd1b. simpl_hyp Heqd1b. split_and.
      rewrite <- Heqd1b, <- Heqd2b. clear Heqd1b Heqd2b.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq1. assumption.
      unfold mset2. repeat rewrite ZMap.gss. reflexivity.
      simpl. intros. destruct_if. bool_rel; rewrite Case; unfold mset2; repeat rewrite ZMap.gss. reflexivity.
      reflexivity.
      eassumption. eassumption.
      split_and. apply (prot_and_map_conf_res _ _ _ _ _ _ _ _ Heqd1b Heqd2b vmid_valid); simpl; try assumption.
      eassumption. eassumption.
      constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
      intros. destruct_zmap. reflexivity. apply shadow_ctxt_eq1. assumption.
      unfold mset2. repeat rewrite ZMap.gss. reflexivity.
      simpl. intros. destruct_if. bool_rel; rewrite Case; unfold mset2; repeat rewrite ZMap.gss. reflexivity.
      reflexivity.
      eassumption. eassumption.
    - rewrite <- Heqd1b in *; simpl in C3; contra. }
  destruct ind2 as (ind2 & inv12 & inv22).
  pose proof (vm_run_cur_same1 _ _ Heqd1b). pose proof (vm_run_cur_same1 _ _ Heqd2b). srewrite.
  destruct ind2; autounfold in *.
  assert(vmid =? 0 = false) by (bool_rel; omega). srewrite. clear_hyp.
  srewrite; simpl_bool_eq; simpl in *; simpl_some; clear_hyp.
  clear Heqd1a Heqd2a Heqd1b Heqd2b.
  hsimpl_func ex1; hsimpl_func ex2. apply OBS_EQ. srewrite.
  destruct inv22. rewrite C8 in *. clear_hyp; simpl_local. destruct Hlocal0.
  pose proof (shadow_ctxt_eq0 (cur_vcpuid d2b) cur_vcpuid_range0). repeat rewrite H2.
  constructor; autounfold; simpl; srewrite; srewrite; simpl_bool_eq; try reflexivity; try assumption.
Qed.

Lemma vm_exit_confidentiality_restore:
  forall vmid d1 d2 d1' d2'
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
    (ex1: vm_exit_handler_spec d1 = Some d1')
    (ex2: vm_exit_handler_spec d2 = Some d2')
    (obseq: indisting vmid d1 d2),
    indisting vmid d1' d2'.
Proof.
  intros. unfold_spec ex1; unfold_spec ex2.
  simpl_hyp ex1; simpl_hyp ex1; simpl_hyp ex1; contra.
  simpl_hyp ex2; simpl_hyp ex2; simpl_hyp ex2; contra.
  clear_hyp.
  assert(cur1_r: HOSTVISOR < cur_vmid d1 < COREVISOR).
  { destruct inv1. apply valid_vm_vmid0; assumption. }
  assert(cur2_r: HOSTVISOR < cur_vmid d2 < COREVISOR).
  { destruct inv2. apply valid_vm_vmid0; assumption. }
  assert(vmid_nz1: vmid <> cur_vmid d1).
  { autounfold in *. intro T. rewrite <- T in *. simpl_bool_eq.
    rewrite orb_comm in act1. inversion act1. }
  assert(vmid_nz2: vmid <> cur_vmid d2).
  { autounfold in *. intro T. rewrite <- T in *. simpl_bool_eq.
    rewrite orb_comm in act2. inversion act2. }
  repeat simpl_hyp ex1; inv ex1; contra.
  exploit(vm_exit_pre_integ vmid _ _ _ C5); try assumption; try omega.
  intros (? & cur & ih & ? & cic). autounfold in act1'; srewrite.
  rewrite andb_comm, orb_comm in act1'.
  replace (cur_vmid d1 =? vmid) with false in act1' by (symmetry; bool_rel; omega).
  inversion act1'.
  repeat simpl_hyp ex2; inv ex2; contra.
  exploit(vm_exit_pre_integ vmid _ _ _ C6); try assumption; try omega.
  intros (? & cur & ih & ? & cic). autounfold in act2'; srewrite.
  rewrite andb_comm, orb_comm in act2'.
  replace (cur_vmid d2 =? vmid) with false in act2' by (symmetry; bool_rel; omega).
  inversion act2'.
  autounfold in *; simpl in *.
  exploit(vm_exit_pre_integ vmid _ _ _ C5); try assumption; try omega.
  exploit(vm_exit_pre_integ vmid _ _ _ C6); try assumption; try omega.
  intros (lc1 & cur1 & ih1 & crd1 & cic1). intros (lc2 & cur2 & ih2 & crd2 & cic2).
  bool_rel. apply cic1 in C11. apply cic2 in C8. clear cic1 cic2.
  destruct C8; destruct C11.
  assert(host: vmid = 0).
  { destruct (vmid =? 0) eqn:T; bool_rel. assumption.
    simpl in act1'. autounfold in act1'; bool_rel; omega. }
  rewrite host in *; simpl_bool_eq; simpl in *. bool_rel_all.
  remember (r {cur_vmid: 0} {cur_vcpuid: -1}) as d10.
  remember (r0 {cur_vmid: 0} {cur_vcpuid: -1}) as d20.
  assert(indisting 0 d10 d20).
  { eapply LOCAL_UNC. apply obseq.
    eapply TRANS. eapply lc2. rewrite Heqd10. apply SAME_OB.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    replace (cur_vmid d1 =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
    replace (0 =? cur_vmid d1) with false by (symmetry; bool_rel; omega). reflexivity.
    eapply TRANS. eapply lc1. rewrite Heqd20. apply SAME_OB.
    constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
    constructor; intros; reflexivity.
    replace (cur_vmid d2 =? 0) with false by (symmetry; bool_rel; omega). reflexivity.
    replace (0 =? cur_vmid d2) with false by (symmetry; bool_rel; omega). reflexivity. }
  apply indisting_obs_eq in H3. subst. unfold switch_to_host.
  destruct H3; autounfold in *; repeat srewrite; simpl_bool_eq; simpl in *.
  destruct inv2. pose proof (shadow_ctxt_eq0 _ curid_range0). repeat srewrite.
  apply OBS_EQ. constructor; autounfold; simpl; repeat srewrite; simpl_bool_eq; try reflexivity; try assumption.
  rewrite Heqd10; autounfold; rewrite orb_comm; simpl_bool_eq; reflexivity.
  rewrite Heqd20; autounfold; rewrite orb_comm; simpl_bool_eq; reflexivity.
Qed.
```
