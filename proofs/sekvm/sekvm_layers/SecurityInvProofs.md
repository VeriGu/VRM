# InvProofs

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
Require Import Invs.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.ltb Z.geb Z.gtb.
Local Opaque count_smmu_map.

Lemma map_host_inv:
  forall addr s s' a b
    (ex: local_map_host addr s = (s', false, a, b))
    (Haddr: valid_addr addr),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex.
  destruct (s2_owner (addr / 4096) @ (s2page s) =? 4294967295) eqn:Hinvalid; simpl in *.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H. reflexivity. apply host_npt_cons.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H.
  rewrite host_pte_pfn_dev. reflexivity.  assumption.
  apply host_flatmap.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv Hpfn. rewrite host_pte_pfn_dev; try assumption.
  left. assumption. apply host_iso.
  intros. assert_gsoH H. red; intro. subst. omega. rewrite (ZMap.gso _ _ Hneq) in H.
  eapply vm_iso; eassumption.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H. reflexivity. apply host_npt_cons.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H.
  rewrite host_pte_pfn_mem. reflexivity.  assumption.
  apply host_flatmap.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv Hpfn. rewrite host_pte_pfn_mem; try assumption.
  right. bool_rel_all; autounfold in *; omega. apply host_iso.
  intros. assert_gsoH H. red; intro. subst. omega. rewrite (ZMap.gso _ _ Hneq) in H.
  eapply vm_iso; eassumption.
Qed.

Lemma clear_vm_page_inv:
  forall vmid pfn s s' a b c
    (ex: local_clear_vm_page vmid pfn s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (valid_state': vm_state (VS (vmid @ (vminfos s))) >= POWEROFF),
    shared_inv s -> shared_inv s'.
Proof.
  assert(Z_div_le_le: forall a b c d, 0 < d -> a <= b <= c -> a / d <= b / d <= c / d).
  { intros. destruct H0; split; apply Z_div_le; assumption. }
  intros. hsimpl_func ex; bool_rel; try assumption.
  destruct H; autounfold in *.
  assert(Hcount0: forall n, 0 <= Z.of_nat n <= EL2_SMMU_CFG_SIZE -> count_smmu_map n pfn (smmu_vmid s) (spts s) = 0).
  { Local Transparent count_smmu_map.
    induction n0. intros; reflexivity.
    rewrite Nat2Z.inj_succ, succ_plus_1. intros.
    simpl. rewrite IHn0. repeat destruct_if; try omega.
    match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) eqn: Hsp end.
    autounfold in *; bool_rel. destruct_if; try reflexivity; bool_rel.
    exploit (smmu_iso 0 (Z.of_nat n0 mod 8) (Z.of_nat n0 / 8) (pfn + 1000000000) z2 z3);
      autounfold; try eassumption; try omega.
    rewrite Z.mul_comm. rewrite <- Z.div_mod. assumption. omega.
    assert(0 <= Z.of_nat n0 <= 15) by omega.
    assert(0 <= Z.of_nat n0 / 8 <= 1).
    eapply (Z_div_le_le 0 _ 15 8); omega. omega.
    apply Z_mod_lt; omega.
    intros (? & ?).
    rewrite Z.mul_comm, <- Z.div_mod in H0; try omega.
    rewrite Case in H0.
    pose proof (host_s2_map z2 H0). rewrite H1 in H2.
    destruct (zeq z2 pfn); srewrite; omega.
    match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) eqn: Hsp end.
    destruct_if; reflexivity. omega.
    Local Opaque count_smmu_map. }
  destruct (z =? 0) eqn:Hz.
  inv C2; bool_rel; srewrite.
  replace z0 with 0 in *.
  rewrite zmap_set_id.
  constructor; autounfold; simpl; try assumption.
  intros. destruct_zmap. simpl. reflexivity.
  apply host_s2_map. rewrite (ZMap.gso _ _ Heq) in H. assumption.
  assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
  rewrite (ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. simpl. auto.
  eapply host_iso; try eassumption.
  intros. destruct_zmap. srewrite.
  exploit (vm_iso _ _ _ _ _ H); try eassumption. omega.
  intros. srewrite. omega. eapply vm_iso; try eassumption.
  rewrite (ZMap.gso _ _ Heq) in H3. assumption.
  intros. destruct_zmap. rewrite Heq in *.
  exploit (smmu_iso vmid cbndx index gfn pfn pte); try eassumption.
  intros (? & ?). srewrite. destruct Hvalid_vmid; omega.
  eapply smmu_iso; eassumption.
  intro. destruct_zmap. simpl; intros.
  rewrite Hcount0. omega. simpl; autounfold. omega.
  apply smmu_count. pose proof (host_npt_cons _ _ _ _ C0).
  rewrite H. reflexivity.
  pose proof (local_mmap_level3 _ _ _ _ _ C2).
  constructor; autounfold; simpl; try assumption.
  intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
  intro T. inv T. reflexivity. apply host_npt_cons.
  intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
  replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
  intros. inv H0. contra. apply host_flatmap.
  intros. destruct_zmap. simpl. reflexivity.
  apply host_s2_map. rewrite (ZMap.gso _ _ Heq) in H0. assumption.
  assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
  rewrite (ZMap.gso _ _ Hneq). assumption.
  rewrite ZMap.gss. intros until pte. rewrite H.
  replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
  destruct_zmap. intros. destruct_zmap. simpl. auto. inv Hpfn. contra.
  destruct_zmap. simpl. intros; auto.
  eapply host_iso; try eassumption.
  intros. assert_gsoH H0. red; intro. rewrite H5 in H1; omega.
  rewrite (ZMap.gso _ _ Hneq) in H0.
  destruct_zmap. srewrite.
  exploit (vm_iso _ _ _ _ _ H0); try eassumption. omega.
  intros. srewrite. omega. eapply vm_iso; try eassumption.
  rewrite (ZMap.gso _ _ Heq) in H4. assumption.
  intros. destruct_zmap. rewrite Heq in *.
  exploit (smmu_iso vmid0 cbndx index gfn pfn pte); try eassumption.
  intros (? & ?). srewrite. destruct Hvalid_vmid; omega.
  eapply smmu_iso; eassumption.
  intro. destruct_zmap. simpl; intros.
  rewrite Hcount0. omega. simpl; autounfold. omega.
  apply smmu_count.
Qed.

Lemma assign_pfn_to_vm_inv:
  forall vmid gfn pfn dorc logn s s' n a b c
    (ex: local_assign_pfn_to_vm vmid gfn pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; bool_rel; try assumption.
  - duplicate H; destruct H; autounfold in *.
    pose proof (smmu_count_0_no_map _ D _ C C0) as Hcount0.
    destruct (z =? 0) eqn:Hz.
    + inv C3; bool_rel; srewrite.
      replace z0 with 0 in *.
      rewrite zmap_set_id.
      constructor; autounfold; simpl; try assumption.
      * intro. destruct_zmap. simpl. intros; omega. apply host_s2_map.
      * assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
        rewrite (ZMap.gso _ _ Hneq). assumption.
      * intros. destruct_zmap. rewrite Heq in *.
        rewrite (host_flatmap _ _ _ _ Hpfn) in Hpfn. rewrite C1 in Hpfn. inv Hpfn.
        contra. assumption. eapply host_iso; try eassumption.
      * intros. destruct_zmap. rewrite Heq in *.
        exploit (vm_iso _ _ _ _ _ H); try eassumption. omega.
        intros. rewrite C in H4. omega. rewrite (ZMap.gso _ _ Heq) in H3.
         eapply vm_iso; eassumption.
      * intros. destruct_zmap. simpl. rewrite Heq in *.
        exploit (smmu_iso vmid0 cbndx index gfn0 pfn pte); try eassumption.
        intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
        rewrite Heq. apply Hspt. eapply smmu_iso; eassumption.
      * intro. destruct_zmap. simpl; intros.
        rewrite <- C0. eapply smmu_count; eassumption. eapply smmu_count.
      * pose proof (host_npt_cons _ _ _ _ C1). rewrite H. reflexivity.
    + pose proof (local_mmap_level3 _ _ _ _ _ C3).
      constructor; autounfold; simpl; try assumption.
      * intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
        intro T. inv T. reflexivity. apply host_npt_cons.
      * intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
        intros. inv H0. contra. apply host_flatmap.
      * intro. destruct_zmap. simpl. intros; omega. apply host_s2_map.
      * assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
        rewrite (ZMap.gso _ _ Hneq). assumption.
      * rewrite ZMap.gss. rewrite H. intros until pte.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
        destruct_zmap. intros. inv Hpfn. contra.
        intros. autounfold in *. assert_gso. red; intro.
        inv H0. pose proof (host_flatmap _ _ _ _ Hpfn Hexists). inv H0.
        apply Heq. rewrite Z_div_mult_full. reflexivity. omega.
        rewrite (ZMap.gso _ _ Hneq). eapply host_iso; eassumption.
      * intros. destruct_zmap. rewrite Heq in *.
        assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
        exploit (vm_iso _ _ _ _ _ H0); try eassumption. omega. intros.
        rewrite C in H5. omega.
        assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
        rewrite (ZMap.gso _ _ Heq) in H4. eapply vm_iso; eassumption.
      * intros. destruct_zmap. simpl. rewrite Heq in *.
        exploit (smmu_iso vmid0 cbndx index gfn0 pfn pte); try eassumption.
        intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
        rewrite Heq. apply Hspt. eapply smmu_iso; eassumption.
      * intro. destruct_zmap. simpl; intros.
        rewrite <- C0. eapply smmu_count; eassumption. eapply smmu_count.
  - rewrite zmap_set_id. destruct s; simpl in *. assumption.
Qed.

Lemma map_pfn_vm_inv:
  forall vmid addr pte level s s' a
    (ex: local_map_pfn_vm vmid addr pte level s = (s', false, a))
    (Howner: vm_state (VS (vmid @ (vminfos s))) >= POWEROFF \/
       forall pfn, (if level =? 2 then phys_page pte / PAGE_SIZE <= pfn < phys_page pte / PAGE_SIZE + 512
                     else pfn = phys_page pte / PAGE_SIZE) -> s2_owner (pfn @ (s2page s)) = vmid)
    (valid_vm: valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  Local Transparent Z.sub.
  intros. hsimpl_func ex; bool_rel; try assumption.
  duplicate H; destruct H; autounfold in *.
  assert(Hnhost: 0 <> vmid) by omega.
  constructor; autounfold; simpl; repeat rewrite (ZMap.gso _ _ Hnhost); try assumption.
  intros until pte0. destruct_zmap; try eapply vm_iso. inv Heq.
  intros. destruct (level =? 2) eqn:Hlevel.
  - pose proof (local_mmap_level2 _ _ _ _ _ C gfn) as Hn.
    rewrite vm_pte_pfn_level2 in Hn.
    destruct in_range_n in Hn. rewrite H in Hn. inv Hn. simpl.
    destruct Howner as [?|Howner]. omega.
    apply Howner. autounfold in *. omega. rewrite Hn in H.
    eapply vm_iso; try eassumption.
  - pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn.
    rewrite Hn in H. destruct (gfn =? addr / PAGE_SIZE) eqn:Hsame.
    bool_rel. rewrite Hsame in H. rewrite ZMap.gss in H. inv H.
    rewrite vm_pte_pfn_level3 in *.
    destruct Howner as [?|Howner]. omega.
    apply Howner; reflexivity.
    bool_rel. rewrite (ZMap.gso _ _ Hsame) in H.
    eapply vm_iso; eassumption.
Qed.

Lemma map_io_inv:
  forall vmid gpa pa s s' a b c
    (ex: local_map_io vmid gpa pa s = (s', false, a, b, c))
    (valid_addr: valid_paddr pa)
    (valid_vm': valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  intros; hsimpl_func ex; try assumption; destruct H; autounfold in *.
  assert(Hnhost: 0 <> vmid) by omega.
  constructor; autounfold; simpl; repeat rewrite (ZMap.gso _ _ Hnhost); try assumption.
  intros until pte. destruct_zmap; try eapply vm_iso. inv Heq.
  intros. rewrite (local_mmap_level3 _ _ _ _ _ C1) in H.
  destruct (gfn =? gpa / PAGE_SIZE) eqn:Hsame; bool_rel; subst.
  rewrite ZMap.gss in H. inv H.
  rewrite vm_pte_pfn_dev in H3; try assumption. autounfold in H3; omega.
  rewrite (ZMap.gso _ _ Hsame) in H. eapply vm_iso; eassumption.
Qed.

Lemma grant_vm_page_inv:
  forall vmid pfn s s' a
    (ex: local_grant_vm_page vmid pfn s = (s', a))
    (valid_vm': valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct_if.
  - bool_rel_all. destruct H; autounfold in *.
    constructor; autounfold; simpl; try assumption.
    + intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
      eapply host_s2_map; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. inv Heq.
      intros. pose proof (host_iso _ _ _ _ Hpfn Hexists).
      simpl. omega. apply host_iso.
    + intros until pte. destruct_zmap. inv Heq.
      simpl. apply vm_iso. apply vm_iso.
    + intros until pte. destruct_zmap. inv Heq. simpl.
      apply smmu_iso. apply smmu_iso.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count.
  - destruct s; simpl in *; assumption.
Qed.

Lemma revoke_vm_page_inv:
  forall vmid pfn dorc logn s s' a b c n
    (ex: local_revoke_vm_page vmid pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex.
  - destruct H; autounfold in *.
    destruct (z =? 0) eqn:Hz; bool_rel_all.
    + inv C3. rewrite zmap_set_id.
      constructor; autounfold; simpl; try assumption.
      * intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
        eapply host_s2_map; eassumption.
      * destruct_zmap. inv Heq. omega. assumption.
      * intros until pte. destruct_zmap. intros.
        simpl. pose proof (host_flatmap _ _ _ _ Hpfn Hexists).
        inv H. pose proof (host_npt_cons _ _ _ _ C1).
        rewrite C1 in Hpfn. inv Hpfn.
        replace (phys_page 0 / 4096) with 0 in H1 by reflexivity. omega.
        apply host_iso.
      * intros until pte. destruct_zmap. inv Heq.
        simpl. apply vm_iso. apply vm_iso.
      * intros until pte. destruct_zmap. inv Heq. simpl.
        apply smmu_iso. apply smmu_iso.
      * intro. destruct_zmap. inv Heq. simpl. intros. omega.
        apply smmu_count.
    + pose proof (local_mmap_level3 _ _ _ _ _ C3) as Hn.
      constructor; autounfold; simpl; try assumption.
      * rewrite ZMap.gss. intros until pte. rewrite Hn.
        destruct_zmap. intros. inv H. reflexivity.
        apply host_npt_cons.
      * rewrite ZMap.gss. intros until pte. rewrite Hn.
        destruct_zmap. intros. inv H.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in H0 by reflexivity.
        contra. apply host_flatmap.
      * intro pfn0. destruct_zmap. simpl. intros; omega.
        eapply host_s2_map; eassumption.
      * destruct_zmap. simpl. rewrite <- Heq. eapply page_0_invalid. assumption.
      * rewrite ZMap.gss. rewrite Hn. intros until pte.
        destruct_zmap. intros. inv Hpfn.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in Hexists by reflexivity.
        contra. intros. pose proof (host_flatmap _ _ _ _ Hpfn Hexists).
        rewrite Z_div_mult_full in Heq. rewrite H in Heq. rewrite (ZMap.gso _ _ Heq).
        eapply host_iso; eassumption. autounfold; omega.
      * intros until pte. intros. assert_gsoH H. red; intro; srewrite; omega.
        rewrite (ZMap.gso _ _ Hneq) in H.
        destruct_zmap. inv Heq. simpl. eapply vm_iso; try eassumption.
        rewrite ZMap.gss in H3. simpl in H3. assumption.
        eapply vm_iso; try eassumption. rewrite (ZMap.gso _ _ Heq) in H3. assumption.
      * intros until pte. destruct_zmap. inv Heq. simpl.
        apply smmu_iso. apply smmu_iso.
      * intro. destruct_zmap. inv Heq. simpl. intros. omega.
        apply smmu_count.
  - bool_rel_all. destruct H; autounfold in *.
    constructor; autounfold; simpl; try assumption.
    + intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
      eapply host_s2_map; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. inv Heq.
      intros. pose proof (host_iso _ _ _ _ Hpfn Hexists).
      simpl. omega. apply host_iso.
    + intros until pte. destruct_zmap. inv Heq.
      simpl. apply vm_iso. apply vm_iso.
    + intros until pte. destruct_zmap. inv Heq. simpl.
      apply smmu_iso. apply smmu_iso.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count.
  - assumption.
Qed.

Lemma set_vcpu_active_inv:
  forall vmid vcpuid s s' a
    (ex: local_set_vcpu_active vmid vcpuid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso.
  intros until pte. destruct_zmap; simpl; apply smmu_iso.
Qed.

Lemma set_vcpu_inactive_inv:
  forall vmid vcpuid s s' a
    (ex: local_set_vcpu_inactive vmid vcpuid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso.
  intros until pte. destruct_zmap; simpl; apply smmu_iso.
Qed.

Lemma register_vcpu_inv:
  forall vmid vcpuid s s' a
    (ex: local_register_vcpu vmid vcpuid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso.
  intros until pte. destruct_zmap; simpl; apply smmu_iso.
Qed.

Lemma gen_vmid_inv:
  forall s s' a
    (ex: local_gen_vmid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
Qed.

Lemma register_kvm_inv:
  forall vmid s s' a
    (ex: local_register_kvm vmid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl.
  intros. eapply vm_iso; try eassumption. rewrite C. omega.
  apply vm_iso.
  intros until pte. destruct_zmap; simpl.
  intros. eapply smmu_iso; try eassumption. rewrite C.
  autounfold in *; bool_rel; omega.
  apply smmu_iso.
Qed.

Lemma set_boot_info_inv:
  forall vmid load_addr size s s' a b
    (ex: local_set_boot_info vmid load_addr size s = (s', false, a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso.
  intros until pte. destruct_zmap; simpl; apply smmu_iso.
  assumption.
Qed.

Lemma remap_vm_image_inv:
  forall vmid pfn load_idx s s' a b
    (ex: local_remap_vm_image vmid pfn load_idx s = (s', false, a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H; autounfold in *.
  assert(0 <> 16) by omega.
  constructor; autounfold; simpl; try rewrite (ZMap.gso _ _ H); try assumption.
  intros until pte. intros ? ?. assert_gsoH H0.
  red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
  destruct_zmap; simpl; eapply vm_iso; try eassumption.
  rewrite Heq in H0; eassumption. omega.
  intros until pte. destruct_zmap; simpl; apply smmu_iso.
  assumption. assumption.
Qed.

Lemma smmu_assign_page_inv:
  forall cbndx index pfn gfn s s' a b c d
    (ex: local_smmu_assign_page cbndx index pfn gfn s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; try assumption; bool_rel_all.
  pose proof (smmu_count_0_no_map _ H _ C2 C3) as Hcount0.
  destruct H; autounfold in *.
  destruct (z =? 0) eqn:Hz; bool_rel_all.
  - inv C6. rewrite zmap_set_id.
    constructor; autounfold; simpl; try assumption.
    + intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
      eapply host_s2_map; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. intros.
      simpl. pose proof (host_flatmap _ _ _ _ Hpfn Hexists).
      inv H. pose proof (host_npt_cons _ _ _ _ C4).
      rewrite C4 in Hpfn. inv Hpfn.
      replace (phys_page 0 / 4096) with 0 in H1 by reflexivity. omega.
      apply host_iso.
    + intros until pte. destruct_zmap. simpl.
      intros. exploit vm_iso; try eassumption. omega.
      intros. omega. apply vm_iso.
    + intros until pte. destruct_zmap. simpl.
      intros. exploit smmu_iso; try eassumption.
      intros (? & ?). srewrite.
      exploit Hcount0; try eassumption. reflexivity. intros. inv H2.
      apply smmu_iso.
    + intro. destruct_zmap. simpl. intros.
      pose proof (smmu_count _ C2). rewrite C3 in H0. omega.
      apply smmu_count.
  - pose proof (local_mmap_level3 _ _ _ _ _ C6) as Hn.
    constructor; autounfold; simpl; try assumption.
    + rewrite ZMap.gss. intros until pte. rewrite Hn.
      destruct_zmap. intros. inv H. reflexivity.
      apply host_npt_cons.
    + rewrite ZMap.gss. intros until pte. rewrite Hn.
      destruct_zmap. intros. inv H.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in H0 by reflexivity.
      contra. apply host_flatmap.
    + intro pfn0. destruct_zmap. simpl. intros; omega.
      eapply host_s2_map; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + rewrite ZMap.gss. rewrite Hn. intros until pte.
      destruct_zmap. intros. inv Hpfn.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in Hexists by reflexivity.
      contra. intros. pose proof (host_flatmap _ _ _ _ Hpfn Hexists).
      rewrite Z_div_mult_full in Heq. rewrite H in Heq. rewrite (ZMap.gso _ _ Heq).
      eapply host_iso; eassumption. autounfold; omega.
    + intros until pte. intros ? ?.  assert_gsoH H. red; intro; srewrite; omega.
      rewrite (ZMap.gso _ _ Hneq) in H.
      destruct_zmap. simpl.
      intros. exploit vm_iso; try eassumption. omega. rewrite Heq. omega.
      intros. rewrite Heq in H4. omega. eapply vm_iso; try eassumption.
    + intros until pte. destruct_zmap. simpl. intros.
      exploit smmu_iso; try eassumption. intros (? & ?).
      srewrite. pose proof (Hcount0 _ _ Hvalid_smmu Hvalid_cfg Hsmmu _ _ _ Hspt).
      contra. apply smmu_iso.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count.
Qed.

Lemma smmu_map_page_inv:
  forall cbndx index iova pte s s' a b c d
    (ex: local_smmu_map_page cbndx index iova pte s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; try assumption.
  apply andb_true_iff in C1. destruct C1 as (C10 & C11). bool_rel.
  pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
  destruct_if. apply andb_true_iff in Case. destruct Case; bool_rel.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl; try assumption.
    + rewrite Hn. intros until pte0. destruct_zmap.
      destruct_zmap. intros. inv H3. reflexivity.
      rewrite <- Heq. eapply spt_cons; eassumption.
      apply spt_cons.
    + intro. destruct_zmap. simpl.
      intros. eapply host_s2_map; try eassumption. apply host_s2_map.
    + destruct_zmap. simpl. rewrite <- Heq. assumption. assumption.
    + intros until pte0. destruct_zmap. simpl. intros. auto.
      apply host_iso.
    + intros until pte0. destruct_zmap. simpl. intros.
      exploit vm_iso; try eassumption. intros. omega.
      apply vm_iso.
    + intros until pte0. rewrite Hn. destruct_zmap.
      destruct_zmap. intros. inv Hspt. rewrite ZMap.gss.
      simpl. rewrite H0 in *.
      split. assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite H2. rewrite C10. reflexivity. rewrite C11. reflexivity.
      intros. assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt.
      exploit smmu_iso; try eassumption. intros (? & ?).
      destruct_zmap. simpl. srewrite. auto. auto.
      intros. exploit smmu_iso; try eassumption. intros (? & ?).
      destruct_zmap. simpl. srewrite. auto. auto.
    + intro. destruct_zmap. simpl. intros. pose proof (smmu_count _ H).
      Local Transparent count_smmu_map.
      assert(forall n, (Z.of_nat n <= smmu_id index cbndx) ->
                  count_smmu_map n (phys_page pte / 4096) (smmu_vmid s) s0 =
                  count_smmu_map n (phys_page pte / 4096) (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl; autounfold in *. rewrite Hn. assert_gso.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. omega. omega. rewrite (ZMap.gso _ _ Hneq).
        rewrite IHn. reflexivity. omega. }
      pose proof (host_s2_map _ H0).
      assert(forall n, (Z.of_nat n > smmu_id index cbndx) ->
                  count_smmu_map n (phys_page pte / 4096) (smmu_vmid s) s0 <=
                  count_smmu_map n (phys_page pte / 4096) (smmu_vmid s) (spts s) + 1).
      { induction n. intros. autounfold in *. simpl in H5. omega.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        destruct (smmu_id index cbndx =? Z.of_nat n) eqn:Hsame. bool_rel.
        simpl; autounfold in *. rewrite Hn.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq.
        rewrite <- Hsame. rewrite ZMap.gss. simpl.
        srewrite. rewrite ZMap.gss. rewrite <- Heq.
        destruct_if. bool_rel. srewrite. omega. simpl_bool_eq.
        srewrite. rewrite H3. match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        destruct_if; omega. omega. omega.
        bool_rel. simpl. autounfold in *.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. rewrite Hn. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
        match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if. apply IHn. omega.
        assert(Z.of_nat n > index * 8 + cbndx) by omega. apply IHn in H6. omega.
        apply IHn. omega. omega. }
      pose proof (H5 16%nat). replace (Pos.to_nat 16) with (16%nat) by reflexivity.
      assert(Z.of_nat 16 > smmu_id index cbndx). autounfold; simpl; omega.
      apply H6 in H7. replace (Z.to_nat 16) with 16%nat in H2 by reflexivity. omega.
      pose proof (host_s2_map _ H0). srewrite.
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) s0 =
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. autounfold in *. rewrite Hn.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. destruct_zmap.
        assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). rewrite IHn. reflexivity.
        omega. rewrite IHn. reflexivity. omega. omega. }
      rewrite H2. apply smmu_count. autounfold; simpl. omega.
      Local Opaque count_smmu_map.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl.
    + rewrite Hn. intros until pte0. destruct_zmap.
      destruct_zmap. intros. inv H1. reflexivity.
      rewrite <- Heq. eapply spt_cons; eassumption.
      apply spt_cons.
    + assumption. + assumption. + assumption. + assumption.
    + assumption. + assumption. + assumption.
    + rewrite Hn. intros until pte0. destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      assert(index0 * 8 + cbndx0 = index * 8 + cbndx) by omega.
      srewrite. auto.
      assert(index0 * 8 + cbndx0 = index * 8 + cbndx) by omega.
      rewrite <- H. apply smmu_iso. apply smmu_iso.
    + intro. destruct (zeq pfn (phys_page pte / 4096)).
      srewrite. intros. assert(s2_count (phys_page pte / 4096) @ (s2page s) >= 16).
      bool_rel_all; omega.
      Local Transparent count_smmu_map.
      assert(forall n pfn a b, count_smmu_map n pfn a b <= Z.of_nat n).
      { induction n. intros. simpl. omega.
        intros. rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        pose proof (IHn pfn0 a b).
        repeat destruct_if; omega. }
      pose proof (H1 (Pos.to_nat 16) (phys_page pte / 4096) (smmu_vmid s) s0).
      replace (Z.of_nat (Pos.to_nat 16)) with 16 in H2 by reflexivity. omega.
      intros. pose proof (host_s2_map _ H).
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) s0 =
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n0. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. autounfold in *. rewrite Hn.
        replace (Z.of_nat n0 / 8 * 8) with (8 * (Z.of_nat n0 / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. destruct_zmap.
        assert(Z.of_nat n0 = index * 8 + cbndx) by omega. rewrite H2.
        destruct_zmap.
        assert((index * 8 + cbndx) @ (smmu_vmid s) =? 0 = false).
        bool_rel. red; intro T. rewrite T in C10. symmetry in C10.
        pose proof (host_s2_map _ C10). srewrite. omega. rewrite H3.
        match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; apply IHn0; omega. rewrite IHn0. reflexivity. omega.
        rewrite IHn0. reflexivity. omega. omega. }
      rewrite H1. apply smmu_count. assumption. autounfold; simpl. omega.
      Local Opaque count_smmu_map.
Qed.

Lemma smmu_clear_inv:
  forall iova cbndx index s s' a b c d
    (ex: local_smmu_clear iova cbndx index s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; try assumption.
  destruct_if. apply andb_true_iff in Case. destruct Case; bool_rel.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl; try assumption.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply spt_cons.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). intros until pte.
      destruct_zmap. destruct_zmap. intros. inv H3. reflexivity.
      rewrite <- Heq. eapply spt_cons; eassumption. apply spt_cons.
    + intro. destruct_zmap. simpl.
      intros. eapply host_s2_map; try eassumption. apply host_s2_map.
    + destruct_zmap. simpl. rewrite <- Heq. assumption. assumption.
    + intros until pte. destruct_zmap. simpl. intros. auto.
      apply host_iso.
    + intros until pte. destruct_zmap. simpl. intros.
      exploit vm_iso; try eassumption. intros. omega.
      apply vm_iso.
    + intros until pte.
      destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2.
      intros. destruct_zmap. simpl. replace (phys_page 0 / 4096) with 0 in Heq by reflexivity.
      contra. eapply smmu_iso; try eassumption.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      replace (phys_page 0 / PAGE_SIZE) with 0 in H by reflexivity. contra.
      intros. destruct_zmap. simpl.
      autounfold in *.
      assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt. rewrite Heq1 in Hspt.
      eapply smmu_iso; try eassumption. omega.
      autounfold in *.
      assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt.
      eapply smmu_iso; try eassumption.
      destruct_zmap. simpl. intros.
      eapply smmu_iso; try eassumption.
      eapply smmu_iso; try eassumption.
    + intro. destruct_zmap. simpl. intros. pose proof (smmu_count _ H).
      Local Transparent count_smmu_map.
      destruct (z0 =? 0) eqn:Hz; bool_rel. srewrite.
      replace (phys_page 0 / 4096) with 0 in H by reflexivity. omega.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      assert(forall n, (Z.of_nat n <= smmu_id index cbndx) ->
                  count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) s0 =
                  count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl; autounfold in *. rewrite Hn. assert_gso.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. omega. omega. rewrite (ZMap.gso _ _ Hneq).
        rewrite IHn. reflexivity. omega. }
      pose proof (host_s2_map _ H0).
      assert(forall n, (Z.of_nat n > smmu_id index cbndx) ->
                  count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) s0 <=
                  count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) (spts s) - 1).
      { induction n. intros. autounfold in *. simpl in H5. omega.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        destruct (smmu_id index cbndx =? Z.of_nat n) eqn:Hsame. bool_rel.
        simpl; autounfold in *. rewrite Hn.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq.
        rewrite <- Hsame in *. rewrite ZMap.gss. simpl.
        remember ((index * 8 + cbndx) @ (smmu_vmid s)) as vmid0.
        symmetry in Heqvmid0. exploit (smmu_vm cbndx index); try eassumption.
        srewrite. assumption. intros.
        exploit spt_cons; try eapply C1; try eassumption. intros.
        exploit smmu_iso; try eapply C1; try eassumption.
        destruct (zeq vmid0 0). auto. right. split. omega.
        replace (0 <? vmid0) with true in C0 by (symmetry; bool_rel; omega).
        replace (vmid0 <? 16) with true in C0 by (symmetry; bool_rel; omega).
        simpl in C0. bool_rel. omega. intro. srewrite. inversion H7.
        intros (? & ?). srewrite. rewrite <- H9. rewrite ZMap.gss. rewrite <- Heq.
        replace (phys_page 0 / 4096 =? 0) with true by reflexivity.
        rewrite Heq. rewrite H9. rewrite C1.
        destruct_if. bool_rel. srewrite. inversion page_0_invalid.
        rewrite H3. omega. omega. rewrite <- H8. simpl_bool_eq.
        rewrite H3. omega. omega. omega. bool_rel.
        simpl. autounfold in *.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. rewrite Hn. assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
        match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if. apply IHn. omega.
        assert(Z.of_nat n > index * 8 + cbndx) by omega. apply IHn in H6. omega.
        apply IHn. omega. omega. }
      pose proof (H5 16%nat). replace (Pos.to_nat 16) with (16%nat) by reflexivity.
      assert(Z.of_nat 16 > smmu_id index cbndx). autounfold; simpl; omega.
      apply H6 in H7. replace (Z.to_nat 16) with 16%nat in H2 by reflexivity. omega.
      destruct (z0 =? 0) eqn:Hz; bool_rel.
      inv C2. apply smmu_count.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      pose proof (host_s2_map _ H0). srewrite.
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) s0 =
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. autounfold in *. rewrite Hn.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. destruct_zmap.
        remember ((index * 8 + cbndx) @ (smmu_vmid s)) as vmid0.
        symmetry in Heqvmid0. exploit (smmu_vm cbndx index); try eassumption.
        srewrite. assumption. intros.
        exploit spt_cons; try eapply C1; try eassumption. intros.
        exploit smmu_iso; try eapply C1; try eassumption.
        destruct (zeq vmid0 0). auto. right. split. omega.
        replace (0 <? vmid0) with true in C0 by (symmetry; bool_rel; omega).
        replace (vmid0 <? 16) with true in C0 by (symmetry; bool_rel; omega).
        simpl in C0. bool_rel. omega. intro. srewrite. inversion H4.
        intros (? & ?). srewrite. assert_gso. omega.
        rewrite (ZMap.gso _ _ Hneq). rewrite IHn. reflexivity.
        omega. rewrite IHn. reflexivity. omega. omega. }
      rewrite H2. apply smmu_count. autounfold; simpl. omega.
      Local Opaque count_smmu_map.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply spt_cons.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). intros until pte.
      destruct_zmap. destruct_zmap. intros. inv H1. reflexivity.
      rewrite <- Heq. eapply spt_cons; eassumption. apply spt_cons.
    + assumption. + assumption. + assumption. + assumption.
    + assumption. + assumption. + assumption.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply smmu_iso.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      rewrite Hn. intros until pte. destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      replace (phys_page 0 / PAGE_SIZE) with 0 in H by reflexivity.
      contra. rewrite <- Heq. eapply smmu_iso; eassumption. apply smmu_iso.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. assumption.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      intros. destruct (zeq pfn (phys_page z0 / 4096)).
      srewrite. intros. assert(s2_count (phys_page z0 / 4096) @ (s2page s) <= 0).
      bool_rel_all; omega.
      pose proof (smmu_count _ H).
      Local Transparent count_smmu_map.
      assert(forall n, count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) s0 <=
                  count_smmu_map n (phys_page z0 / 4096) (smmu_vmid s) (spts s)).
      { induction n. simpl. omega.
        simpl. rewrite Hn. destruct_zmap. destruct_zmap.
        replace (phys_page 0 / PAGE_SIZE =? 0) with true by reflexivity.
        match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega. }
      pose proof (H2 (Z.to_nat 16)). replace (Pos.to_nat 16) with (Z.to_nat 16) by reflexivity.
      omega.
      pose proof (host_s2_map _ H).
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) s0 <=
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n0. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. autounfold in *. rewrite Hn.
        replace (Z.of_nat n0 / 8 * 8) with (8 * (Z.of_nat n0 / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. destruct_zmap.
        assert(Z.of_nat n0 = index * 8 + cbndx) by omega. rewrite H2.
        destruct_zmap. replace (phys_page 0 / 4096 =? 0) with true by reflexivity.
        rewrite C1. rewrite IHn0. repeat destruct_if; try reflexivity. omega. omega.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega. omega. }
      assert(Z.of_nat (Pos.to_nat 16) <= EL2_SMMU_CFG_SIZE).
      simpl. autounfold. omega. apply H1 in H2.
      pose proof (smmu_count _ H).
      replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
      omega.
      Local Opaque count_smmu_map.
Qed.

Lemma free_smmu_pgd_inv:
  forall cbndx index s s' a b
    (ex: local_free_smmu_pgd cbndx index s = (s', false, a, b))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. assumption.
  destruct H. constructor; autounfold in *; simpl; try assumption.
  - intros. destruct_zmap. srewrite. rewrite ZMap.gss in H. contra.
    eapply smmu_vm; try eassumption. rewrite (ZMap.gso _ _ Heq) in H.
    assumption.
  - intros until pte. destruct_zmap. intros. omega.
    apply smmu_iso.
  - intros.
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) # index * 8 + cbndx == 4294967295 (spts s) <=
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        Local Transparent count_smmu_map.
        simpl; autounfold in *.
        destruct_zmap.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; bool_rel; try omega.
        assert(Z.of_nat n <= 16) by omega. apply IHn in H1.
        repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; omega.
        Local Opaque count_smmu_map. }
      assert(Z.of_nat (Pos.to_nat 16) <= EL2_SMMU_CFG_SIZE).
      simpl. autounfold. omega. apply H0 in H1.
      pose proof (smmu_count _ H).
      replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
      omega.
Qed.

Lemma alloc_smmu_pgd_inv:
  forall cbndx vmid index num s s' a b c
    (ex: local_alloc_smmu_pgd cbndx vmid index num s = (s', false, a, b, c))
    (Hvmid: HOSTVISOR <= vmid < COREVISOR)
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; try assumption.
  destruct H. constructor; autounfold in *; simpl; try assumption.
  - intros until pte. destruct_zmap. rewrite ZMap.gi. intros. inv H1. reflexivity.
    apply spt_cons.
  - intros. destruct_zmap. omega. apply smmu_vm; try assumption.
    rewrite (ZMap.gso _ _ Heq) in H. assumption.
  - intros until pte. destruct_zmap. rewrite ZMap.gi. intros.
    inv Hspt. contra. intros. assert_gsoH Hspt. omega.
    rewrite (ZMap.gso _ _ Hneq) in Hspt. eapply smmu_iso; eassumption.
  - intros.
    match goal with
    | |- _ >= count_smmu_map _ _ ?a ?b =>
      assert(forall n, (Z.of_nat n) <= EL2_SMMU_CFG_SIZE -> count_smmu_map n pfn a b <= count_smmu_map n pfn (smmu_vmid s) (spts s))
    end.
    { induction n. reflexivity.
      rewrite Nat2Z.inj_succ, succ_plus_1. intros.
      Local Transparent count_smmu_map.
      simpl; autounfold in *.
      replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
      rewrite <- Z_div_mod_eq.
      destruct_zmap.
      assert (Z.of_nat n = index * 8 + cbndx) by omega.
      rewrite H1 in *. rewrite ZMap.gi. simpl_bool_eq.
      repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
      repeat destruct_if; bool_rel; try omega.
      assert (Z.of_nat n <> index * 8 + cbndx) by omega.
      rewrite (ZMap.gso _ _ H1).
      assert(Z.of_nat n <= 16) by omega. apply IHn in H2.
      repeat match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
      repeat destruct_if; omega. omega.
      Local Opaque count_smmu_map. }
    assert(Z.of_nat (Pos.to_nat 16) <= EL2_SMMU_CFG_SIZE).
    simpl. autounfold. omega. apply H0 in H1.
    pose proof (smmu_count _ H).
    replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
    omega.
Qed.

Lemma set_vm_poweroff_inv:
  forall vmid s s' a
    (ex: local_set_vm_poweroff vmid s = (s', a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  - intros until pte. destruct_zmap. simpl. intros. omega.
    apply vm_iso.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply smmu_iso; try eassumption. destruct Hvalid_vmid; omega.
    apply smmu_iso.
Qed.

Lemma load_encrypted_vcpu_inv:
  forall vmid vcpuid cregs cstates dorc logn s s' cr cs n' a
    (ex: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s = (s', false, cr, cs, n', a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply vm_iso; try eassumption.
    apply vm_iso.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply smmu_iso; try eassumption.
    apply smmu_iso.
Qed.

Lemma load_save_encrypt_buf_inv:
  forall vmid inbuf outbuf dorc logn s s' n' a b
    (ex: local_save_encrypt_buf vmid inbuf outbuf dorc logn s = (s', false, n', a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
Qed.

Lemma load_load_decrypt_buf_inv:
  forall vmid inbuf dorc logn s s' n' a b c d
    (Hvalid_vm: valid_vm vmid)
    (ex: local_load_decrypt_buf vmid inbuf dorc logn s = (s', false, n', a, b, c, d)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; bool_rel_all.
  pose proof (smmu_count_0_no_map _ H _ Hcond Hcond0) as Hcount0.
  destruct H; autounfold in *; bool_rel_all.
  destruct (z =? 0) eqn:Hz.
  - inv C3; bool_rel; srewrite.
    replace z0 with 0 in *.
    rewrite zmap_set_id.
    constructor; autounfold; simpl; try assumption.
    + intro. destruct_zmap. simpl. intros; omega. apply host_s2_map.
    + assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
      rewrite (ZMap.gso _ _ Hneq). assumption.
    + intros. destruct_zmap. rewrite Heq in *.
      rewrite (host_flatmap _ _ _ _ Hpfn) in Hpfn. rewrite C1 in Hpfn. inv Hpfn.
      rewrite H0 in Hexists. contra. assumption. eapply host_iso; try eassumption.
    + intros. destruct_zmap. rewrite Heq in *.
      exploit (vm_iso _ _ _ _ _ H); try eassumption. omega.
      intros. rewrite Hcond in H4. omega. rewrite (ZMap.gso _ _ Heq) in H3.
      eapply vm_iso; eassumption.
    + intros. destruct_zmap. simpl. rewrite Heq in *.
      exploit (smmu_iso vmid0 cbndx index gfn pfn pte); try eassumption.
      rewrite Heq. assumption. omega.
      intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
      rewrite H0. assumption. rewrite Heq. apply Hspt. eapply smmu_iso; eassumption.
    + intro. destruct_zmap. simpl; intros.
      rewrite <- Hcond0. eapply smmu_count; eassumption. eapply smmu_count.
    + pose proof (host_npt_cons _ _ _ _ C1). rewrite H. reflexivity.
  - pose proof (local_mmap_level3 _ _ _ _ _ C3).
    constructor; autounfold; simpl; try assumption.
    + intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
      intro T. inv T. reflexivity. apply host_npt_cons.
    + intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
      intros. inv H0. contra. apply host_flatmap.
    + intro. destruct_zmap. simpl. intros; omega. apply host_s2_map.
    + assert_gso. red; intro T. rewrite T in page_0_invalid. omega.
      rewrite (ZMap.gso _ _ Hneq). assumption.
    + rewrite ZMap.gss. rewrite H. intros until pte.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
      destruct_zmap. intros. inv Hpfn. contra.
      intros. autounfold in *. assert_gso. red; intro.
      inv H0. pose proof (host_flatmap _ _ _ _ Hpfn Hexists). inv H0.
      apply Heq. rewrite Z_div_mult_full. reflexivity. omega.
      rewrite (ZMap.gso _ _ Hneq). eapply host_iso; eassumption.
    + intros. destruct_zmap. rewrite Heq in *.
      assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
      exploit (vm_iso _ _ _ _ _ H0); try eassumption. omega. intros.
      rewrite Hcond in H5. omega.
      assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
      rewrite (ZMap.gso _ _ Heq) in H4. eapply vm_iso; eassumption.
    + intros. destruct_zmap. simpl. rewrite Heq in *.
      exploit (smmu_iso vmid0 cbndx index gfn pfn pte); try eassumption.
      rewrite Heq. assumption. omega.
      intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
      rewrite H1. assumption.
      rewrite Heq. apply Hspt. eapply smmu_iso; eassumption.
    + intro. destruct_zmap. simpl; intros.
      rewrite <- Hcond0. eapply smmu_count; eassumption. eapply smmu_count.
Qed.

Lemma mem_load_inv:
  forall gfn reg d d'
    (spec: mem_load_spec gfn reg d = Some d')
    (halt0: halt d = false)
    (halt': halt d' = false)
    (Hinv: state_inv d),
    state_inv d'.
Proof.
  intros; hsimpl_func spec.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
  rewrite ZMap.gss.
  pose proof (set_shadow_ctxt_dirty _ _ _ _  _ _ C3).
  simpl in *. rewrite H. assumption. autounfold; bool_rel; omega.
Qed.

Lemma mem_store_inv:
  forall gfn reg d d'
    (spec: mem_store_spec gfn reg d = Some d')
    (halt0: halt d = false)
    (halt': halt d' = false)
    (Hinv: state_inv d),
    state_inv d'.
Proof.
  intros; hsimpl_func spec.
  extract_adt C2 dq.
  destruct Hinv.
  assert(shared_inv (shared dq)).
  rewrite Heqdq; apply oracle_inv. assumption.
  autounfold in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; try assumption.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
  extract_adt C2 dq.
  destruct Hinv.
  assert(shared_inv (shared dq)).
  rewrite Heqdq; apply oracle_inv. assumption.
  autounfold in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; try assumption.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
Qed.

Lemma dev_load_inv:
  forall gfn reg cbndx index d d'
    (spec: dev_load_spec gfn reg cbndx index d = Some d')
    (halt0: halt d = false)
    (halt': halt d' = false)
    (Hinv: state_inv d),
    state_inv d'.
Proof.
  intros; hsimpl_func spec.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
  rewrite ZMap.gss.
  pose proof (set_shadow_ctxt_dirty _ _ _ _  _ _ C6).
  simpl in *. rewrite H. assumption. autounfold; bool_rel; omega.
Qed.

Lemma dev_store_inv:
  forall gfn reg cbndx index d d'
    (spec: dev_store_spec gfn reg cbndx index d = Some d')
    (halt0: halt d = false)
    (halt': halt d' = false)
    (Hinv: state_inv d),
    state_inv d'.
Proof.
  intros; hsimpl_func spec.
  extract_adt C3 dq.
  destruct Hinv.
  assert(shared_inv (shared dq)).
  rewrite Heqdq; apply oracle_inv. assumption.
  autounfold in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; try assumption.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
  extract_adt C3 dq.
  destruct Hinv.
  assert(shared_inv (shared dq)).
  rewrite Heqdq; apply oracle_inv. assumption.
  autounfold in *. rewrite Heqdq in *.
  constructor; autounfold; simpl; try assumption.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  destruct Hinv; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  apply oracle_inv. assumption.
Qed.
```
