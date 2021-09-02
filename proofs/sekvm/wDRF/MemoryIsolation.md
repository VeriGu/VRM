# MemoryIsolation

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
Require Import TrapHandler.Spec.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.ltb Z.geb Z.gtb.

Fixpoint count_smmu_map (n: nat) (pfn: Z) (smmu: ZMap.t Z) (spt: SPT) :=
  match n with
  | O => 0
  | S n' =>
    let k := count_smmu_map n' pfn smmu spt in
    let smmuid := Z.of_nat n' in
    let index := smmuid / SMMU_NUM_CTXT_BANKS in
    let cbndx := smmuid mod SMMU_NUM_CTXT_BANKS in
    let vmid := smmuid @ smmu in
    let gfn := pfn + SMMU_HOST_OFFSET in
    let (pfn0, pte) := gfn @ ((SMMU_TTBR index cbndx) @ (spt_pt spt)) in
    if pfn0 =? 0 then k else if vmid =? HOSTVISOR then k + 1 else k
  end.

Record shared_inv (sdt: Shared) :=
  {
    spt_cons:
      forall cbndx index gfn pfn pte,
        valid_smmu index -> valid_smmu_cfg cbndx ->
        let spt := (SMMU_TTBR index cbndx) @ (spt_pt (spts sdt)) in
        gfn @ spt = (pfn, pte) -> pfn = phys_page pte / PAGE_SIZE;

    host_npt_cons:
      forall gfn pfn level pte,
        let npt := ZMap.get HOSTVISOR (npts sdt) in
        gfn @ (pt npt) = (pfn, level, pte) -> pfn = phys_page pte / PAGE_SIZE;

    host_flatmap:
      forall gfn pfn level pte,
        let npt := ZMap.get HOSTVISOR (npts sdt) in
        gfn @ (pt npt) = (pfn, level, pte) -> pfn <> 0 -> gfn = pfn;

    host_s2_map:
      forall pfn, s2_owner (pfn @ (s2page sdt)) = HOSTVISOR -> s2_gfn (pfn @ (s2page sdt)) = pfn + SMMU_HOST_OFFSET;

    page_0_invalid:
      s2_owner (0 @ (s2page sdt)) = INVALID;

    host_iso:
      let npt := HOSTVISOR @ (npts sdt) in
      forall gfn pfn level pte
        (Hpfn: gfn @ (pt npt) = (pfn, level, pte))
        (Hexists: pfn <> 0),
        let page := pfn @ (s2page sdt) in
        s2_owner page = INVALID \/ (s2_owner page = HOSTVISOR \/ s2_count page > 0);

    vm_iso:
      forall vmid gfn pfn level pte,
        let npt := vmid @ (npts sdt) in
        gfn @ (pt npt) = (pfn, level, pte) ->
        HOSTVISOR < vmid < COREVISOR ->
        vm_state (VS (vmid @ (vminfos sdt))) <= VERIFIED ->
        pfn <> 0 ->
        let page := pfn @ (s2page sdt) in
        s2_owner page <> INVALID -> s2_owner page = vmid;

    smmu_vm:
      forall cbndx index (Hvalid_smmu: valid_smmu index) (Hvalid_cfg: valid_smmu_cfg cbndx),
        (smmu_id index cbndx) @ (smmu_vmid sdt) <> INVALID ->
        HOSTVISOR <= (smmu_id index cbndx) @ (smmu_vmid sdt) < COREVISOR;

    smmu_iso:
      forall vmid cbndx index gfn pfn pte
        (Hsmmu: (smmu_id index cbndx) @ (smmu_vmid sdt) = vmid)
        (Hspt: gfn @ ((SMMU_TTBR index cbndx) @ (spt_pt (spts sdt))) = (pfn, pte))
        (Hvalid_smmu: valid_smmu index) (Hvalid_cfg: valid_smmu_cfg cbndx)
        (Hvalid_vmid: (vmid = HOSTVISOR \/ (valid_vm vmid /\ vm_state (VS (vmid @ (vminfos sdt))) <= VERIFIED))),
        pfn <> 0 ->
        let page := pfn @ (s2page sdt) in
        s2_owner page = (smmu_id index cbndx) @ (smmu_vmid sdt) /\ s2_gfn page = gfn;

    smmu_count:
      forall pfn, s2_owner (pfn @ (s2page sdt)) = HOSTVISOR ->
             s2_count (pfn @ (s2page sdt)) >= count_smmu_map (Z.to_nat EL2_SMMU_CFG_SIZE) pfn (smmu_vmid sdt) (spts sdt);

    remap_ptr:
      next_remap_ptr (core_data sdt) > 0;

    core_map:
      forall gfn (Hgfn: next_remap_ptr (core_data sdt) / PAGE_SIZE <= gfn),
      match gfn @ (pt (COREVISOR @ (npts sdt))) with
      | (pfn, level, pte) => pfn = 0
      end;

    remap_addr:
      forall vmid load_idx (Hload_idx: 0 <= load_idx < vm_next_load_info (VB (vmid @ (vminfos sdt)))),
        let boot := VB (vmid @ (vminfos sdt)) in
        let size := load_idx @ (vm_load_size boot) in
        let remap := load_idx @ (vm_remap_addr boot) in
        let mapped := load_idx @ (vm_mapped_pages boot) in
        let pgnum := (size + 4095) / PAGE_SIZE in
        mapped <= pgnum /\ remap / PAGE_SIZE + pgnum <= next_remap_ptr (core_data sdt) / PAGE_SIZE;

    core_remap:
      forall vmid load_idx (Hload_idx: 0 <= load_idx < vm_next_load_info (VB (vmid @ (vminfos sdt)))),
        let boot := VB (vmid @ (vminfos sdt)) in
        let size := load_idx @ (vm_load_size boot) in
        let remap := load_idx @ (vm_remap_addr boot) in
        let mapped := load_idx @ (vm_mapped_pages boot) in
        let pgnum := (size + 4095) / PAGE_SIZE in
        forall gfn (Hgfn: remap / PAGE_SIZE + mapped <= gfn < remap / PAGE_SIZE + pgnum),
        match gfn @ (pt (COREVISOR @ (npts sdt))) with
        | (pfn, level, pte) => pfn = 0
        end;

    remap_range:
      forall vmid load_idx,
        let boot := VB (vmid @ (vminfos sdt)) in
        let size := load_idx @ (vm_load_size boot) in
        let remap := load_idx @ (vm_remap_addr boot) in
        let mapped := load_idx @ (vm_mapped_pages boot) in
        size >= 0 /\ remap >= 0 /\ mapped >= 0;

    remap_no_overlap:
      forall vmid1 load_idx1 vmid2 load_idx2
        (Hload_idx1: 0 <= load_idx1 < vm_next_load_info (VB (vmid1 @ (vminfos sdt))))
        (Hload_idx2: 0 <= load_idx2 < vm_next_load_info (VB (vmid2 @ (vminfos sdt))))
        (Hnot_same: vmid1 <> vmid2 \/ load_idx1 <> load_idx2),
        let boot1 := VB (vmid1 @ (vminfos sdt)) in
        let size1 := load_idx1 @ (vm_load_size boot1) in
        let remap1 := load_idx1 @ (vm_remap_addr boot1) in
        let pgnum1 := (size1 + 4095) / PAGE_SIZE in
        let boot2 := VB (vmid2 @ (vminfos sdt)) in
        let size2 := load_idx2 @ (vm_load_size boot2) in
        let remap2 := load_idx2 @ (vm_remap_addr boot2) in
        let pgnum2 := (size2 + 4095) / PAGE_SIZE in
        remap1 / PAGE_SIZE >= (remap2 / PAGE_SIZE + pgnum2) \/ remap2 / PAGE_SIZE >= (remap1 / PAGE_SIZE + pgnum1)
  }.

Lemma smmu_count_0_no_map:
  forall sdt (Hinv: shared_inv sdt) pfn,
    s2_owner (pfn @ (s2page sdt)) = HOSTVISOR -> s2_count (pfn @ (s2page sdt)) = 0 ->
    forall index cbndx, valid_smmu index -> valid_smmu_cfg cbndx -> (smmu_id index cbndx) @ (smmu_vmid sdt) = HOSTVISOR ->
                   forall gfn0 pfn0 pte0, gfn0 @ ((SMMU_TTBR index cbndx) @ (spt_pt (spts sdt))) = (pfn0, pte0) -> pfn0 <> pfn.
Proof.
  Local Transparent Z.add Z.mul Z.div.
  intros. red. intros. inv H4.
  destruct Hinv; autounfold in *.
  pose proof (smmu_count0 pfn H). rewrite H0 in H4.
  assert(pfn <> 0). red. intros. rewrite H5 in H.
  rewrite page_0_invalid0 in H. inversion H.
  remember ((index * 8 + cbndx) @ (smmu_vmid sdt)) as vmid.
  symmetry in Heqvmid.
  exploit smmu_iso0; try eapply H7; try eauto.
  intros (? & ?); srewrite; clear_hyp.
  assert(forall n,  count_smmu_map n pfn (smmu_vmid sdt) (spts sdt) >= 0).
  induction n. simpl. omega.
  simpl. match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
  repeat destruct_if; omega.
  assert(forall n, Z.of_nat n > smmu_id index cbndx -> count_smmu_map n pfn (smmu_vmid sdt) (spts sdt) >= 1).
  induction n. simpl. intros; autounfold in *; omega.
  rewrite Nat2Z.inj_succ, succ_plus_1. intros.
  destruct (Z.of_nat n >? smmu_id index cbndx) eqn:Hcase; bool_rel.
  assert(count_smmu_map n pfn (smmu_vmid sdt) (spts sdt) >= 1) by (apply IHn; omega).
  simpl. match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
  repeat destruct_if; omega.
  assert(smmu_id index cbndx = Z.of_nat n) by omega.
  simpl count_smmu_map. autounfold in *.
  rewrite <- H10.
  assert((index * 8 + cbndx) / 8 = index).
  rewrite Z_div_plus_full_l. rewrite Zdiv_small. omega. assumption. omega.
  assert((index * 8 + cbndx) mod 8 = cbndx).
  rewrite Z.add_comm. rewrite Z_mod_plus_full. rewrite Zmod_small. reflexivity. omega.
  rewrite H11, H12. rewrite host_s2_map0 in H8. srewrite. destruct_if. bool_rel; contra.
  simpl_bool_eq. pose proof (H n). omega. assumption.
  assert(count_smmu_map 16 pfn (smmu_vmid sdt) (spts sdt) >= 1).
  apply H9. autounfold in *. simpl. omega.
  replace (Z.to_nat 16) with (16%nat) in H4 by reflexivity. omega.
  Local Opaque Z.add Z.mul Z.div.
Qed.

Local Opaque count_smmu_map.

Record state_inv (adt: RData) :=
  {
    shared_invariant: shared_inv (shared adt);

    curid_range: valid_vcpu (curid adt);
    cur_vmid_range: valid_vmid (cur_vmid adt);
    cur_vcpuid_range: valid_vcpu (cur_vcpuid adt);
    valid_host_vmid: ihost adt = true -> icore adt = false -> cur_vmid adt = HOSTVISOR;
    valid_host_vcpuid: cur_vmid adt = HOSTVISOR -> cur_vcpuid adt = curid adt;
    valid_core_vcpuid: cur_vmid adt = COREVISOR -> cur_vcpuid adt = curid adt;
    valid_vm_vmid: ihost adt = false -> icore adt = false -> valid_vm (cur_vmid adt);
    run_vcpu_dirty:
      dirty (ctxt_states (ctxt_id (cur_vmid adt) (cur_vcpuid adt)) @ (shadow_ctxts adt)) =? INVALID64 = false
  }.

Hypothesis oracle_inv: forall d,  shared_inv (shared d) -> shared_inv (shared (query_oracle d)).

(***********************************************************************************************************************************)

Ltac extract_adt H name :=
  match type of H with
  | context[query_oracle ?a] => remember (query_oracle a) as name
  end.

(*****************************************************************************************************************************************************)

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
  destruct_zmap. intros. inv H. reflexivity. apply host_npt_cons0.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H.
  rewrite host_pte_pfn_dev. reflexivity.  assumption.
  apply host_flatmap0.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv Hpfn. rewrite host_pte_pfn_dev; try assumption.
  left. assumption. apply host_iso0.
  intros. assert_gsoH H. red; intro. subst. omega. rewrite (ZMap.gso _ _ Hneq) in H.
  eapply vm_iso0; eassumption.
  rewrite ZMap.gso. assumption. intro T; inversion T.
  rewrite ZMap.gso. assumption. intro T; inversion T.
  pose proof (local_mmap_level3 _ _ _ _ _ C0) as Hn.
  destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H. reflexivity. apply host_npt_cons0.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv H.
  rewrite host_pte_pfn_mem. reflexivity.  assumption.
  apply host_flatmap0.
  rewrite ZMap.gss. intros until pte. rewrite Hn.
  destruct_zmap. intros. inv Hpfn. rewrite host_pte_pfn_mem; try assumption.
  right. bool_rel_all; autounfold in *; omega. apply host_iso0.
  intros. assert_gsoH H. red; intro. subst. omega. rewrite (ZMap.gso _ _ Hneq) in H.
  eapply vm_iso0; eassumption.
  rewrite ZMap.gso. assumption. intro T; inversion T.
  rewrite ZMap.gso. assumption. intro T; inversion T.
Qed.

Lemma map_host_core_iso:
  forall addr s s' a b
    (ex: local_map_host addr s = (s', false, a, b))
    (Haddr: valid_addr addr)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros. hsimpl_func ex; simpl; try omega.
Qed.

Lemma Z_div_le_le:
  forall a b c d, 0 < d -> a <= b <= c -> a / d <= b / d <= c / d.
Proof.
  intros. destruct H0; split; apply Z_div_le; assumption.
Qed.

Lemma clear_vm_page_inv:
  forall vmid pfn s s' a b c
    (ex: local_clear_vm_page vmid pfn s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (valid_state': vm_state (VS (vmid @ (vminfos s))) = POWEROFF),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; bool_rel; try assumption.
  destruct H; autounfold in *.
  assert(Hcount0: forall n, 0 <= Z.of_nat n <= EL2_SMMU_CFG_SIZE -> count_smmu_map n pfn (smmu_vmid s) (spts s) = 0).
  { Local Transparent count_smmu_map.
    induction n0. intros; reflexivity.
    rewrite Nat2Z.inj_succ, succ_plus_1. intros.
    simpl. rewrite IHn0. repeat destruct_if; try omega.
    match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) eqn: Hsp end.
    autounfold in *; bool_rel. destruct_if; try reflexivity; bool_rel.
    exploit (smmu_iso0 0 (Z.of_nat n0 mod 8) (Z.of_nat n0 / 8) (pfn + 1000000000) z2 z3);
      autounfold; try eassumption; try omega.
    rewrite Z.mul_comm. rewrite <- Z.div_mod. assumption. omega.
    assert(0 <= Z.of_nat n0 <= 15) by omega.
    assert(0 <= Z.of_nat n0 / 8 <= 1).
    eapply (Z_div_le_le 0 _ 15 8); omega. omega.
    apply Z_mod_lt; omega.
    intros (? & ?).
    rewrite Z.mul_comm, <- Z.div_mod in H0; try omega.
    rewrite Case in H0.
    pose proof (host_s2_map0 z2 H0). rewrite H1 in H2.
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
  apply host_s2_map0. rewrite (ZMap.gso _ _ Heq) in H. assumption.
  assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
  rewrite (ZMap.gso _ _ Hneq). assumption.
  intros. destruct_zmap. simpl. auto.
  eapply host_iso0; try eassumption.
  intros. destruct_zmap. srewrite.
  exploit (vm_iso0 _ _ _ _ _ H); try eassumption. omega.
  intros. srewrite. omega. eapply vm_iso0; try eassumption.
  rewrite (ZMap.gso _ _ Heq) in H3. assumption.
  intros. destruct_zmap. rewrite Heq in *.
  exploit (smmu_iso0 vmid cbndx index gfn pfn pte); try eassumption.
  intros (? & ?). srewrite. destruct Hvalid_vmid; omega.
  eapply smmu_iso0; eassumption.
  intro. destruct_zmap. simpl; intros.
  rewrite Hcount0. omega. simpl; autounfold. omega.
  apply smmu_count0. pose proof (host_npt_cons0 _ _ _ _ C0).
  rewrite H. reflexivity.
  pose proof (local_mmap_level3 _ _ _ _ _ C2).
  constructor; autounfold; simpl; try assumption.
  intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
  intro T. inv T. reflexivity. apply host_npt_cons0.
  intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
  replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
  intros. inv H0. contra. apply host_flatmap0.
  intros. destruct_zmap. simpl. reflexivity.
  apply host_s2_map0. rewrite (ZMap.gso _ _ Heq) in H0. assumption.
  assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
  rewrite (ZMap.gso _ _ Hneq). assumption.
  rewrite ZMap.gss. intros until pte. rewrite H.
  replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
  destruct_zmap. intros. destruct_zmap. simpl. auto. inv Hpfn. contra.
  destruct_zmap. simpl. intros; auto.
  eapply host_iso0; try eassumption.
  intros. assert_gsoH H0. red; intro. rewrite H5 in H1; omega.
  rewrite (ZMap.gso _ _ Hneq) in H0.
  destruct_zmap. srewrite.
  exploit (vm_iso0 _ _ _ _ _ H0); try eassumption. omega.
  intros. srewrite. omega. eapply vm_iso0; try eassumption.
  rewrite (ZMap.gso _ _ Heq) in H4. assumption.
  intros. destruct_zmap. rewrite Heq in *.
  exploit (smmu_iso0 vmid0 cbndx index gfn pfn pte); try eassumption.
  intros (? & ?). srewrite. destruct Hvalid_vmid; omega.
  eapply smmu_iso0; eassumption.
  intro. destruct_zmap. simpl; intros.
  rewrite Hcount0. omega. simpl; autounfold. omega.
  apply smmu_count0.
  rewrite ZMap.gso. assumption. intro T; inversion T.
  rewrite ZMap.gso. assumption. intro T; inversion T.
Qed.

Lemma clear_vm_page_core_iso:
  forall vmid pfn s s' a b c
    (ex: local_clear_vm_page vmid pfn s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (valid_state': vm_state (VS (vmid @ (vminfos s))) = POWEROFF)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_zmap; simpl; omega.
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
      * intro. destruct_zmap. simpl. intros; omega. apply host_s2_map0.
      * assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
        rewrite (ZMap.gso _ _ Hneq). assumption.
      * intros. destruct_zmap. rewrite Heq in *.
        rewrite (host_flatmap0 _ _ _ _ Hpfn) in Hpfn. rewrite C1 in Hpfn. inv Hpfn.
        contra. assumption. eapply host_iso0; try eassumption.
      * intros. destruct_zmap. rewrite Heq in *.
        exploit (vm_iso0 _ _ _ _ _ H); try eassumption. omega.
        intros. rewrite C in H4. omega. rewrite (ZMap.gso _ _ Heq) in H3.
         eapply vm_iso0; eassumption.
      * intros. destruct_zmap. simpl. rewrite Heq in *.
        exploit (smmu_iso0 vmid0 cbndx index gfn0 pfn pte); try eassumption.
        intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
        rewrite Heq. apply Hspt. eapply smmu_iso0; eassumption.
      * intro. destruct_zmap. simpl; intros.
        rewrite <- C0. eapply smmu_count0; eassumption. eapply smmu_count0.
      * pose proof (host_npt_cons0 _ _ _ _ C1). rewrite H. reflexivity.
    + pose proof (local_mmap_level3 _ _ _ _ _ C3).
      constructor; autounfold; simpl; try assumption.
      * intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
        intro T. inv T. reflexivity. apply host_npt_cons0.
      * intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
        intros. inv H0. contra. apply host_flatmap0.
      * intro. destruct_zmap. simpl. intros; omega. apply host_s2_map0.
      * assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
        rewrite (ZMap.gso _ _ Hneq). assumption.
      * rewrite ZMap.gss. rewrite H. intros until pte.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
        destruct_zmap. intros. inv Hpfn. contra.
        intros. autounfold in *. assert_gso. red; intro.
        inv H0. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists). inv H0.
        apply Heq. rewrite Z_div_mult_full. reflexivity. omega.
        rewrite (ZMap.gso _ _ Hneq). eapply host_iso0; eassumption.
      * intros. destruct_zmap. rewrite Heq in *.
        assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
        exploit (vm_iso0 _ _ _ _ _ H0); try eassumption. omega. intros.
        rewrite C in H5. omega.
        assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
        rewrite (ZMap.gso _ _ Heq) in H4. eapply vm_iso0; eassumption.
      * intros. destruct_zmap. simpl. rewrite Heq in *.
        exploit (smmu_iso0 vmid0 cbndx index gfn0 pfn pte); try eassumption.
        intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
        rewrite Heq. apply Hspt. eapply smmu_iso0; eassumption.
      * intro. destruct_zmap. simpl; intros.
        rewrite <- C0. eapply smmu_count0; eassumption. eapply smmu_count0.
      * rewrite ZMap.gso. assumption. intro T; inversion T.
      * rewrite ZMap.gso. assumption. intro T; inversion T.
  - rewrite zmap_set_id. destruct s; simpl in *. assumption.
Qed.

Lemma assign_pfn_to_vm_core_iso:
  forall vmid gfn pfn dorc logn s s' n a b c
    (ex: local_assign_pfn_to_vm vmid gfn pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_zmap; simpl; omega.
  destruct_zmap; simpl; omega.
Qed.

Lemma map_pfn_vm_inv:
  forall vmid addr pte level s s' a
    (ex: local_map_pfn_vm vmid addr pte level s = (s', false, a))
    (Howner: forall pfn, (if level =? 2 then phys_page pte / PAGE_SIZE <= pfn < phys_page pte / PAGE_SIZE + 512
                     else pfn = phys_page pte / PAGE_SIZE) -> s2_owner (pfn @ (s2page s)) = vmid)
    (valid_vm: valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  Local Transparent Z.sub.
  intros. hsimpl_func ex; bool_rel; try assumption.
  duplicate H; destruct H; autounfold in *.
  assert(Hnhost: 0 <> vmid) by omega.
  constructor; autounfold; simpl; repeat rewrite (ZMap.gso _ _ Hnhost); try assumption.
  intros until pte0. destruct_zmap; try eapply vm_iso0. inv Heq.
  intros. destruct (level =? 2) eqn:Hlevel.
  - pose proof (local_mmap_level2 _ _ _ _ _ C gfn) as Hn.
    rewrite vm_pte_pfn_level2 in Hn.
    destruct in_range_n in Hn. rewrite H in Hn. inv Hn. simpl.
    apply Howner. autounfold in *. omega. rewrite Hn in H.
    eapply vm_iso0; try eassumption.
  - pose proof (local_mmap_level3 _ _ _ _ _ C) as Hn.
    rewrite Hn in H. destruct (gfn =? addr / PAGE_SIZE) eqn:Hsame.
    bool_rel. rewrite Hsame in H. rewrite ZMap.gss in H. inv H.
    rewrite vm_pte_pfn_level3 in *. apply Howner; reflexivity.
    bool_rel. rewrite (ZMap.gso _ _ Hsame) in H.
    eapply vm_iso0; eassumption.
  - rewrite ZMap.gso. assumption. intro T. subst; omega.
  - rewrite ZMap.gso. assumption. intro T. subst; omega.
Qed.

Lemma map_pfn_vm_iso:
  forall vmid addr pte level s s' a
    (ex: local_map_pfn_vm vmid addr pte level s = (s', false, a))
    (Howner: forall pfn, (if level =? 2 then phys_page pte / PAGE_SIZE <= pfn < phys_page pte / PAGE_SIZE + 512
                     else pfn = phys_page pte / PAGE_SIZE) -> s2_owner (pfn @ (s2page s)) = vmid)
    (valid_vm: valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
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
  intros until pte. destruct_zmap; try eapply vm_iso0. inv Heq.
  intros. rewrite (local_mmap_level3 _ _ _ _ _ C1) in H.
  destruct (gfn =? gpa / PAGE_SIZE) eqn:Hsame; bool_rel; subst.
  rewrite ZMap.gss in H. inv H.
  rewrite vm_pte_pfn_dev in H3; try assumption. autounfold in H3; omega.
  rewrite (ZMap.gso _ _ Hsame) in H. eapply vm_iso0; eassumption.
  rewrite ZMap.gso. assumption. intro T. subst; omega.
  rewrite ZMap.gso. assumption. intro T. subst; omega.
Qed.

Lemma map_io_core_iso:
  forall vmid gpa pa s s' a b c
    (ex: local_map_io vmid gpa pa s = (s', false, a, b, c))
    (valid_addr: valid_paddr pa)
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
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
      eapply host_s2_map0; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. inv Heq.
      intros. pose proof (host_iso0 _ _ _ _ Hpfn Hexists).
      simpl. omega. apply host_iso0.
    + intros until pte. destruct_zmap. inv Heq.
      simpl. apply vm_iso0. apply vm_iso0.
    + intros until pte. destruct_zmap. inv Heq. simpl.
      apply smmu_iso0. apply smmu_iso0.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count0.
  - destruct s; simpl in *; assumption.
Qed.

Lemma grant_vm_page_core_iso:
  forall vmid pfn s s' a
    (ex: local_grant_vm_page vmid pfn s = (s', a))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_if. destruct_zmap; simpl; omega. omega.
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
        eapply host_s2_map0; eassumption.
      * destruct_zmap. inv Heq. omega. assumption.
      * intros until pte. destruct_zmap. intros.
        simpl. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists).
        inv H. pose proof (host_npt_cons0 _ _ _ _ C1).
        rewrite C1 in Hpfn. inv Hpfn.
        replace (phys_page 0 / 4096) with 0 in H1 by reflexivity. omega.
        apply host_iso0.
      * intros until pte. destruct_zmap. inv Heq.
        simpl. apply vm_iso0. apply vm_iso0.
      * intros until pte. destruct_zmap. inv Heq. simpl.
        apply smmu_iso0. apply smmu_iso0.
      * intro. destruct_zmap. inv Heq. simpl. intros. omega.
        apply smmu_count0.
    + pose proof (local_mmap_level3 _ _ _ _ _ C3) as Hn.
      constructor; autounfold; simpl; try assumption.
      * rewrite ZMap.gss. intros until pte. rewrite Hn.
        destruct_zmap. intros. inv H. reflexivity.
        apply host_npt_cons0.
      * rewrite ZMap.gss. intros until pte. rewrite Hn.
        destruct_zmap. intros. inv H.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in H0 by reflexivity.
        contra. apply host_flatmap0.
      * intro pfn0. destruct_zmap. simpl. intros; omega.
        eapply host_s2_map0; eassumption.
      * destruct_zmap. simpl. rewrite <- Heq. eapply page_0_invalid0. assumption.
      * rewrite ZMap.gss. rewrite Hn. intros until pte.
        destruct_zmap. intros. inv Hpfn.
        replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in Hexists by reflexivity.
        contra. intros. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists).
        rewrite Z_div_mult_full in Heq. rewrite H in Heq. rewrite (ZMap.gso _ _ Heq).
        eapply host_iso0; eassumption. autounfold; omega.
      * intros until pte. intros. assert_gsoH H. red; intro; srewrite; omega.
        rewrite (ZMap.gso _ _ Hneq) in H.
        destruct_zmap. inv Heq. simpl. eapply vm_iso0; try eassumption.
        rewrite ZMap.gss in H3. simpl in H3. assumption.
        eapply vm_iso0; try eassumption. rewrite (ZMap.gso _ _ Heq) in H3. assumption.
      * intros until pte. destruct_zmap. inv Heq. simpl.
        apply smmu_iso0. apply smmu_iso0.
      * intro. destruct_zmap. inv Heq. simpl. intros. omega.
        apply smmu_count0.
      * rewrite ZMap.gso. assumption. intro T. inv T.
      * rewrite ZMap.gso. assumption. intro T. inv T.
  - bool_rel_all. destruct H; autounfold in *.
    constructor; autounfold; simpl; try assumption.
    + intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
      eapply host_s2_map0; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. inv Heq.
      intros. pose proof (host_iso0 _ _ _ _ Hpfn Hexists).
      simpl. omega. apply host_iso0.
    + intros until pte. destruct_zmap. inv Heq.
      simpl. apply vm_iso0. apply vm_iso0.
    + intros until pte. destruct_zmap. inv Heq. simpl.
      apply smmu_iso0. apply smmu_iso0.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count0.
  - assumption.
Qed.

Lemma revoke_vm_page_core_iso:
  forall vmid pfn dorc logn s s' a b c n
    (ex: local_revoke_vm_page vmid pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_zmap; simpl; omega.
  destruct_zmap; simpl; omega.
Qed.

Lemma set_vcpu_active_inv:
  forall vmid vcpuid s s' a
    (ex: local_set_vcpu_active vmid vcpuid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso0.
  intros until pte. destruct_zmap; simpl; apply smmu_iso0.
  intros. destruct_zmap; simpl.
  rewrite Heq in *. rewrite ZMap.gss in Hload_idx.
  eapply remap_addr0. assumption.
  rewrite (ZMap.gso _ _ Heq) in Hload_idx.
  eapply remap_addr0. assumption.
  intros. destruct (zeq vmid0 vmid). subst.
  rewrite ZMap.gss in *; simpl in *.
  eapply (core_remap0 vmid load_idx Hload_idx). assumption.
  rewrite (ZMap.gso _ _ n) in Hgfn, Hload_idx.
  eapply (core_remap0 vmid0 load_idx Hload_idx). assumption.
  intros. destruct_zmap; simpl; apply remap_range0.
  intros.
  destruct (zeq vmid vmid1), (zeq vmid vmid2);
    repeat subst; repeat rewrite ZMap.gss in *; simpl in *.
  eapply remap_no_overlap0; assumption.
  rewrite ZMap.gso. eapply remap_no_overlap0. assumption.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  left. assumption. intro T; inv T; contra.
  rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  assumption. left. intro T; inv T; contra. intro T; inv T; contra.
  rewrite ZMap.gso. rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  assumption. intro T; inv T; contra. intro T; inv T; contra.
Qed.

Lemma set_vcpu_active_core_iso:
  forall vmid vcpuid s s' a
    (ex: local_set_vcpu_active vmid vcpuid s = (s', false, a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma register_vcpu_inv:
  forall vmid vcpuid s s' a
    (ex: local_register_vcpu vmid vcpuid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso0.
  intros until pte. destruct_zmap; simpl; apply smmu_iso0.
  intros. destruct_zmap; simpl.
  rewrite Heq in *. rewrite ZMap.gss in Hload_idx.
  eapply remap_addr0. assumption.
  rewrite (ZMap.gso _ _ Heq) in Hload_idx.
  eapply remap_addr0. assumption.
  intros. destruct (zeq vmid0 vmid). subst.
  rewrite ZMap.gss in *; simpl in *.
  eapply (core_remap0 vmid load_idx Hload_idx). assumption.
  rewrite (ZMap.gso _ _ n) in Hgfn, Hload_idx.
  eapply (core_remap0 vmid0 load_idx Hload_idx). assumption.
  intros. destruct_zmap; simpl; apply remap_range0.
  intros.
  destruct (zeq vmid vmid1), (zeq vmid vmid2);
    repeat subst; repeat rewrite ZMap.gss in *; simpl in *.
  eapply remap_no_overlap0; assumption.
  rewrite ZMap.gso. eapply remap_no_overlap0. assumption.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  left. assumption. intro T; inv T; contra.
  rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  assumption. left. intro T; inv T; contra. intro T; inv T; contra.
  rewrite ZMap.gso. rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  assumption. intro T; inv T; contra. intro T; inv T; contra.
Qed.

Lemma register_vcpu_core_iso:
  forall vmid vcpuid s s' a
    (ex: local_register_vcpu vmid vcpuid s = (s', false, a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma gen_vmid_inv:
  forall s s' a
    (ex: local_gen_vmid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
Qed.

Lemma gen_vmid_core_iso:
  forall s s' a
    (ex: local_gen_vmid s = (s', false, a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma register_kvm_inv:
  forall vmid s s' a
    (ex: local_register_kvm vmid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl.
  intros. eapply vm_iso0; try eassumption. rewrite C. omega.
  apply vm_iso0.
  intros until pte. destruct_zmap; simpl.
  intros. eapply smmu_iso0; try eassumption. rewrite C.
  autounfold in *; bool_rel; omega.
  apply smmu_iso0.
  intros. destruct_zmap; simpl.
  rewrite Heq in *. rewrite ZMap.gss in Hload_idx.
  eapply remap_addr0. assumption.
  rewrite (ZMap.gso _ _ Heq) in Hload_idx.
  eapply remap_addr0. assumption.
  intros. destruct (zeq vmid0 vmid). subst.
  rewrite ZMap.gss in *; simpl in *.
  eapply (core_remap0 vmid load_idx Hload_idx). assumption.
  rewrite (ZMap.gso _ _ n) in Hgfn, Hload_idx.
  eapply (core_remap0 vmid0 load_idx Hload_idx). assumption.
  intros. destruct_zmap; simpl; apply remap_range0.
  intros.
  destruct (zeq vmid vmid1), (zeq vmid vmid2);
    repeat subst; repeat rewrite ZMap.gss in *; simpl in *.
  eapply remap_no_overlap0; assumption.
  rewrite ZMap.gso. eapply remap_no_overlap0. assumption.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  left. assumption. intro T; inv T; contra.
  rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  assumption. left. intro T; inv T; contra. intro T; inv T; contra.
  rewrite ZMap.gso. rewrite ZMap.gso. eapply remap_no_overlap0.
  rewrite ZMap.gso in Hload_idx1. assumption. intro T; inv T; contra.
  rewrite ZMap.gso in Hload_idx2. assumption. intro T; inv T; contra.
  assumption. intro T; inv T; contra. intro T; inv T; contra.
Qed.

Lemma register_kvm_core_iso:
  forall vmid s s' a
    (ex: local_register_kvm vmid s = (s', false, a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma set_boot_info_inv:
  forall vmid load_addr size s s' a b
    (Hsize: size >= 0)
    (ex: local_set_boot_info vmid load_addr size s = (s', false, a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H.
  constructor; simpl; try assumption.
  intros until pte. destruct_zmap; simpl; apply vm_iso0.
  intros until pte. destruct_zmap; simpl; apply smmu_iso0.
  intros. bool_rel_all0. omega.
  intros. eapply core_map0. bool_rel_all0. autounfold in *.
  assert((next_remap_ptr (core_data s)  + (size + 4095) / 4096 * 4096) / 4096 >=
         next_remap_ptr (core_data s) / 4096).
  { apply Z_div_ge. omega. omega. }
  omega.

  intros. destruct (zeq vmid0 vmid). subst.
  subst. rewrite ZMap.gss in *; simpl in *. autounfold in *.
  destruct (zeq load_idx (vm_next_load_info (VB vmid @ (vminfos s)))).
  subst. repeat rewrite ZMap.gss in *; simpl in *.
  bool_rel_all0; split. omega.
  rewrite Z_div_plus_full. omega. intro T; inv T.
  repeat rewrite (ZMap.gso _ _ n).
  exploit (remap_addr0 vmid load_idx). omega.
  intros (a & b). split. assumption.
  rewrite Z_div_plus_full. bool_rel_all0; omega. intro T; inv T.
  rewrite (ZMap.gso _ _ n) in *. rewrite (ZMap.gso _ _ n) in Hload_idx.
  exploit (remap_addr0 vmid0 load_idx). omega.
  intros (a & b). split. assumption.
  rewrite Z_div_plus_full. bool_rel_all0; omega. intro T; inv T.

  intros. destruct (zeq vmid0 vmid). subst.
  subst. rewrite ZMap.gss in *; simpl in *. autounfold in *.
  destruct (zeq load_idx (vm_next_load_info (VB vmid @ (vminfos s)))).
  subst. repeat rewrite ZMap.gss in *; simpl in *.
  eapply core_map0. omega.
  repeat rewrite (ZMap.gso _ _ n) in Hgfn.
  eapply (core_remap0 vmid load_idx). omega. assumption.
  rewrite (ZMap.gso _ _ n) in Hgfn, Hload_idx.
  eapply (core_remap0 vmid0 load_idx Hload_idx). assumption.

  intros. destruct_zmap; simpl. destruct_zmap; simpl. omega.
  apply remap_range0. apply remap_range0.

  intros; autounfold in *.
  repeat
    (destruct_zmap; simpl; subst; try rewrite ZMap.gss in *; simpl in *);
     try omega; try eapply remap_no_overlap0; try rewrite ZMap.gso in Hload_idx2;
     try rewrite ZMap.gso in Hload_idx1; try omega; try assumption.
   destruct Hnot_same; contra.
   exploit (remap_addr0 vmid load_idx2). omega.
   intros (a & b). left. apply Z.ge_le_iff. assumption.
   exploit (remap_addr0 vmid2 load_idx2). omega.
   intros (a & b). left. apply Z.ge_le_iff. assumption.
   exploit (remap_addr0 vmid load_idx1). omega.
   intros (a & b). right. apply Z.ge_le_iff. assumption.
   exploit (remap_addr0 vmid1 load_idx1). omega.
   intros (a & b). right. apply Z.ge_le_iff. assumption.
   assumption.
Qed.

Lemma set_boot_info_core_iso:
  forall vmid load_addr size s s' a b
    (Hsize: size >= 0)
    (ex: local_set_boot_info vmid load_addr size s = (s', false, a, b))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma remap_vm_image_inv:
  forall vmid pfn load_idx s s' a b
    (Hload_idx: valid_load_idx load_idx)
    (ex: local_remap_vm_image vmid pfn load_idx s = (s', false, a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H; autounfold in *.
  assert(0 <> 16) by omega.
  constructor; autounfold; simpl; try rewrite (ZMap.gso _ _ H); try assumption.
  intros until pte. intros ? ?. assert_gsoH H0.
  red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
  destruct_zmap; simpl; eapply vm_iso0; try eassumption.
  rewrite Heq in H0; eassumption. omega.
  intros until pte. destruct_zmap; simpl; apply smmu_iso0.
  pose proof (local_mmap_level3 _ _ _ _ _ C2) as Hn.
  rewrite ZMap.gss. rewrite Hn.
  intros. destruct_zmap.
  exploit (remap_addr0 vmid load_idx). split; omega.
  intros (a & b). autounfold in *.
  rewrite Z_div_plus_full in Heq. omega. intro T; inv T.
  apply core_map0. assumption.

  intros. destruct (zeq vmid0 vmid). subst.
  subst. rewrite ZMap.gss in *; simpl in *. autounfold in *.
  destruct_zmap.
  bool_rel_all0; split. omega.
  exploit (remap_addr0 vmid load_idx). omega.
  intros (a & b). assumption.
  exploit (remap_addr0 vmid load_idx0). bool_rel_all0; split; omega.
  auto.
  rewrite (ZMap.gso _ _ n0) in *. rewrite (ZMap.gso _ _ n0) in Hload_idx0.
  apply remap_addr0. assumption.

  intros. pose proof (local_mmap_level3 _ _ _ _ _ C2) as Hn.
  rewrite ZMap.gss. rewrite Hn.
  pose proof (remap_range0 vmid0 load_idx0).
  {
    destruct (zeq vmid0 vmid).
    - subst. repeat rewrite ZMap.gss in *; simpl in *.
      destruct (zeq load_idx0 load_idx).
      + subst. repeat rewrite ZMap.gss in *; simpl in *.
        destruct_zmap. rewrite Heq in Hgfn; autounfold in *.
        rewrite Z_div_plus_full in Hgfn. omega. intro T; inv T.
        eapply (core_remap0 vmid load_idx). omega. omega.
      + rewrite (ZMap.gso _ _ n0) in Hgfn.
        destruct_zmap.
        * autounfold in *. rewrite Z_div_plus_full in Heq.
          exploit (remap_no_overlap0 vmid load_idx vmid load_idx0).
          omega. omega. right. intro T; inv T; contra.
          intros. rewrite Heq in Hgfn.
          exploit (remap_addr0 vmid load_idx). split; omega.
          pose proof (remap_range0 vmid load_idx). omega.
          intro T; inv T.
        * eapply (core_remap0 vmid load_idx0). assumption. assumption.
    - rewrite (ZMap.gso _ _ n0) in Hgfn, Hload_idx0.
      destruct_zmap.
      + autounfold in *. rewrite Z_div_plus_full in Heq.
        exploit (remap_no_overlap0 vmid load_idx vmid0 load_idx0).
        omega. omega. left. intro T; inv T; contra.
        intros. rewrite Heq in Hgfn.
        exploit (remap_addr0 vmid load_idx). split; omega.
        pose proof (remap_range0 vmid load_idx). omega.
        intro T; inv T.
      + eapply (core_remap0 vmid0 load_idx0). assumption. assumption.
  }

  intros. pose proof (remap_range0 vmid0 load_idx0).
  destruct_zmap; simpl. destruct_zmap; simpl. subst. omega.
  subst. omega. omega.

  intros.
  repeat (destruct_zmap; simpl; subst; try rewrite ZMap.gss in *; simpl in *);
          eapply remap_no_overlap0; try rewrite ZMap.gso in Hload_idx2;
          try rewrite ZMap.gso in Hload_idx1; try omega; try assumption.

  assumption. assumption.
Qed.

Lemma remap_vm_image_core_iso:
  forall vmid pfn load_idx s s' a b
    (Hload_idx: valid_load_idx load_idx)
    (ex: local_remap_vm_image vmid pfn load_idx s = (s', false, a, b))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma smmu_assign_page_inv:
  forall vmid cbndx index pfn gfn s s' a b c d
    (ex: local_smmu_assign_page cbndx index pfn gfn s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; try assumption; bool_rel_all.
  pose proof (smmu_count_0_no_map _ H _ C2 C3) as Hcount0.
  destruct H; autounfold in *.
  destruct (z =? 0) eqn:Hz; bool_rel_all.
  - inv C6. rewrite zmap_set_id.
    constructor; autounfold; simpl; try assumption.
    + intro pfn0. destruct_zmap. inv Heq. simpl. intros. omega.
      eapply host_s2_map0; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + intros until pte. destruct_zmap. intros.
      simpl. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists).
      inv H. pose proof (host_npt_cons0 _ _ _ _ C4).
      rewrite C4 in Hpfn. inv Hpfn.
      replace (phys_page 0 / 4096) with 0 in H1 by reflexivity. omega.
      apply host_iso0.
    + intros until pte. destruct_zmap. simpl.
      intros. exploit vm_iso0; try eassumption. omega.
      intros. omega. apply vm_iso0.
    + intros until pte. destruct_zmap. simpl.
      intros. exploit smmu_iso0; try eassumption.
      intros (? & ?). srewrite.
      exploit Hcount0; try eassumption. reflexivity. intros. inv H2.
      apply smmu_iso0.
    + intro. destruct_zmap. simpl. intros.
      pose proof (smmu_count0 _ C2). rewrite C3 in H0. omega.
      apply smmu_count0.
  - pose proof (local_mmap_level3 _ _ _ _ _ C6) as Hn.
    constructor; autounfold; simpl; try assumption.
    + rewrite ZMap.gss. intros until pte. rewrite Hn.
      destruct_zmap. intros. inv H. reflexivity.
      apply host_npt_cons0.
    + rewrite ZMap.gss. intros until pte. rewrite Hn.
      destruct_zmap. intros. inv H.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in H0 by reflexivity.
      contra. apply host_flatmap0.
    + intro pfn0. destruct_zmap. simpl. intros; omega.
      eapply host_s2_map0; eassumption.
    + destruct_zmap. inv Heq. omega. assumption.
    + rewrite ZMap.gss. rewrite Hn. intros until pte.
      destruct_zmap. intros. inv Hpfn.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 in Hexists by reflexivity.
      contra. intros. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists).
      rewrite Z_div_mult_full in Heq. rewrite H in Heq. rewrite (ZMap.gso _ _ Heq).
      eapply host_iso0; eassumption. autounfold; omega.
    + intros until pte. intros ? ?.  assert_gsoH H. red; intro; srewrite; omega.
      rewrite (ZMap.gso _ _ Hneq) in H.
      destruct_zmap. simpl.
      intros. exploit vm_iso0; try eassumption. omega. rewrite Heq. omega.
      intros. rewrite Heq in H4. omega. eapply vm_iso0; try eassumption.
    + intros until pte. destruct_zmap. simpl. intros.
      exploit smmu_iso0; try eassumption. intros (? & ?).
      srewrite. pose proof (Hcount0 _ _ Hvalid_smmu Hvalid_cfg Hsmmu _ _ _ Hspt).
      contra. apply smmu_iso0.
    + intro. destruct_zmap. inv Heq. simpl. intros. omega.
      apply smmu_count0.
    + rewrite ZMap.gso. eapply core_map0. intro T; inv T.
    + rewrite ZMap.gso. eapply core_remap0. intro T; inv T.
Qed.

Lemma smmu_assign_page_core_iso:
  forall vmid cbndx index pfn gfn s s' a b c d
    (ex: local_smmu_assign_page cbndx index pfn gfn s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_zmap; simpl; bool_rel_all0; omega.
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
      rewrite <- Heq. eapply spt_cons0; eassumption.
      apply spt_cons0.
    + intro. destruct_zmap. simpl.
      intros. eapply host_s2_map0; try eassumption. apply host_s2_map0.
    + destruct_zmap. simpl. rewrite <- Heq. assumption. assumption.
    + intros until pte0. destruct_zmap. simpl. intros. auto.
      apply host_iso0.
    + intros until pte0. destruct_zmap. simpl. intros.
      exploit vm_iso0; try eassumption. intros. omega.
      apply vm_iso0.
    + intros until pte0. rewrite Hn. destruct_zmap.
      destruct_zmap. intros. inv Hspt. rewrite ZMap.gss.
      simpl. rewrite H0 in *.
      split. assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite H2. rewrite C10. reflexivity. rewrite C11. reflexivity.
      intros. assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt.
      exploit smmu_iso0; try eassumption. intros (? & ?).
      destruct_zmap. simpl. srewrite. auto. auto.
      intros. exploit smmu_iso0; try eassumption. intros (? & ?).
      destruct_zmap. simpl. srewrite. auto. auto.
    + intro. destruct_zmap. simpl. intros. pose proof (smmu_count0 _ H).
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
      pose proof (host_s2_map0 _ H0).
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
      pose proof (host_s2_map0 _ H0). srewrite.
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
      rewrite H2. apply smmu_count0. autounfold; simpl. omega.
      Local Opaque count_smmu_map.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl.
    + rewrite Hn. intros until pte0. destruct_zmap.
      destruct_zmap. intros. inv H1. reflexivity.
      rewrite <- Heq. eapply spt_cons0; eassumption.
      apply spt_cons0.
    + assumption. + assumption. + assumption. + assumption.
    + assumption. + assumption. + assumption.
    + rewrite Hn. intros until pte0. destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      assert(index0 * 8 + cbndx0 = index * 8 + cbndx) by omega.
      srewrite. auto.
      assert(index0 * 8 + cbndx0 = index * 8 + cbndx) by omega.
      rewrite <- H. apply smmu_iso0. apply smmu_iso0.
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
      intros. pose proof (host_s2_map0 _ H).
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
        pose proof (host_s2_map0 _ C10). srewrite. omega. rewrite H3.
        match goal with |- context[?a @ (?b @ ?c)] => destruct (a @ (b @ c)) end.
        repeat destruct_if; apply IHn0; omega. rewrite IHn0. reflexivity. omega.
        rewrite IHn0. reflexivity. omega. omega. }
      rewrite H1. apply smmu_count0. assumption. autounfold; simpl. omega.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
      Local Opaque count_smmu_map.
Qed.

Lemma smmu_map_page_core_iso:
  forall cbndx index iova pte s s' a b c d
    (ex: local_smmu_map_page cbndx index iova pte s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_if. destruct_zmap; simpl; omega. omega.
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
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply spt_cons0.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). intros until pte.
      destruct_zmap. destruct_zmap. intros. inv H3. reflexivity.
      rewrite <- Heq. eapply spt_cons0; eassumption. apply spt_cons0.
    + intro. destruct_zmap. simpl.
      intros. eapply host_s2_map0; try eassumption. apply host_s2_map0.
    + destruct_zmap. simpl. rewrite <- Heq. assumption. assumption.
    + intros until pte. destruct_zmap. simpl. intros. auto.
      apply host_iso0.
    + intros until pte. destruct_zmap. simpl. intros.
      exploit vm_iso0; try eassumption. intros. omega.
      apply vm_iso0.
    + intros until pte.
      destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2.
      intros. destruct_zmap. simpl. replace (phys_page 0 / 4096) with 0 in Heq by reflexivity.
      contra. eapply smmu_iso0; try eassumption.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      replace (phys_page 0 / PAGE_SIZE) with 0 in H by reflexivity. contra.
      intros. destruct_zmap. simpl.
      autounfold in *.
      assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt. rewrite Heq1 in Hspt.
      eapply smmu_iso0; try eassumption. omega.
      autounfold in *.
      assert((index0 * 8 + cbndx0) = (index * 8 + cbndx)) by omega.
      rewrite <- H2 in Hspt.
      eapply smmu_iso0; try eassumption.
      destruct_zmap. simpl. intros.
      eapply smmu_iso0; try eassumption.
      eapply smmu_iso0; try eassumption.
    + intro. destruct_zmap. simpl. intros. pose proof (smmu_count0 _ H).
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
      pose proof (host_s2_map0 _ H0).
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
        symmetry in Heqvmid0. exploit (smmu_vm0 cbndx index); try eassumption.
        srewrite. assumption. intros.
        exploit spt_cons0; try eapply C1; try eassumption. intros.
        exploit smmu_iso0; try eapply C1; try eassumption.
        destruct (zeq vmid0 0). auto. right. split. omega.
        replace (0 <? vmid0) with true in C0 by (symmetry; bool_rel; omega).
        replace (vmid0 <? 16) with true in C0 by (symmetry; bool_rel; omega).
        simpl in C0. bool_rel. omega. intro. srewrite. inversion H7.
        intros (? & ?). srewrite. rewrite <- H9. rewrite ZMap.gss. rewrite <- Heq.
        replace (phys_page 0 / 4096 =? 0) with true by reflexivity.
        rewrite Heq. rewrite H9. rewrite C1.
        destruct_if. bool_rel. srewrite. inversion page_0_invalid0.
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
      inv C2. apply smmu_count0.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      pose proof (host_s2_map0 _ H0). srewrite.
      assert(forall n, (Z.of_nat n <= EL2_SMMU_CFG_SIZE) ->
                  count_smmu_map n pfn (smmu_vmid s) s0 =
                  count_smmu_map n pfn (smmu_vmid s) (spts s)).
      { induction n. reflexivity.
        rewrite Nat2Z.inj_succ, succ_plus_1. intros.
        simpl. autounfold in *. rewrite Hn.
        replace (Z.of_nat n / 8 * 8) with (8 * (Z.of_nat n / 8)) by apply Z.mul_comm.
        rewrite <- Z_div_mod_eq. destruct_zmap.
        remember ((index * 8 + cbndx) @ (smmu_vmid s)) as vmid0.
        symmetry in Heqvmid0. exploit (smmu_vm0 cbndx index); try eassumption.
        srewrite. assumption. intros.
        exploit spt_cons0; try eapply C1; try eassumption. intros.
        exploit smmu_iso0; try eapply C1; try eassumption.
        destruct (zeq vmid0 0). auto. right. split. omega.
        replace (0 <? vmid0) with true in C0 by (symmetry; bool_rel; omega).
        replace (vmid0 <? 16) with true in C0 by (symmetry; bool_rel; omega).
        simpl in C0. bool_rel. omega. intro. srewrite. inversion H4.
        intros (? & ?). srewrite. assert_gso. omega.
        rewrite (ZMap.gso _ _ Hneq). rewrite IHn. reflexivity.
        omega. rewrite IHn. reflexivity. omega. omega. }
      rewrite H2. apply smmu_count0. autounfold; simpl. omega.
      Local Opaque count_smmu_map.
  - destruct H; autounfold in *.
    constructor; autounfold; simpl.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply spt_cons0.
      rewrite (local_spt_map_pt _ _ _ _ _ _ C2). intros until pte.
      destruct_zmap. destruct_zmap. intros. inv H1. reflexivity.
      rewrite <- Heq. eapply spt_cons0; eassumption. apply spt_cons0.
    + assumption. + assumption. + assumption. + assumption.
    + assumption. + assumption. + assumption.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. apply smmu_iso0.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      rewrite Hn. intros until pte. destruct_zmap.
      destruct_zmap. intros. inv Hspt.
      replace (phys_page 0 / PAGE_SIZE) with 0 in H by reflexivity.
      contra. rewrite <- Heq. eapply smmu_iso0; eassumption. apply smmu_iso0.
    + destruct (z0 =? 0) eqn:Hz; bool_rel. inv C2. assumption.
      pose proof (local_spt_map_pt _ _ _ _ _ _ C2) as Hn.
      intros. destruct (zeq pfn (phys_page z0 / 4096)).
      srewrite. intros. assert(s2_count (phys_page z0 / 4096) @ (s2page s) <= 0).
      bool_rel_all; omega.
      pose proof (smmu_count0 _ H).
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
      pose proof (host_s2_map0 _ H).
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
      pose proof (smmu_count0 _ H).
      replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
      omega.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
      Local Opaque count_smmu_map.
Qed.

Lemma smmu_clear_core_iso:
  forall iova cbndx index s s' a b c d
    (ex: local_smmu_clear iova cbndx index s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_if. destruct_zmap; simpl; omega. omega.
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
    eapply smmu_vm0; try eassumption. rewrite (ZMap.gso _ _ Heq) in H.
    assumption.
  - intros until pte. destruct_zmap. intros. omega.
    apply smmu_iso0.
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
      pose proof (smmu_count0 _ H).
      replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
      omega.
Qed.

Lemma free_smmu_pgd_core_iso:
  forall cbndx index s s' a b
    (ex: local_free_smmu_pgd cbndx index s = (s', false, a, b))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
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
    apply spt_cons0.
  - intros. destruct_zmap. omega. apply smmu_vm0; try assumption.
    rewrite (ZMap.gso _ _ Heq) in H. assumption.
  - intros until pte. destruct_zmap. rewrite ZMap.gi. intros.
    inv Hspt. contra. intros. assert_gsoH Hspt. omega.
    rewrite (ZMap.gso _ _ Hneq) in Hspt. eapply smmu_iso0; eassumption.
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
    pose proof (smmu_count0 _ H).
    replace (Pos.to_nat 16) with (Z.to_nat 16) in * by reflexivity.
    omega.
Qed.

Lemma alloc_smmu_pgd_core_iso:
  forall cbndx vmid index num s s' a b c
    (ex: local_alloc_smmu_pgd cbndx vmid index num s = (s', false, a, b, c))
    (Hvmid: HOSTVISOR <= vmid < COREVISOR)
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma set_vm_poweroff_inv:
  forall vmid s s' a
    (ex: local_set_vm_poweroff vmid s = (s', a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  - intros until pte. destruct_zmap. simpl. intros. omega.
    apply vm_iso0.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply smmu_iso0; try eassumption. destruct Hvalid_vmid; omega.
    apply smmu_iso0.
  - intros. destruct_zmap; subst; try rewrite ZMap.gss in *; simpl in *. apply remap_addr0; assumption.
    rewrite (ZMap.gso _ _ Heq) in Hload_idx. apply remap_addr0; assumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply core_remap0; eassumption.
    rewrite (ZMap.gso _ _ n) in Hload_idx, Hgfn; simpl in *. eapply core_remap0; eassumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply remap_range0; eassumption.
    rewrite (ZMap.gso _ _ n). eapply remap_range0.
  - intros.
    repeat (destruct_zmap; simpl; subst; try rewrite ZMap.gss in *; simpl in *);
            eapply remap_no_overlap0; try rewrite ZMap.gso in Hload_idx2;
            try rewrite ZMap.gso in Hload_idx1; try omega; try assumption.
Qed.

Lemma set_vm_poweroff_core_iso:
  forall vmid s s' a
    (ex: local_set_vm_poweroff vmid s = (s', a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma verify_vm_inv:
  forall vmid s s' a
    (ex: local_verify_vm vmid s = (s', false, a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex. destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply vm_iso0; try eassumption. omega.
    apply vm_iso0.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply smmu_iso0; try eassumption. omega.
    apply smmu_iso0.
  - intros. destruct_zmap; subst; try rewrite ZMap.gss in *; simpl in *. apply remap_addr0; assumption.
    rewrite (ZMap.gso _ _ Heq) in Hload_idx. apply remap_addr0; assumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply core_remap0; eassumption.
    rewrite (ZMap.gso _ _ n) in Hload_idx, Hgfn; simpl in *. eapply core_remap0; eassumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply remap_range0; eassumption.
    rewrite (ZMap.gso _ _ n). eapply remap_range0.
  - intros.
    repeat (destruct_zmap; simpl; subst; try rewrite ZMap.gss in *; simpl in *);
            eapply remap_no_overlap0; try rewrite ZMap.gso in Hload_idx2;
            try rewrite ZMap.gso in Hload_idx1; try omega; try assumption.
Qed.

Lemma verify_vm_core_iso:
  forall vmid s s' a
    (ex: local_verify_vm vmid s = (s', false, a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma load_encrypted_vcpu_inv:
  forall vmid vcpuid cregs cstates dorc logn s s' cr cs n' a
    (ex: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s = (s', false, cr, cs, n', a)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply vm_iso0; try eassumption.
    apply vm_iso0.
  - intros until pte. destruct_zmap. simpl. intros.
    eapply smmu_iso0; try eassumption.
    apply smmu_iso0.
  - intros. destruct_zmap; subst; try rewrite ZMap.gss in *; simpl in *. apply remap_addr0; assumption.
    rewrite (ZMap.gso _ _ Heq) in Hload_idx. apply remap_addr0; assumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply core_remap0; eassumption.
    rewrite (ZMap.gso _ _ n) in Hload_idx, Hgfn; simpl in *. eapply core_remap0; eassumption.
  - intros. destruct (zeq vmid0 vmid); subst; try rewrite ZMap.gss in *; simpl in *. eapply remap_range0; eassumption.
    rewrite (ZMap.gso _ _ n). eapply remap_range0.
  - intros.
    repeat (destruct_zmap; simpl; subst; try rewrite ZMap.gss in *; simpl in *);
            eapply remap_no_overlap0; try rewrite ZMap.gso in Hload_idx2;
            try rewrite ZMap.gso in Hload_idx1; try omega; try assumption.
Qed.

Lemma load_encrypted_vcpu_core_iso:
  forall vmid vcpuid cregs cstates dorc logn s s' cr cs n' a
    (ex: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s = (s', false, cr, cs, n', a))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
Qed.

Lemma load_save_encrypt_buf_inv:
  forall vmid inbuf outbuf dorc logn s s' n' a b
    (ex: local_save_encrypt_buf vmid inbuf outbuf dorc logn s = (s', false, n', a, b)),
    shared_inv s -> shared_inv s'.
Proof.
  intros. hsimpl_func ex; destruct H; autounfold in *.
  constructor; autounfold; simpl; try assumption.
Qed.

Lemma load_save_encrypt_buf_core_iso:
  forall vmid inbuf outbuf dorc logn s s' n' a b
    (ex: local_save_encrypt_buf vmid inbuf outbuf dorc logn s = (s', false, n', a, b))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
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
    + intro. destruct_zmap. simpl. intros; omega. apply host_s2_map0.
    + assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
      rewrite (ZMap.gso _ _ Hneq). assumption.
    + intros. destruct_zmap. rewrite Heq in *.
      rewrite (host_flatmap0 _ _ _ _ Hpfn) in Hpfn. rewrite C1 in Hpfn. inv Hpfn.
      rewrite H0 in Hexists. contra. assumption. eapply host_iso0; try eassumption.
    + intros. destruct_zmap. rewrite Heq in *.
      exploit (vm_iso0 _ _ _ _ _ H); try eassumption. omega.
      intros. rewrite Hcond in H4. omega. rewrite (ZMap.gso _ _ Heq) in H3.
      eapply vm_iso0; eassumption.
    + intros. destruct_zmap. simpl. rewrite Heq in *.
      exploit (smmu_iso0 vmid0 cbndx index gfn pfn pte); try eassumption.
      rewrite Heq. assumption. omega.
      intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
      rewrite H0. assumption. rewrite Heq. apply Hspt. eapply smmu_iso0; eassumption.
    + intro. destruct_zmap. simpl; intros.
      rewrite <- Hcond0. eapply smmu_count0; eassumption. eapply smmu_count0.
    + pose proof (host_npt_cons0 _ _ _ _ C1). rewrite H. reflexivity.
  - pose proof (local_mmap_level3 _ _ _ _ _ C3).
    constructor; autounfold; simpl; try assumption.
    + intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
      intro T. inv T. reflexivity. apply host_npt_cons0.
    + intros until pte. rewrite ZMap.gss. rewrite H. destruct_zmap.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
      intros. inv H0. contra. apply host_flatmap0.
    + intro. destruct_zmap. simpl. intros; omega. apply host_s2_map0.
    + assert_gso. red; intro T. rewrite T in page_0_invalid0. omega.
      rewrite (ZMap.gso _ _ Hneq). assumption.
    + rewrite ZMap.gss. rewrite H. intros until pte.
      replace (phys_page 144115188075855872 / PAGE_SIZE) with 0 by reflexivity.
      destruct_zmap. intros. inv Hpfn. contra.
      intros. autounfold in *. assert_gso. red; intro.
      inv H0. pose proof (host_flatmap0 _ _ _ _ Hpfn Hexists). inv H0.
      apply Heq. rewrite Z_div_mult_full. reflexivity. omega.
      rewrite (ZMap.gso _ _ Hneq). eapply host_iso0; eassumption.
    + intros. destruct_zmap. rewrite Heq in *.
      assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
      exploit (vm_iso0 _ _ _ _ _ H0); try eassumption. omega. intros.
      rewrite Hcond in H5. omega.
      assert_gsoH H0. red; intro; srewrite; omega. rewrite (ZMap.gso _ _ Hneq) in H0.
      rewrite (ZMap.gso _ _ Heq) in H4. eapply vm_iso0; eassumption.
    + intros. destruct_zmap. simpl. rewrite Heq in *.
      exploit (smmu_iso0 vmid0 cbndx index gfn pfn pte); try eassumption.
      rewrite Heq. assumption. omega.
      intros (? & ?). srewrite. eapply Hcount0 in Heq; try eassumption. inv Heq.
      rewrite H1. assumption.
      rewrite Heq. apply Hspt. eapply smmu_iso0; eassumption.
    + intro. destruct_zmap. simpl; intros.
      rewrite <- Hcond0. eapply smmu_count0; eassumption. eapply smmu_count0.
    + rewrite ZMap.gso. assumption. intro T; inv T.
    + rewrite ZMap.gso. assumption. intro T; inv T.
Qed.

Lemma load_load_decrypt_buf_core_iso:
  forall vmid inbuf dorc logn s s' n' a b c d
    (Hvalid_vm: valid_vm vmid)
    (ex: local_load_decrypt_buf vmid inbuf dorc logn s = (s', false, n', a, b, c, d))
    (Hinv: shared_inv s),
    forall pfn, (s2_owner pfn @ (s2page s) = COREVISOR) <-> (s2_owner pfn @ (s2page s') = COREVISOR).
Proof.
  intros; autounfold in *. hsimpl_func ex; simpl; try omega.
  destruct_zmap; simpl; bool_rel_all0; omega.
Qed.
```
