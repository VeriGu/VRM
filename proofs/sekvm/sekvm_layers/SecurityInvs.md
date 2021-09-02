# Invs

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

Local Open Scope Z_scope.

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
             s2_count (pfn @ (s2page sdt)) >= count_smmu_map (Z.to_nat EL2_SMMU_CFG_SIZE) pfn (smmu_vmid sdt) (spts sdt)
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

Opaque count_smmu_map.

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

Ltac extract_adt H name :=
  match type of H with
  | context[query_oracle ?a] => remember (query_oracle a) as name
  end.
```
