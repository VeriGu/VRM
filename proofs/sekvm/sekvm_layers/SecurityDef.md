# SecurityDef

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

Definition valid_role (vmid: Z) (adt: RData) :=
  vmid = HOSTVISOR \/ (HOSTVISOR < vmid < COREVISOR /\ vm_state (VS (vmid @ (vminfos (shared adt)))) = VERIFIED).

Definition active (vmid: Z) (adt: RData) :=
  ((vmid =? HOSTVISOR) && ihost adt) || (cur_vmid adt =? vmid).

Definition observe_reg (vmid: Z) (adt: RData) :=
  if (cur_vmid adt =? vmid) && (negb (icore adt)) then
    Some (ctxt_regs (regs adt))
  else None.

Definition observe_npt (vmid: Z) (gfn: Z) (sdt: Shared) :=
  if vmid =? HOSTVISOR then
    match gfn @ (pt (vmid @ (npts sdt))) with
    | (pfn, level, pte) =>
      if s2_owner (pfn @ (s2page sdt)) =? HOSTVISOR
      then pfn
      else 0
    end
  else
    match gfn @ (pt (vmid @ (npts sdt))) with
    | (pfn, level, pte) => pfn
    end.

Definition observe_owner (vmid: Z) (pfn: Z) (sdt: Shared) :=
  let page := pfn @ (s2page sdt) in
  if vmid =? HOSTVISOR then s2_owner page
  else if s2_owner page =? vmid then 1 else 0.

Definition observe_count (vmid: Z) (pfn: Z) (sdt: Shared) :=
  let page := pfn @ (s2page sdt) in
  if s2_owner page =? INVALID then -1
  else if s2_owner page =? vmid then s2_count page
       else 0.

Definition observe_gfn (vmid: Z) (pfn: Z) (sdt: Shared) :=
  let page := pfn @ (s2page sdt) in
  if vmid =? HOSTVISOR then s2_gfn page
  else if s2_owner page =? vmid then s2_gfn page
       else 0.

Definition observe_flatmem (vmid: Z) (pfn: Z) (sdt: Shared) :=
  let page := pfn @ (s2page sdt) in
  if s2_owner page =? vmid then pfn @ (flatmem sdt)
  else 0.

Definition observe_smmu (vmid: Z) (cbndx: Z) (index: Z) (sdt: Shared) :=
  let vmid0 := (smmu_id index cbndx) @ (smmu_vmid sdt) in
  if vmid =? HOSTVISOR then vmid0 else
    if vmid =? vmid0 then 1 else 0.

Definition observe_spt (vmid: Z) (cbndx: Z) (index: Z) (gfn: Z) (sdt: Shared) :=
  let vmid0 := (smmu_id index cbndx) @ (smmu_vmid sdt) in
  let spt := (SMMU_TTBR index cbndx) @ (spt_pt (spts sdt)) in
  if vmid =? HOSTVISOR then gfn @ spt
  else if vmid =? vmid0 then gfn @ spt else (0, 0).

Definition observe_shadow_ctxt (vmid: Z) (vcpuid: Z) (adt: RData) :=
  (ctxt_id vmid vcpuid) @ (shadow_ctxts adt).

Definition observe_boot_info (vmid: Z) (vmid0: Z) (sdt: Shared) :=
  if (vmid =? HOSTVISOR) then Some (VB (vmid0 @ (vminfos sdt)))
  else if vmid =? vmid0 then Some (VB (vmid0 @ (vminfos sdt)))
       else None.

Definition observe_state_info (vmid: Z) (vmid0: Z) (sdt: Shared) :=
  if (vmid =? HOSTVISOR) then None
  else if vmid =? vmid0 then Some (VS (vmid0 @ (vminfos sdt)))
       else None.

Definition observe_core_data (vmid: Z) (sdt: Shared) :=
  if (vmid =? HOSTVISOR) then Some (core_data sdt)
  else None.

Definition observe_dirty (vmid: Z) (vmid0: Z) (vcpuid0: Z) (adt: RData) :=
  if vmid =? HOSTVISOR then
    dirty (ctxt_states ((ctxt_id vmid0 vcpuid0) @ (shadow_ctxts adt))) =? INVALID64
  else true.

Definition observe_cur_vcpuid (vmid: Z) (adt: RData) :=
  if vmid =? (cur_vmid adt) then
    (cur_vcpuid adt)
  else -1.

Definition observe_data_log (vmid: Z) (adt: RData) :=
  ZMap.get vmid (data_log adt).

Definition observe_core_data_log (vmid: Z) (vmid0: Z) (adt: RData) :=
  if vmid =? HOSTVISOR then
    Some (vmid0 @ (core_data_log adt))
  else if (vmid =? vmid0) then
         Some (vmid0 @ (core_data_log adt))
       else None.

Definition observe_smmu_cfg (adt: RData) :=
  smmu_conf adt.

Record shared_eq (vmid: Z) (s1 s2: Shared) :=
  {
    npt_eq:
      forall gfn, observe_npt vmid gfn s1 = observe_npt vmid gfn s2;
    owner_eq:
      forall pfn, observe_owner vmid pfn s1 = observe_owner vmid pfn s2;
    count_eq:
      forall pfn, observe_count vmid pfn s1 = observe_count vmid pfn s2;
    gfn_eq:
      forall pfn, observe_gfn vmid pfn s1 = observe_gfn vmid pfn s2;
    mem_eq:
      forall pfn, observe_flatmem vmid pfn s1 = observe_flatmem vmid pfn s2;
    smmu_eq:
      forall cbndx index (Hcb: valid_smmu_cfg cbndx) (Hsmmu: valid_smmu index),
        observe_smmu vmid cbndx index s1 = observe_smmu vmid cbndx index s2;
    spt_eq:
      forall gfn cbndx index (Hcb: valid_smmu_cfg cbndx) (Hsmmu: valid_smmu index),
        observe_spt vmid cbndx index gfn s1 = observe_spt vmid cbndx index gfn s2;
    boot_eq:
      forall vmid0, observe_boot_info vmid vmid0 s1 = observe_boot_info vmid vmid0 s2;
    state_eq:
      forall vmid0, observe_state_info vmid vmid0 s1 = observe_state_info vmid vmid0 s2;
    core_data_eq:
      observe_core_data vmid s1 = observe_core_data vmid s2
  }.

Record obs_eq (vmid: Z) (d1 d2: RData) :=
  {
    sh_eq: shared_eq vmid (shared d1) (shared d2);

    regs_eq :
        observe_reg vmid d1 = observe_reg vmid d2;
    shadow_ctxt_eq:
      forall vcpuid (Hvcpu: valid_vcpu vcpuid),
        observe_shadow_ctxt vmid vcpuid d1 = observe_shadow_ctxt vmid vcpuid d2;
    dirty_eq:
      forall vmid0 vcpuid0 (Hvm: valid_vm vmid0) (Hvcpu: valid_vcpu vcpuid0),
        observe_dirty vmid vmid0 vcpuid0 d1 = observe_dirty vmid vmid0 vcpuid0 d2;
    curid_eq:
      curid d1 = curid d2;
    cur_vcpu_eq:
      observe_cur_vcpuid vmid d1 = observe_cur_vcpuid vmid d2;
    data_log_eq:
      observe_data_log vmid d1 = observe_data_log vmid d2;
    core_data_log_eq:
        forall vmid0, observe_core_data_log vmid vmid0 d1 = observe_core_data_log vmid vmid0 d2;
    data_oracle_eq:
      doracle d1 = doracle d2;
    core_data_oracle_eq:
      core_doracle d1 = core_doracle d2;
    smmu_cfg_eq:
      observe_smmu_cfg d1 = observe_smmu_cfg d2
  }.

Inductive local_unchanged vmid d1 d2 : Prop :=
| SAME_OB:
    forall (same_ob: obs_eq vmid d1 d2),
      local_unchanged vmid d1 d2
| ORACLE:
    forall (oracle: d2 = query_oracle d1),
      local_unchanged vmid d1 d2
| TRANS:
    forall d3 (unc1: local_unchanged vmid d1 d3)
           (unc2: local_unchanged vmid d3 d2),
      local_unchanged vmid d1 d2.

Inductive indisting vmid d d' : Prop :=
| OBS_EQ: forall (Hoeq: obs_eq vmid d d'),
    indisting vmid d d'
| LOCAL_UNC: forall d0 d0'
               (Hind: indisting vmid d0 d0')
               (Hunc1: local_unchanged vmid d0 d)
               (Hunc2: local_unchanged vmid d0' d'),
    indisting vmid d d'.

Hypothesis indisting_obs_eq:
  forall vmid d d' (Hactive: active vmid d = true) (Hcur': active vmid d' = true),
    indisting vmid d d' -> obs_eq vmid d d'.

Hint Unfold
valid_role
active
observe_reg
observe_npt
observe_owner
observe_count
observe_gfn
observe_flatmem
observe_smmu
observe_spt
observe_shadow_ctxt
observe_boot_info
observe_state_info
observe_dirty
observe_cur_vcpuid
observe_data_log
observe_core_data_log
observe_core_data
observe_smmu_cfg.
```
