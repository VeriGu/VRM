# Spec

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import GenSem.
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

Require Import NPTOps.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import RData.

Local Open Scope Z_scope.

Section MmioPTAllocSpec.

  Definition alloc_smmu_pgd_page_spec (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let spt := (spts (shared adt)) in
      let next := spt_pgd_next spt in
      rely ((SMMU_POOL_START <=? next) && (next <=? SMMU_PMD_START));
      if next + PAGE_SIZE <=? SMMU_PMD_START then
        let spt' := spt {spt_pgd_next: next + PAGE_SIZE} in
        let adt' := adt {shared: (shared adt) {spts: spt'}} in
        Some (adt', VZ64 next)
      else
        Some (adt {halt: true}, VZ64 0)
    | _ => None
    end.

  Definition alloc_smmu_pmd_page_spec  (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let spt := (spts (shared adt)) in
      let next := spt_pmd_next spt in
      rely ((SMMU_PMD_START <=? next) && (next <=? SMMU_POOL_END));
      if next + PAGE_SIZE <=? SMMU_POOL_END then
        let spt' := spt {spt_pmd_next: next + PAGE_SIZE} in
        let adt' := adt {shared: (shared adt) {spts: spt'}} in
        Some (adt', VZ64 next)
      else
        Some (adt {halt: true}, VZ64 0)
    | _ => None
    end.

End MmioPTAllocSpec.

Section MmioPTAllocSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := NPTOps_ops) LDATA).

  Definition alloc_smmu_pgd_page_spec0 (adt: RData) : option (RData * Z64) :=
    when' next == get_smmu_pgd_next_spec adt;
    rely is_addr next;
    if next + PAGE_SIZE <=? SMMU_PMD_START then
      when adt' == set_smmu_pgd_next_spec (VZ64 (next + PAGE_SIZE)) adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next'))
    else
      when adt' == panic_spec adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next')).

  Definition alloc_smmu_pmd_page_spec0 (adt: RData) : option (RData * Z64) :=
    when' next == get_smmu_pmd_next_spec adt;
    rely is_addr next;
    if next + PAGE_SIZE <=? SMMU_POOL_END then
      when adt' == set_smmu_pmd_next_spec (VZ64 (next + PAGE_SIZE)) adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next'))
    else
      when adt' == panic_spec adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next')).

  Inductive alloc_smmu_pgd_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_smmu_pgd_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'  res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_smmu_pgd_page_spec0  labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_smmu_pgd_page_spec_low_step s WB nil (m'0, labd) (Vlong res) (m'0, labd').

  Inductive alloc_smmu_pmd_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_smmu_pmd_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'  res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_smmu_pmd_page_spec0  labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_smmu_pmd_page_spec_low_step s WB nil (m'0, labd) (Vlong res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition alloc_smmu_pgd_page_spec_low: compatsem LDATAOps :=
      csem alloc_smmu_pgd_page_spec_low_step (type_of_list_type nil) Tint64.

    Definition alloc_smmu_pmd_page_spec_low: compatsem LDATAOps :=
      csem alloc_smmu_pmd_page_spec_low_step (type_of_list_type nil) Tint64.

  End WITHMEM.

End MmioPTAllocSpecLow.

```
