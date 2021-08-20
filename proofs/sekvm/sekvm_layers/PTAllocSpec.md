# PTAllocSpec

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

Require Import AbstractMachine.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import RData.

Local Open Scope Z_scope.

Section PTAllocSpec.

  Definition alloc_pgd_page_spec (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    if halt adt then Some (adt, VZ64 0) else
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      let next := pt_pgd_next npt in
      rely ((pgd_start vmid <=? next) && (next <=? pud_start vmid));
      if next + PAGE_SIZE <=? pud_start vmid then
        let npt' := npt {pt_pgd_next: next + PAGE_SIZE} in
        let adt' := adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}} in
        Some (adt', VZ64 next)
      else
        Some (adt {halt: true}, VZ64 0)
    | _ => None
    end.

  Definition alloc_pud_page_spec (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    if halt adt then Some (adt, VZ64 0) else
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      let next := pt_pud_next npt in
      rely ((pud_start vmid <=? next) && (next <=? pmd_start vmid));
      if next + PAGE_SIZE <=? pmd_start vmid then
        let npt' := npt {pt_pud_next: next + PAGE_SIZE} in
        let adt' := adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}} in
        Some (adt', VZ64 next)
      else
        Some (adt {halt: true}, VZ64 0)
    | _ => None
    end.

  Definition alloc_pmd_page_spec (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    if halt adt then Some (adt, VZ64 0) else
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      let next := pt_pmd_next npt in
      rely ((pmd_start vmid <=? next) && (next <=? pool_end vmid));
      if next + PAGE_SIZE <=? pool_end vmid then
        let npt' := npt {pt_pmd_next: next + PAGE_SIZE} in
        let adt' := adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}} in
        Some (adt', VZ64 next)
      else
        Some (adt {halt: true}, VZ64 0)
    | _ => None
    end.

End PTAllocSpec.

Section PTAllocSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := AbstractMachine_ops) LDATA).

  Definition alloc_pgd_page_spec0 (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    when' next == get_pgd_next_spec vmid adt;
    rely is_addr next;
    if next + PAGE_SIZE <=? pud_start vmid then
      when adt' == set_pgd_next_spec vmid (VZ64 (next + PAGE_SIZE)) adt;
      when' next' == check64_spec (VZ64 next) adt';
      rely is_int64 next';
      Some (adt', (VZ64 next'))
    else
      when adt' == panic_spec adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next')).

  Definition alloc_pud_page_spec0 (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    when' next == get_pud_next_spec vmid adt;
    rely is_addr next;
    if next + PAGE_SIZE <=? pmd_start vmid then
      when adt' == set_pud_next_spec vmid (VZ64 (next + PAGE_SIZE)) adt;
      when' next' == check64_spec (VZ64 next) adt';
      rely is_int64 next';
      Some (adt', (VZ64 next'))
    else
      when adt' == panic_spec adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next')).

  Definition alloc_pmd_page_spec0 (vmid: Z) (adt: RData) : option (RData * Z64) :=
    rely is_vmid vmid;
    when' next == get_pmd_next_spec vmid adt;
    rely is_addr next;
    if next + PAGE_SIZE <=? pool_end vmid then
      when adt' == set_pmd_next_spec vmid (VZ64 (next + PAGE_SIZE)) adt;
      when' next' == check64_spec (VZ64 next) adt';
      rely is_int64 next';
      Some (adt', (VZ64 next'))
    else
      when adt' == panic_spec adt;
      when' next' == check64_spec (VZ64 next) adt';
      Some (adt', (VZ64 next')).

  Inductive alloc_pgd_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_pgd_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_pgd_page_spec0 (Int.unsigned vmid) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_pgd_page_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive alloc_pud_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_pud_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_pud_page_spec0 (Int.unsigned vmid) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_pud_page_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive alloc_pmd_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_pmd_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_pmd_page_spec0 (Int.unsigned vmid) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_pmd_page_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition alloc_pgd_page_spec_low: compatsem LDATAOps :=
      csem alloc_pgd_page_spec_low_step (type_of_list_type (Tint32::nil)) Tint64.

    Definition alloc_pud_page_spec_low: compatsem LDATAOps :=
      csem alloc_pud_page_spec_low_step (type_of_list_type (Tint32::nil)) Tint64.

    Definition alloc_pmd_page_spec_low: compatsem LDATAOps :=
      csem alloc_pmd_page_spec_low_step (type_of_list_type (Tint32::nil)) Tint64.

  End WITHMEM.

End PTAllocSpecLow.

```
