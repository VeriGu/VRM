# MmioPTWalkSpec

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

Require Import HypsecCommLib.
Require Import MmioPTAlloc.Layer.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import MmioPTAlloc.Spec.

Local Open Scope Z_scope.

Section MmioPTWalkSpec.

  Definition walk_smmu_pgd_spec (ttbr: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match ttbr, addr with
    | VZ64 ttbr, VZ64 addr =>
      if halt adt then Some (adt, VZ64 0) else
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spt := spts (shared adt) in
        let ttbr_pa := phys_page ttbr in
        let pgd_idx := stage2_pgd_index addr in
        let pgd_p := Z.lor ttbr_pa (pgd_idx * 8) in
        rely ((SMMU_POOL_START <=? pgd_p) && (pgd_p <? SMMU_PGD_START));
        let pgd := pgd_p @ (spt_vttbr_pool spt) in
        rely is_int64 pgd;
        if (pgd =? 0) && (alloc =? 1) then
          let (next, end_) := (spt_pgd_next spt, SMMU_PMD_START) in
          rely ((SMMU_PGD_START <=? next) && (next <=? SMMU_PMD_START));
          if next + PAGE_SIZE <=? end_ then
            let pgd' := Z.lor next PUD_TYPE_TABLE in
            let pool' := (spt_vttbr_pool spt) # pgd_p == pgd' in
            let par' := (spt_pgd_par spt) # next == pgd_p in
            let spt' := spt {spt_pgd_next: next + PAGE_SIZE} {spt_vttbr_pool: pool'} {spt_pgd_par: par'} in
            Some (adt {shared: (shared adt) {spts: spt'}}, VZ64 pgd')
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pgd)
      | _ => None
      end
    end.

  Definition walk_smmu_pmd_spec (pgd: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pgd, addr with
    | VZ64 pgd, VZ64 addr =>
      if halt adt then Some (adt, VZ64 0) else
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spt := spts (shared adt) in
        if (pgd =? 0) then Some (adt, VZ64 0) else
        let pgd_pa := phys_page pgd in
        let pmd_idx := pmd_index addr in
        let pmd_p := Z.lor pgd_pa (pmd_idx * 8) in
        rely ((SMMU_PGD_START <=? pmd_p) && (pmd_p <? SMMU_PMD_START));
        let pmd := pmd_p @ (spt_pgd_pool spt) in
        rely is_int64 pmd;
        if (pmd =? 0) && (alloc =? 1) then
          let (next, end_) := (spt_pmd_next spt, SMMU_POOL_END) in
          rely ((SMMU_PMD_START <=? next) && (next <=? SMMU_POOL_END));
          if next + PAGE_SIZE <=? end_ then
            let pmd' := Z.lor next PMD_TYPE_TABLE in
            let pool' := (spt_pgd_pool spt) # pmd_p == pmd' in
            let par' := (spt_pmd_par spt) # next == pmd_p in
            let spt' := spt {spt_pmd_next: next + PAGE_SIZE} {spt_pgd_pool: pool'} {spt_pmd_par: par'} in
            Some (adt {shared: (shared adt) {spts: spt'}}, VZ64 pmd')
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pmd)
      | _ => None
      end
    end.

  Definition walk_smmu_pte_spec (pmd: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match pmd, addr with
    | VZ64 pmd, VZ64 addr =>
      if halt adt then Some (VZ64 0) else
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spt := spts (shared adt) in
        if (pmd =? 0) then Some (VZ64 0) else
        let pmd_pa := phys_page pmd in
        let pte_idx := pte_index addr in
        let pte_p := Z.lor pmd_pa (pte_idx * 8) in
        rely ((SMMU_PMD_START <=? pte_p) && (pte_p <? SMMU_POOL_END));
        let pte := pte_p @ (spt_pmd_pool spt) in
        rely is_int64 pte;
        Some (VZ64 pte)
      | _ => None
      end
    end.

  Definition set_smmu_pte_spec (pmd: Z64) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match pmd, addr, pte with
    | VZ64 pmd, VZ64 addr, VZ64 pte =>
      if halt adt then Some adt else
      if tstate adt =? 0 then
        let id := SPT_ID in
        match ZMap.get id (lock adt) with
        | LockOwn true =>
          let spt := spts (shared adt) in
          let pmd_pa := phys_page pmd in
          let pte_idx :=  pte_index addr in
          let pte_p := Z.lor pmd_pa (pte_idx * 8) in
          rely ((SMMU_PMD_START <=? pte_p) && (pte_p <? SMMU_POOL_END));
          let pool' := ZMap.set pte_p pte (spt_pmd_pool spt) in
          Some (adt {tstate: 1} {shared: (shared adt) {spts: spt {spt_pmd_pool: pool'}}})
        | _ => None
        end
      else None
    end.

End MmioPTWalkSpec.

Section MmioPTWalkSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioPTAlloc_ops) LDATA).

  Definition walk_smmu_pgd_spec0 (ttbr: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match ttbr, addr with
    | VZ64 ttbr, VZ64 addr =>
      let ttbr_pa := phys_page ttbr in
      let pgd_idx := stage2_pgd_index addr in
      let p := Z.lor ttbr_pa (pgd_idx * 8) in
      when' pgd == smmu_pt_load_spec (VZ64 p) adt;
      rely is_int64 pgd;
      if (pgd =? 0) && (alloc =? 1) then
        when' pgd_pa, adt' == alloc_smmu_pgd_page_spec adt;
        rely is_addr pgd_pa;
        let pgd' := Z.lor pgd_pa PUD_TYPE_TABLE in
        when adt'' == smmu_pt_store_spec (VZ64 p) (VZ64 pgd') adt';
        when' res == check64_spec (VZ64 pgd') adt'';
        Some (adt'', VZ64 res)
      else
        when' res == check64_spec (VZ64 pgd) adt;
        Some (adt, VZ64 res)
    end.

  Definition walk_smmu_pmd_spec0 (pgd: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pgd, addr with
    | VZ64 pgd, VZ64 addr =>
      if (pgd =? 0) then
        when' res == check64_spec (VZ64 0) adt;
        Some (adt, VZ64 res)
      else
        let pgd_pa := phys_page pgd in
        let pmd_idx := pmd_index addr in
        let p := Z.lor pgd_pa (pmd_idx * 8) in
        when' pmd == smmu_pt_load_spec (VZ64 p) adt;
        rely is_int64 pmd;
        if (pmd =? 0) && (alloc =? 1) then
          when' pmd_pa, adt' == alloc_smmu_pmd_page_spec adt;
          rely is_addr pmd_pa;
          let pmd' := Z.lor pmd_pa PMD_TYPE_TABLE in
          when adt'' == smmu_pt_store_spec (VZ64 p) (VZ64 pmd') adt';
          when' res == check64_spec (VZ64 pmd') adt'';
          Some (adt'', VZ64 res)
        else
          when' res == check64_spec (VZ64 pmd) adt;
          Some (adt, VZ64 res)
end.

  Definition walk_smmu_pte_spec0 (pmd: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match pmd, addr with
    | VZ64 pmd, VZ64 addr =>
      if (pmd =? 0) then
        when' res == check64_spec (VZ64 0) adt;
        Some (VZ64 res)
      else
        let pmd_pa := phys_page pmd in
        let pte_idx := pte_index addr in
        let p := Z.lor pmd_pa (pte_idx * 8) in
        when' pte == smmu_pt_load_spec (VZ64 p) adt;
        rely is_int64 pte;
        when' res == check64_spec (VZ64 pte) adt;
        Some (VZ64 res)
    end.

  Definition set_smmu_pte_spec0 (pmd: Z64) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match pmd, addr, pte with
    | VZ64 pmd, VZ64 addr, VZ64 pte' =>
      let pmd_pa := phys_page pmd in
      let pte_idx := pte_index addr in
      let p := Z.lor pmd_pa (pte_idx * 8) in
      smmu_pt_store_spec (VZ64 p) (VZ64 pte') adt
    end.

  Inductive walk_smmu_pgd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_smmu_pgd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' ttbr addr alloc res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_smmu_pgd_spec0 (VZ64 (Int64.unsigned ttbr)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_smmu_pgd_spec_low_step s WB ((Vlong ttbr)::(Vlong addr)::(Vint alloc)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive walk_smmu_pmd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_smmu_pmd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pgd addr alloc res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_smmu_pmd_spec0 (VZ64 (Int64.unsigned pgd)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_smmu_pmd_spec_low_step s WB ((Vlong pgd)::(Vlong addr)::(Vint alloc)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive walk_smmu_pte_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_smmu_pte_spec_low_intro s (WB: _ -> Prop) m'0 labd pmd addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_smmu_pte_spec0 (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      walk_smmu_pte_spec_low_step s WB ((Vlong pmd)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive set_smmu_pte_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_smmu_pte_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pmd addr pte
      (Hinv: high_level_invariant labd)
      (Hspec: set_smmu_pte_spec0 (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      set_smmu_pte_spec_low_step s WB ((Vlong pmd)::(Vlong addr)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition walk_smmu_pgd_spec_low: compatsem LDATAOps :=
      csem walk_smmu_pgd_spec_low_step (type_of_list_type (Tint64::Tint64::Tint32::nil)) Tint64.

    Definition walk_smmu_pmd_spec_low: compatsem LDATAOps :=
      csem walk_smmu_pmd_spec_low_step (type_of_list_type (Tint64::Tint64::Tint32::nil)) Tint64.

    Definition walk_smmu_pte_spec_low: compatsem LDATAOps :=
      csem walk_smmu_pte_spec_low_step (type_of_list_type (Tint64::Tint64::nil)) Tint64.

    Definition set_smmu_pte_spec_low: compatsem LDATAOps :=
      csem set_smmu_pte_spec_low_step (type_of_list_type (Tint64::Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End MmioPTWalkSpecLow.

```
