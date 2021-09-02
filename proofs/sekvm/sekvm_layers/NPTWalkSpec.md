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

Require Import HypsecCommLib.
Require Import Constants.
Require Import PTWalk.Layer.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import PTWalk.Spec.

Local Open Scope Z_scope.

Fixpoint local_mmap_loop (n: nat) (gfn: Z) (pfn: Z) (level: Z) (pte: Z) (pt': ZMap.t (Z*Z*Z)) :=
  match n with
  | O => Some (gfn, pfn, pt')
  | S m =>
    match local_mmap_loop m gfn pfn level pte pt' with
    | Some (gfn', pfn', pt0) =>
      Some (gfn'+1, pfn'+1, ZMap.set gfn' (pfn', level, pte) pt0)
    | _ => None
    end
  end.

Definition local_mmap (vmid: Z) (addr: Z) (level: Z) (pte: Z) (npt: NPT) :=
  if level =? 2 then
    let gfn := addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD in
    let pfn := (phys_page pte) / PAGE_SIZE in
    if pmd_table pte =? PMD_TYPE_TABLE then None
    else
      let pgd_next' := (if (pgd_index addr) @ (pgd_t npt) then (pt_pgd_next npt) else (pt_pgd_next npt) + PAGE_SIZE) in
      let pud_next' := (if (pud_index addr) @ ((pgd_index addr) @ (pud_t npt))
                        then (pt_pud_next npt) else (pt_pud_next npt) + PAGE_SIZE) in
      if (pgd_next' <=? pud_start vmid) && (pud_next'  <=? pmd_start vmid) then
        match local_mmap_loop (Z.to_nat PTRS_PER_PMD) gfn pfn 2 pte (pt npt) with
        | Some (_, _, pt') =>
          let npt' := npt {pt: pt'} {pgd_t: ZMap.set (pgd_index addr) true (pgd_t npt)}
                          {pud_t: (pud_t npt) # (pgd_index addr) == (((pgd_index addr) @ (pud_t npt)) # (pud_index addr) == true)}
                          {pmd_t: (pmd_t npt) # (pgd_index addr) ==
                                  (((pgd_index addr) @ (pmd_t npt)) # (pud_index addr) ==
                                   (((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt))) # (pmd_index addr) == false))}
                          {pt_pgd_next: pgd_next'} {pt_pud_next: pud_next'}
          in
          Some (false, npt')
        | _ => None
        end
      else Some (true, npt)
  else
    let gfn := addr / PAGE_SIZE in
    let pfn := (phys_page pte) / PAGE_SIZE in
    match gfn @ (pt npt) with
    | (pfn0, level0, pte0) =>
      if level0 =? 2 then Some (true, npt)
      else
        let pgd_next' := (if (pgd_index addr) @ (pgd_t npt) then (pt_pgd_next npt) else (pt_pgd_next npt) + PAGE_SIZE) in
        let pud_next' := (if (pud_index addr) @ ((pgd_index addr) @ (pud_t npt))
                          then (pt_pud_next npt) else (pt_pud_next npt) + PAGE_SIZE) in
        let pmd_next' := (if (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt)))
                          then (pt_pmd_next npt) else (pt_pmd_next npt) + PAGE_SIZE) in
        if (pgd_next' <=? pud_start vmid) && (pud_next'  <=? pmd_start vmid) && (pmd_next' <=? pool_end vmid) then
          match local_mmap_loop 1 gfn pfn 3 pte (pt npt) with
          | Some (_, _, pt') =>
            let npt' := npt {pt: pt'}
                            {pgd_t: (pgd_t npt) # (pgd_index addr) == true}
                            {pud_t: (pud_t npt) # (pgd_index addr) ==
                                    (((pgd_index addr) @ (pud_t npt)) # (pud_index addr) == true)}
                            {pmd_t: (pmd_t npt) # (pgd_index addr) ==
                                    (((pgd_index addr) @ (pmd_t npt)) # (pud_index addr) ==
                                     (((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt))) # (pmd_index addr) == true))}
                            {pt_pgd_next: pgd_next'} {pt_pud_next: pud_next'} {pt_pmd_next: pmd_next'}
            in
            Some (false, npt')
          | _ => None
          end
        else Some (true, npt)
    end.


Section NPTWalkSpec.

  Definition get_npt_level_spec (vmid: Z) (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some 0 else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := ZMap.get vmid (npts (shared adt)) in
        let gfn := addr / PAGE_SIZE in
        match ZMap.get gfn (pt npt) with
        | (pfn, level, pte) =>
          if phys_page pte =? 0 then Some 0
          else Some level
        end
      | _  => None
      end
    end.

  Definition walk_npt_spec (vmid: Z) (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some (VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := ZMap.get vmid (npts (shared adt)) in
        let gfn := addr / PAGE_SIZE in
        match ZMap.get gfn (pt npt) with
        | (pfn, level, pte) => Some (VZ64 pte)
        end
      | _  => None
      end
    end.

  Definition set_npt_spec (vmid: Z) (addr: Z64) (level: Z) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      rely (tstate adt =? 0);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        if (level =? 2) || (level =? 3) then
          if pte =? 0 then None else
          let npts0 := npts (shared adt) in
          match local_mmap vmid addr level pte (vmid @ npts0) with
          | Some (halt', npt') =>
            Some adt {tstate: if halt' then 0 else 1} {halt: halt'} {shared: (shared adt) {npts: npts0 # vmid == npt'}}
          | _ => None
          end
        else None
      | _  => None
      end
    end.

  Definition mem_load_ref_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

  Definition mem_store_ref_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

End NPTWalkSpec.

Section NPTWalkSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := PTWalk_ops) LDATA).

  Definition get_npt_level_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      when' vttbr == get_pt_vttbr_spec vmid adt;
      rely is_int64 vttbr;
      when' pgd, adt1 == walk_pgd_spec vmid (VZ64 vttbr) (VZ64 addr) 0 adt;
      rely is_int64 pgd;
      when' pud, adt2 == walk_pud_spec vmid (VZ64 pgd) (VZ64 addr) 0 adt;
      rely is_int64 pud;
      when' pmd, adt3 == walk_pmd_spec vmid (VZ64 pud) (VZ64 addr) 0 adt;
      rely is_int64 pmd;
      if pmd_table pmd =? PMD_TYPE_TABLE then
        when' pte == walk_pte_spec vmid (VZ64 pmd) (VZ64 addr) adt3;
        rely is_int64 pte;
        if phys_page pte =? 0 then check_spec 0 adt else check_spec 3 adt
      else
        if phys_page pmd =? 0 then check_spec 0 adt else check_spec 2 adt
    end.

  Definition walk_npt_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      when' vttbr == get_pt_vttbr_spec vmid adt;
      rely is_int64 vttbr;
      when' pgd, adt1 == walk_pgd_spec vmid (VZ64 vttbr) (VZ64 addr) 0 adt;
      rely is_int64 pgd;
      when' pud, adt2 == walk_pud_spec vmid (VZ64 pgd) (VZ64 addr) 0 adt;
      rely is_int64 pud;
      when' pmd, adt3 == walk_pmd_spec vmid (VZ64 pud) (VZ64 addr) 0 adt;
      rely is_int64 pmd;
      if pmd_table pmd =? PMD_TYPE_TABLE then
        when' pte == walk_pte_spec vmid (VZ64 pmd) (VZ64 addr) adt;
        rely is_int64 pte;
        when' res == check64_spec (VZ64 pte) adt;
        Some (VZ64 res)
      else
        when' res == check64_spec (VZ64 pmd) adt;
        Some (VZ64 res)
    end.

  Definition set_npt_spec0 (vmid: Z) (addr: Z64) (level: Z) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      when' vttbr == get_pt_vttbr_spec vmid adt;
      rely is_int64 vttbr;
      when' pgd, adt1 == walk_pgd_spec vmid (VZ64 vttbr) (VZ64 addr) 1 adt;
      rely is_int64 pgd;
      when' pud, adt2 == walk_pud_spec vmid (VZ64 pgd) (VZ64 addr) 1 adt1;
      rely is_int64 pud;
      if level =? 2 then
        set_pmd_spec vmid (VZ64 pud) (VZ64 addr) (VZ64 pte) adt2
      else
        when' pmd, adt3 == walk_pmd_spec vmid (VZ64 pud) (VZ64 addr) 1 adt2;
        rely is_int64 pmd;
        if pmd_table pmd =? PMD_TYPE_TABLE then
          set_pte_spec vmid (VZ64 pmd) (VZ64 addr) (VZ64 pte) adt3
        else
          panic_spec adt3
    end.

  Definition mem_load_ref_spec0 (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      mem_load_raw_spec (VZ64 gfn) reg adt
    end.

  Definition mem_store_ref_spec0 (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      mem_store_raw_spec (VZ64 gfn) reg adt
    end.

  Inductive get_npt_level_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_npt_level_spec_low_intro s (WB: _ -> Prop) m'0 labd vmid addr res
      (Hinv: high_level_invariant labd)
      (Hspec: get_npt_level_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) labd = Some (Int.unsigned res)):
      get_npt_level_spec_low_step s WB ((Vint vmid)::(Vlong addr)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive walk_npt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_npt_spec_low_intro s (WB: _ -> Prop) m'0 labd vmid addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_npt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      walk_npt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive set_npt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_npt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr level pte
      (Hinv: high_level_invariant labd)
      (Hspec: set_npt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (Int.unsigned level) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      set_npt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vint level)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive mem_load_ref_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | mem_load_ref_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg
      (Hinv: high_level_invariant labd)
      (Hspec: mem_load_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) labd = Some labd'):
      mem_load_ref_spec_low_step s WB ((Vlong gfn)::(Vint reg)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive mem_store_ref_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | mem_store_ref_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg
      (Hinv: high_level_invariant labd)
      (Hspec: mem_store_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) labd = Some labd'):
      mem_store_ref_spec_low_step s WB ((Vlong gfn)::(Vint reg)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_npt_level_spec_low: compatsem LDATAOps :=
      csem get_npt_level_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tint32.

    Definition walk_npt_spec_low: compatsem LDATAOps :=
      csem walk_npt_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tint64.

    Definition set_npt_spec_low: compatsem LDATAOps :=
      csem set_npt_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::Tint64::nil)) Tvoid.

    Definition mem_load_ref_spec_low: compatsem LDATAOps :=
      csem mem_load_ref_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

    Definition mem_store_ref_spec_low: compatsem LDATAOps :=
      csem mem_store_ref_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

  End WITHMEM.

End NPTWalkSpecLow.

```
