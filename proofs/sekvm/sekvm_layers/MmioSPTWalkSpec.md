# MmioSPTWalkSpec

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

Require Import MmioPTWalk.Spec.
Require Import RData.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import MmioPTWalk.Layer.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MmioSPTWalkSpec.

  Definition clear_smmu_pt_spec (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    rely is_smmu index; rely is_smmu_cfg cbndx;
    if halt adt then Some adt else
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let ttbr := SMMU_TTBR index cbndx in
      let spt := spts (shared adt) in
      let pt0 := ZMap.init (0, 0) in
      let pgd_t0 := ZMap.init false in
      let pmd_t0 := ZMap.init (ZMap.init false) in
      let spt' := spt {spt_pt: (spt_pt spt) # ttbr == pt0} {spt_pgd_t: (spt_pgd_t spt) # ttbr == pgd_t0} {spt_pmd_t: (spt_pmd_t spt) # ttbr == pmd_t0} in
      Some adt {tstate: 1} {shared: (shared adt) {spts: spt'}}
    | _  => None
    end.

  Definition walk_smmu_pt_spec (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr addr;
      if halt adt then Some (VZ64 0) else
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let ttbr := SMMU_TTBR index cbndx in
        let pt := ttbr @ (spt_pt (spts (shared adt))) in
        let gfn := addr / PAGE_SIZE in
        match ZMap.get gfn pt with
        | (pfn, pte) => Some (VZ64 pte)
        end
      | _  => None
      end
    end.

  Definition local_spt_map (cbndx: Z) (index: Z) (addr: Z) (pte: Z) (spt: SPT) :=
    let gfn := addr / PAGE_SIZE in
    let pfn := (phys_page pte) / PAGE_SIZE in
    let ttbr := SMMU_TTBR index cbndx in
    let pt := ttbr @ (spt_pt spt) in
    match gfn @ pt with
    | (pfn0, pte0) =>
      let pgd_next' := (if (stage2_pgd_index addr) @ (ttbr @ (spt_pgd_t spt)) then (spt_pgd_next spt) else (spt_pgd_next spt) + PAGE_SIZE) in
      let pmd_next' := (if (pmd_index addr) @ ((stage2_pgd_index addr) @ (ttbr @ (spt_pmd_t spt)))
                        then (spt_pmd_next spt) else (spt_pmd_next spt) + PAGE_SIZE) in
      if (pgd_next' <=? SMMU_PMD_START) && (pmd_next'  <=? SMMU_POOL_END) then
        let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (pt # gfn == (pfn, pte))}
                        {spt_pgd_t: (spt_pgd_t spt) # ttbr == ((ttbr @ (spt_pgd_t spt)) # (stage2_pgd_index addr) == true)}
                        {spt_pmd_t: (spt_pmd_t spt) # ttbr ==
                                    ((ttbr @ (spt_pmd_t spt)) # (stage2_pgd_index addr) ==
                                    (((stage2_pgd_index addr) @ (ttbr @ (spt_pmd_t spt))) # (pmd_index addr) == true))}
                        {spt_pgd_next: pgd_next'} {spt_pmd_next: pmd_next'}
        in
        Some (false, spt')
      else Some (true, spt)
    end.

  Definition set_smmu_pt_spec (cbndx: Z) (index: Z) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_smmu index; rely is_smmu_cfg cbndx;
      rely is_smmu_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      rely (tstate adt =? 0);
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        match local_spt_map cbndx index addr pte (spts (shared adt)) with
        | Some (halt', spt') =>
          Some adt {tstate: if halt' then 0 else 1} {halt: halt'} {shared: (shared adt) {spts: spt'}}
        | _ => None
        end
      | _  => None
      end
    end.

  Definition dev_load_ref_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      dev_load_raw_spec (VZ64 gfn) reg cbndx index adt
    end.

  Definition dev_store_ref_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      dev_store_raw_spec (VZ64 gfn) reg cbndx index adt
    end.

End MmioSPTWalkSpec.

Section MmioSPTWalkSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioPTWalk_ops) LDATA).

  Definition clear_smmu_pt_spec0 (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    smmu_pt_clear_spec cbndx index adt.

  Definition walk_smmu_pt_spec0 (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      when' ttbr == get_smmu_cfg_hw_ttbr_spec cbndx index adt;
      rely is_int64 ttbr;
      when' pgd, adt1 == walk_smmu_pgd_spec (VZ64 ttbr) (VZ64 addr) 0 adt;
      rely is_int64 pgd;
      when' pmd, adt2 == walk_smmu_pmd_spec (VZ64 pgd) (VZ64 addr) 0 adt;
      rely is_int64 pmd;
      when' pte == walk_smmu_pte_spec (VZ64 pmd) (VZ64 addr) adt;
      rely is_int64 pte;
      check64_spec (VZ64 pte) adt
    end.

  Definition set_smmu_pt_spec0 (cbndx: Z) (index: Z) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      when' ttbr == get_smmu_cfg_hw_ttbr_spec cbndx index adt;
      rely is_int64 ttbr;
      when' pgd, adt1 == walk_smmu_pgd_spec (VZ64 ttbr) (VZ64 addr) 1 adt;
      rely is_int64 pgd;
      when' pmd, adt2 == walk_smmu_pmd_spec (VZ64 pgd) (VZ64 addr) 1 adt1;
      rely is_int64 pmd;
      set_smmu_pte_spec (VZ64 pmd) (VZ64 addr) (VZ64 pte) adt2
    end.

  Definition dev_load_ref_spec0 (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      dev_load_raw_spec (VZ64 gfn) reg cbndx index adt
    end.

  Definition dev_store_ref_spec0 (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match gfn with
    | VZ64 gfn =>
      dev_store_raw_spec (VZ64 gfn) reg cbndx index adt
    end.

  Inductive clear_smmu_pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_smmu_pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: clear_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      clear_smmu_pt_spec_low_step s WB ((Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive walk_smmu_pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_smmu_pt_spec_low_intro s (WB: _ -> Prop) m'0 labd cbndx index addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      walk_smmu_pt_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive set_smmu_pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_smmu_pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx num addr pte
      (Hinv: high_level_invariant labd)
      (Hspec: set_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned num) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      set_smmu_pt_spec_low_step s WB ((Vint cbndx)::(Vint num)::(Vlong addr)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive dev_load_ref_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | dev_load_ref_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: dev_load_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      dev_load_ref_spec_low_step s WB ((Vlong gfn)::(Vint reg)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive dev_store_ref_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | dev_store_ref_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: dev_store_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      dev_store_ref_spec_low_step s WB ((Vlong gfn)::(Vint reg)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition clear_smmu_pt_spec_low: compatsem LDATAOps :=
      csem clear_smmu_pt_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition walk_smmu_pt_spec_low: compatsem LDATAOps :=
      csem walk_smmu_pt_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::nil)) Tint64.

    Definition set_smmu_pt_spec_low: compatsem LDATAOps :=
      csem set_smmu_pt_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition dev_load_ref_spec_low: compatsem LDATAOps :=
      csem dev_load_ref_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition dev_store_ref_spec_low: compatsem LDATAOps :=
      csem dev_store_ref_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End MmioSPTWalkSpecLow.

```
