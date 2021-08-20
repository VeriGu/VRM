# MemoryOpsSpec

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

Require Import MemManager.Layer.
Require Import NPTOps.Spec.
Require Import MemManager.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MemoryOpsSpec.

  Fixpoint clear_vm_loop (n: nat) (pfn: Z) (vmid: Z) (adt: RData) :=
    match n with
    | O => Some (pfn, adt)
    | S n' =>
      match clear_vm_loop n' pfn vmid adt with
      | Some (pfn', adt') =>
        rely is_pfn pfn';
        when adt'' == clear_vm_page_spec vmid (VZ64 pfn') adt';
        Some (pfn' + 1, adt'')
      | _ => None
      end
    end.

  Definition clear_vm_range_spec (vmid: Z) (pfn: Z64) (num: Z64) (adt: RData) : option RData :=
    match pfn, num with
    | VZ64 pfn, VZ64 num =>
      rely is_pfn pfn; rely is_pfn num;
      match clear_vm_loop (Z.to_nat num) pfn vmid adt with
      | Some (pfn', adt'') =>
        rely is_int64 pfn'; Some adt''
      | _ => None
      end
    end.

  Fixpoint prot_and_map_vm_loop (n: nat) (vmid: Z) (gfn: Z) (pfn: Z) (adt: RData) :=
    match n with
    | O => Some (gfn, pfn, adt)
    | S n' =>
      match prot_and_map_vm_loop n' vmid gfn pfn adt with
      | Some (gfn', pfn', adt') =>
        rely is_gfn gfn'; rely is_pfn pfn';
        when adt'' == assign_pfn_to_vm_spec vmid (VZ64 gfn') (VZ64 pfn') adt';
        Some (gfn' + 1, pfn' + 1, adt'')
      | _ => None
      end
    end.

  Definition prot_and_map_vm_s2pt_spec (vmid: Z) (addr: Z64) (pte: Z64) (level: Z) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr;
      let target := phys_page pte in
      let pfn := target / PAGE_SIZE in
      let gfn := addr / PAGE_SIZE in
      if level =? 2 then
        let gfn' := gfn / PTRS_PER_PMD * PTRS_PER_PMD in
        let num := PMD_PAGE_NUM in
        match prot_and_map_vm_loop (Z.to_nat num) vmid gfn' pfn adt with
        | Some (gfn', pfn', adt') =>
          rely is_int64 gfn'; rely is_int64 pfn';
          map_pfn_vm_spec vmid (VZ64 addr) (VZ64 pte) level adt'
        | _ => None
        end
      else
        when adt' == assign_pfn_to_vm_spec vmid (VZ64 gfn) (VZ64 pfn) adt;
        map_pfn_vm_spec vmid (VZ64 addr) (VZ64 pte) 3 adt'
    end.

  Fixpoint grant_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
    match n with
    | O => Some (addr, adt)
    | S n' =>
      match grant_stage2_loop n' vmid addr adt with
      | Some (addr', adt') =>
        rely is_addr addr';
        when' pte, adt2 == walk_s2pt_spec vmid (VZ64 addr') adt';
        rely is_int64 pte;
        when level, adt3 == get_level_s2pt_spec vmid (VZ64 addr') adt2;
        rely is_int level;
        let pte_pa := phys_page pte in
        if pte_pa =? 0 then Some (addr' + PAGE_SIZE, adt3)
        else
          let pfn := pte_pa / PAGE_SIZE in
          if level =? 2 then
            let pfn' := pfn + (Z.land (addr' / PAGE_SIZE) 511) in
            when adt4 == grant_vm_page_spec vmid (VZ64 pfn') adt3;
            Some (addr' + PAGE_SIZE, adt4)
          else
            when adt4 == grant_vm_page_spec vmid (VZ64 pfn) adt3;
            Some (addr' + PAGE_SIZE, adt4)
      | _ => None
      end
    end.

    Definition grant_stage2_sg_gpa_spec (vmid: Z) (addr: Z64) (size: Z64) (adt: RData) : option RData :=
      match addr, size with
      | VZ64 addr, VZ64 size =>
        rely is_vm vmid; rely is_addr addr; rely is_addr size;
        let num := (size + 4095) / PAGE_SIZE in
        match grant_stage2_loop (Z.to_nat num) vmid addr adt with
        | Some (addr', adt') =>
          rely is_int64 addr'; Some adt'
        | _ => None
        end
      end.

  Fixpoint revoke_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
    match n with
    | O => Some (addr, adt)
    | S n' =>
      match revoke_stage2_loop n' vmid addr adt with
      | Some (addr', adt') =>
        rely is_addr addr';
        when' pte, adt2 == walk_s2pt_spec vmid (VZ64 addr') adt';
        rely is_int64 pte;
        when level, adt3 == get_level_s2pt_spec vmid (VZ64 addr') adt2;
        rely is_int level;
        let pte_pa := phys_page pte in
        if pte_pa =? 0 then Some (addr' + PAGE_SIZE, adt3)
        else
          let pfn := pte_pa / PAGE_SIZE in
          if level =? 2 then
            let pfn' := pfn + (Z.land (addr' / PAGE_SIZE) 511) in
            when adt4 == revoke_vm_page_spec vmid (VZ64 pfn') adt3;
            Some (addr' + PAGE_SIZE, adt4)
          else
            when adt4 == revoke_vm_page_spec vmid (VZ64 pfn) adt3;
            Some (addr' + PAGE_SIZE, adt4)
      | _ => None
      end
    end.

    Definition revoke_stage2_sg_gpa_spec (vmid: Z) (addr: Z64) (size: Z64) (adt: RData) : option RData :=
      match addr, size with
      | VZ64 addr, VZ64 size =>
        rely is_vm vmid; rely is_addr addr; rely is_addr size;
        let num := (size + 4095) / PAGE_SIZE in
        match revoke_stage2_loop (Z.to_nat num) vmid addr adt with
        | Some (addr', adt') =>
          rely is_int64 addr'; Some adt'
        | _ => None
        end
      end.

End MemoryOpsSpec.

Section MemoryOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MemManager_ops) LDATA).

  Inductive clear_vm_range_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_vm_range_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn num
      (Hinv: high_level_invariant labd)
      (Hspec: clear_vm_range_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned num)) labd = Some labd'):
      clear_vm_range_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::(Vlong num)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive prot_and_map_vm_s2pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | prot_and_map_vm_s2pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr pte level
      (Hinv: high_level_invariant labd)
      (Hspec: prot_and_map_vm_s2pt_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) (Int.unsigned level) labd = Some labd'):
      prot_and_map_vm_s2pt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vlong pte)::(Vint level)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive grant_stage2_sg_gpa_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | grant_stage2_sg_gpa_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr size
      (Hinv: high_level_invariant labd)
      (Hspec: grant_stage2_sg_gpa_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned size)) labd = Some labd'):
      grant_stage2_sg_gpa_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vlong size)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive revoke_stage2_sg_gpa_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | revoke_stage2_sg_gpa_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr size
      (Hinv: high_level_invariant labd)
      (Hspec: revoke_stage2_sg_gpa_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned size)) labd = Some labd'):
      revoke_stage2_sg_gpa_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vlong size)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition clear_vm_range_spec_low: compatsem LDATAOps :=
      csem clear_vm_range_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition prot_and_map_vm_s2pt_spec_low: compatsem LDATAOps :=
      csem prot_and_map_vm_s2pt_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint32::nil)) Tvoid.

    Definition grant_stage2_sg_gpa_spec_low: compatsem LDATAOps :=
      csem grant_stage2_sg_gpa_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition revoke_stage2_sg_gpa_spec_low: compatsem LDATAOps :=
      csem revoke_stage2_sg_gpa_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End MemoryOpsSpecLow.

```
