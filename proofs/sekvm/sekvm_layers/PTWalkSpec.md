# PTWalkSpec

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

Require Import PTAlloc.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import PTAlloc.Spec.
Require Import AbstractMachine.Spec.
Require Import RData.

Local Open Scope Z_scope.

Section PTWalkSpec.

  Definition walk_pgd_spec (vmid: Z) (vttbr: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match vttbr, addr with
    | VZ64 vttbr, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        let vttbr_pa := phys_page vttbr in
        let pgd_idx := pgd_index addr in
        let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
        rely ((pool_start vmid <=? pgd_p) && (pgd_p <? pgd_start vmid));
        let pgd := pgd_p @ (pt_vttbr_pool npt) in
        rely is_int64 pgd;
        if (pgd =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pgd_next npt, pud_start vmid) in
          rely ((pgd_start vmid <=? next) && (next <=? pud_start vmid));
          if next + PAGE_SIZE <=? end_ then
            let pgd' := Z.lor next PUD_TYPE_TABLE in
            let pool' := (pt_vttbr_pool npt) # pgd_p == pgd' in
            let updates' := (UPDATE_PGD pgd_p pgd') :: (pt_updates npt) in
            let par' := (pt_pgd_par npt) # next == pgd_p in
            let npt' := npt {pt_pgd_next: next + PAGE_SIZE} {pt_vttbr_pool: pool'} {pt_pgd_par: par'} {pt_updates: updates'} in
            Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pgd')
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pgd)
      | _ => None
      end
    end.

  Definition walk_pud_spec (vmid: Z) (pgd: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pgd, addr with
    | VZ64 pgd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pgd =? 0) then Some (adt, VZ64 0) else
        let pgd_pa := phys_page pgd in
        let pud_idx := pud_index addr in
        let pud_p := Z.lor pgd_pa (pud_idx * 8) in
        rely ((pgd_start vmid <=? pud_p) && (pud_p <? pud_start vmid));
        let pud := pud_p @ (pt_pgd_pool npt) in
        rely is_int64 pud;
        if (pud =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pud_next npt, pmd_start vmid) in
          rely ((pud_start vmid <=? next) && (next <=? pmd_start vmid));
          if next + PAGE_SIZE <=? end_ then
            let pud' := Z.lor next PUD_TYPE_TABLE in
            let pool' := (pt_pgd_pool npt) # pud_p == pud' in
            let updates' := (UPDATE_PUD pud_p pud') :: (pt_updates npt) in
            let par' := (pt_pud_par npt) # next == pud_p in
            let npt' := npt {pt_pud_next: next + PAGE_SIZE} {pt_pgd_pool: pool'} {pt_pud_par: par'} {pt_updates: updates'} in
            Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pud')
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pud)
      | _ => None
      end
    end.

  Definition walk_pmd_spec (vmid: Z) (pud: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pud, addr with
    | VZ64 pud, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pud =? 0) then Some (adt, VZ64 0) else
        let pud_pa := phys_page pud in
        let pmd_idx := pmd_index addr in
        let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
        rely ((pud_start vmid <=? pmd_p) && (pmd_p <? pmd_start vmid));
        let pmd := pmd_p @ (pt_pud_pool npt) in
        rely is_int64 pmd;
        if (pmd =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pmd_next npt, pool_end vmid) in
          rely ((pmd_start vmid <=? next) && (next <=? pool_end vmid));
          if next + PAGE_SIZE <=? end_ then
            let pmd' := Z.lor next PMD_TYPE_TABLE in
            let pool' := (pt_pud_pool npt) # pmd_p == pmd' in
            let updates' := (UPDATE_PMD pmd_p pmd') :: (pt_updates npt) in
            let par' := (pt_pmd_par npt) # next == pmd_p in
            let npt' := npt {pt_pmd_next: next + PAGE_SIZE} {pt_pud_pool: pool'} {pt_pmd_par: par'} {pt_updates: updates'} in
            Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pmd')
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pmd)
      | _ => None
      end
    end.

  Definition walk_pte_spec (vmid: Z) (pmd: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match pmd, addr with
    | VZ64 pmd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := ZMap.get vmid (npts (shared adt)) in
        if (pmd =? 0) then Some (VZ64 0) else
        let pmd_pa := phys_page pmd in
        let pte_idx := pte_index addr in
        let pte_p := Z.lor pmd_pa (pte_idx * 8) in
        rely ((pmd_start vmid <=? pte_p) && (pte_p <? pool_end vmid));
        let pte := pte_p @ (pt_pmd_pool npt) in
        rely is_int64 pte;
        Some (VZ64 pte)
      | _ => None
      end
    end.

  Definition set_pmd_spec (vmid: Z) (pud: Z64) (addr: Z64) (pmd: Z64) (adt: RData) : option RData :=
    match pud, pmd, addr with
    | VZ64 pud, VZ64 pmd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some adt else
      if pmd_table pmd =? PMD_TYPE_TABLE then None else
      if tstate adt =? 0 then
        let id := NPT_ID + vmid in
        match ZMap.get id (lock adt) with
        | LockOwn true =>
          let npt := ZMap.get vmid (npts (shared adt)) in
          let pud_pa := phys_page pud in
          let pmd_idx :=  pmd_index addr in
          let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
          rely ((pud_start vmid <=? pmd_p) && (pmd_p <? pmd_start vmid));
          let pool' := ZMap.set pmd_p pmd (pt_pud_pool npt) in
          let updates' := (UPDATE_PMD pmd_p pmd) :: (pt_updates npt) in
          Some (adt {tstate: 1} {shared: (shared adt) {npts: ZMap.set vmid (npt {pt_pud_pool: pool'} {pt_updates: updates'}) (npts (shared adt))}})
        | _ => None
        end
      else None
    end.

  Definition set_pte_spec (vmid: Z) (pmd: Z64) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match pmd, addr, pte with
    | VZ64 pmd, VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some adt else
      if tstate adt =? 0 then
        let id := NPT_ID + vmid in
        match ZMap.get id (lock adt) with
        | LockOwn true =>
          let npt := ZMap.get vmid (npts (shared adt)) in
          let pmd_pa := phys_page pmd in
          let pte_idx :=  pte_index addr in
          let pte_p := Z.lor pmd_pa (pte_idx * 8) in
          rely ((pmd_start vmid <=? pte_p) && (pte_p <? pool_end vmid));
          let pool' := ZMap.set pte_p pte (pt_pmd_pool npt) in
          let updates' := (UPDATE_PTE pte_p pte) :: (pt_updates npt) in
          Some (adt {tstate: 1} {shared: (shared adt) {npts: ZMap.set vmid (npt {pt_pmd_pool: pool'} {pt_updates: updates'}) (npts (shared adt))}})
        | _ => None
        end
      else None
    end.

  (*

  Definition walk_pgd_spec (vmid: Z) (vttbr: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match vttbr, addr with
    | VZ64 vttbr, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        let vttbr_pa := phys_page vttbr in
        let pgd_idx := pgd_index addr in
        let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
        rely ((pool_start vmid <=? pgd_p) && (pgd_p <? pgd_start vmid));
        let pgd := pgd_p @ (pt_vttbr_pool npt) in
        rely is_int64 pgd;
        if (pgd =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pgd_next npt, pud_start vmid) in
          rely ((pgd_start vmid <=? next) && (next <=? pud_start vmid));
          if next + PAGE_SIZE <=? end_ then
            let pgd' := Z.lor next PUD_TYPE_TABLE in
            let pool' := (pt_vttbr_pool npt) # pgd_p == pgd' in
            let par' := (pt_pgd_par npt) # next == pgd_p in
            let npt' := npt {pt_pgd_next: next + PAGE_SIZE} {pt_vttbr_pool: pool'} {pt_pgd_par: par'} in
            if verify_observe (observe_pt vmid npt) (observe_pt vmid npt') then
              Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pgd')
            else None
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pgd)
      | _ => None
      end
    end.

  Definition walk_pud_spec (vmid: Z) (pgd: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pgd, addr with
    | VZ64 pgd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pgd =? 0) then Some (adt, VZ64 0) else
        let pgd_pa := phys_page pgd in
        let pud_idx := pud_index addr in
        let pud_p := Z.lor pgd_pa (pud_idx * 8) in
        rely ((pgd_start vmid <=? pud_p) && (pud_p <? pud_start vmid));
        let pud := pud_p @ (pt_pgd_pool npt) in
        rely is_int64 pud;
        if (pud =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pud_next npt, pmd_start vmid) in
          rely ((pud_start vmid <=? next) && (next <=? pmd_start vmid));
          if next + PAGE_SIZE <=? end_ then
            let pud' := Z.lor next PUD_TYPE_TABLE in
            let pool' := (pt_pgd_pool npt) # pud_p == pud' in
            let par' := (pt_pud_par npt) # next == pud_p in
            let npt' := npt {pt_pud_next: next + PAGE_SIZE} {pt_pgd_pool: pool'} {pt_pud_par: par'} in
            if verify_observe (observe_pt vmid npt) (observe_pt vmid npt') then
              Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pud')
            else None
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pud)
      | _ => None
      end
    end.

  Definition walk_pmd_spec (vmid: Z) (pud: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pud, addr with
    | VZ64 pud, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (adt, VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pud =? 0) then Some (adt, VZ64 0) else
        let pud_pa := phys_page pud in
        let pmd_idx := pmd_index addr in
        let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
        rely ((pud_start vmid <=? pmd_p) && (pmd_p <? pmd_start vmid));
        let pmd := pmd_p @ (pt_pud_pool npt) in
        rely is_int64 pmd;
        if (pmd =? 0) && (alloc =? 1) then
          let (next, end_) := (pt_pmd_next npt, pool_end vmid) in
          rely ((pmd_start vmid <=? next) && (next <=? pool_end vmid));
          if next + PAGE_SIZE <=? end_ then
            let pmd' := Z.lor next PMD_TYPE_TABLE in
            let pool' := (pt_pud_pool npt) # pmd_p == pmd' in
            let par' := (pt_pmd_par npt) # next == pmd_p in
            let npt' := npt {pt_pmd_next: next + PAGE_SIZE} {pt_pud_pool: pool'} {pt_pmd_par: par'} in
            if verify_observe (observe_pt vmid npt) (observe_pt vmid npt') then
              Some (adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}, VZ64 pmd')
            else None
          else Some (adt {halt: true}, VZ64 0)
        else Some (adt, VZ64 pmd)
      | _ => None
      end
    end.

  Definition walk_pte_spec (vmid: Z) (pmd: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match pmd, addr with
    | VZ64 pmd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some (VZ64 0) else
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := ZMap.get vmid (npts (shared adt)) in
        if (pmd =? 0) then Some (VZ64 0) else
        let pmd_pa := phys_page pmd in
        let pte_idx := pte_index addr in
        let pte_p := Z.lor pmd_pa (pte_idx * 8) in
        rely ((pmd_start vmid <=? pte_p) && (pte_p <? pool_end vmid));
        let pte := pte_p @ (pt_pmd_pool npt) in
        rely is_int64 pte;
        Some (VZ64 pte)
      | _ => None
      end
    end.

  Definition set_pmd_spec (vmid: Z) (pud: Z64) (addr: Z64) (pmd: Z64) (adt: RData) : option RData :=
    match pud, pmd, addr with
    | VZ64 pud, VZ64 pmd, VZ64 addr =>
      rely is_vmid vmid;
      if halt adt then Some adt else
      if pmd_table pmd =? PMD_TYPE_TABLE then None else
      if tstate adt =? 0 then
        let id := NPT_ID + vmid in
        match ZMap.get id (lock adt) with
        | LockOwn true =>
          let npt := ZMap.get vmid (npts (shared adt)) in
          let pud_pa := phys_page pud in
          let pmd_idx :=  pmd_index addr in
          let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
          rely ((pud_start vmid <=? pmd_p) && (pmd_p <? pmd_start vmid));
          let pool' := ZMap.set pmd_p pmd (pt_pud_pool npt) in
          Some (adt {tstate: 1} {shared: (shared adt) {npts: ZMap.set vmid (npt {pt_pud_pool: pool'}) (npts (shared adt))}})
        | _ => None
        end
      else None
    end.

  Definition set_pte_spec (vmid: Z) (pmd: Z64) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match pmd, addr, pte with
    | VZ64 pmd, VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some adt else
      if tstate adt =? 0 then
        let id := NPT_ID + vmid in
        match ZMap.get id (lock adt) with
        | LockOwn true =>
          let npt := ZMap.get vmid (npts (shared adt)) in
          let pmd_pa := phys_page pmd in
          let pte_idx :=  pte_index addr in
          let pte_p := Z.lor pmd_pa (pte_idx * 8) in
          rely ((pmd_start vmid <=? pte_p) && (pte_p <? pool_end vmid));
          let pool' := ZMap.set pte_p pte (pt_pmd_pool npt) in
          Some (adt {tstate: 1} {shared: (shared adt) {npts: ZMap.set vmid (npt {pt_pmd_pool: pool'}) (npts (shared adt))}})
        | _ => None
        end
      else None
    end.

  *)

End PTWalkSpec.

Section PTWalkSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := PTAlloc_ops) LDATA).

  Definition walk_pgd_spec0 (vmid: Z) (vttbr: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match vttbr, addr with
    | VZ64 vttbr, VZ64 addr =>
      let vttbr_pa := phys_page vttbr in
      let pgd_idx := pgd_index addr in
      let p := Z.lor vttbr_pa (pgd_idx * 8) in
      when' pgd == pt_load_spec vmid (VZ64 p) adt;
      rely is_int64 pgd;
      if (pgd =? 0) && (alloc =? 1) then
        when' pgd_pa, adt' == alloc_pgd_page_spec vmid adt;
        rely is_addr pgd_pa;
        let pgd' := Z.lor pgd_pa PUD_TYPE_TABLE in
        when adt'' == pt_store_spec vmid (VZ64 p) (VZ64 pgd') adt';
        when' res == check64_spec (VZ64 pgd') adt'';
        Some (adt'', VZ64 res)
      else
        when' res == check64_spec (VZ64 pgd) adt;
        Some (adt, VZ64 res)
    end.

  Definition walk_pud_spec0 (vmid: Z) (pgd: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pgd, addr with
    | VZ64 pgd, VZ64 addr =>
      if (pgd =? 0) then
        when' res == check64_spec (VZ64 0) adt;
        Some (adt, VZ64 res)
      else
        let pgd_pa := phys_page pgd in
        let pud_idx := pud_index addr in
        let p := Z.lor pgd_pa (pud_idx * 8) in
        when' pud == pt_load_spec vmid (VZ64 p) adt;
        rely is_int64 pud;
        if (pud =? 0) && (alloc =? 1) then
          when' pud_pa, adt' == alloc_pud_page_spec vmid adt;
          rely is_addr pud_pa;
          let pud' := Z.lor pud_pa PUD_TYPE_TABLE in
          when adt'' == pt_store_spec vmid (VZ64 p) (VZ64 pud') adt';
          when' res == check64_spec (VZ64 pud') adt'';
          Some (adt'', VZ64 res)
        else
          when' res == check64_spec (VZ64 pud) adt;
          Some (adt, VZ64 res)
    end.

  Definition walk_pmd_spec0 (vmid: Z) (pud: Z64) (addr: Z64) (alloc: Z) (adt: RData) : option (RData * Z64) :=
    match pud, addr with
    | VZ64 pud, VZ64 addr =>
      if (pud =? 0) then
        when' res == check64_spec (VZ64 0) adt;
        Some (adt, VZ64 res)
      else
        let pud_pa := phys_page pud in
        let pmd_idx := pmd_index addr in
        let p := Z.lor pud_pa (pmd_idx * 8) in
        when' pmd == pt_load_spec vmid (VZ64 p) adt;
        rely is_int64 pmd;
        if (pmd =? 0) && (alloc =? 1) then
          when' pmd_pa, adt' == alloc_pmd_page_spec vmid adt;
          rely is_addr pmd_pa;
          let pmd' := Z.lor pmd_pa PMD_TYPE_TABLE in
          when adt'' == pt_store_spec vmid (VZ64 p) (VZ64 pmd') adt';
          when' res == check64_spec (VZ64 pmd') adt'';
          Some (adt'', VZ64 res)
        else
          when' res == check64_spec (VZ64 pmd) adt;
          Some (adt, VZ64 res)
    end.

  Definition walk_pte_spec0 (vmid: Z) (pmd: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match pmd, addr with
    | VZ64 pmd, VZ64 addr =>
      if (pmd =? 0) then
        when' res == check64_spec (VZ64 0) adt;
        Some (VZ64 res)
      else
        let pmd_pa := phys_page pmd in
        let pte_idx := pte_index addr in
        let p := Z.lor pmd_pa (pte_idx * 8) in
        when' pte == pt_load_spec vmid (VZ64 p) adt;
        rely is_int64 pte;
        when' res == check64_spec (VZ64 pte) adt;
        Some (VZ64 res)
    end.

  Definition set_pmd_spec0 (vmid: Z) (pud: Z64) (addr: Z64) (pmd: Z64) (adt: RData) : option RData :=
    match pud, addr, pmd with
    | VZ64 pud, VZ64 addr, VZ64 pmd =>
      let pud_pa := phys_page pud in
      let pmd_idx := pmd_index addr in
      let p := Z.lor pud_pa (pmd_idx * 8) in
      pt_store_spec vmid (VZ64 p) (VZ64 pmd) adt
    end.

  Definition set_pte_spec0 (vmid: Z) (pmd: Z64) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match pmd, addr, pte with
    | VZ64 pmd, VZ64 addr, VZ64 pte' =>
      let pmd_pa := phys_page pmd in
      let pte_idx := pte_index addr in
      let p := Z.lor pmd_pa (pte_idx * 8) in
      pt_store_spec vmid (VZ64 p) (VZ64 pte') adt
    end.

  Inductive walk_pgd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_pgd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vttbr addr alloc res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_pgd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned vttbr)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_pgd_spec_low_step s WB ((Vint vmid)::(Vlong vttbr)::(Vlong addr)::(Vint alloc)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive walk_pud_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_pud_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pgd addr alloc res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_pud_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pgd)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_pud_spec_low_step s WB ((Vint vmid)::(Vlong pgd)::(Vlong addr)::(Vint alloc)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive walk_pmd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_pmd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pud addr alloc res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_pmd_spec_low_step s WB ((Vint vmid)::(Vlong pud)::(Vlong addr)::(Vint alloc)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive walk_pte_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_pte_spec_low_intro s (WB: _ -> Prop) m'0 labd vmid pmd addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      walk_pte_spec_low_step s WB ((Vint vmid)::(Vlong pmd)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive set_pmd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_pmd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pud addr pmd
      (Hinv: high_level_invariant labd)
      (Hspec: set_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pmd)) labd = Some labd'):
      set_pmd_spec_low_step s WB ((Vint vmid)::(Vlong pud)::(Vlong addr)::(Vlong pmd)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive set_pte_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_pte_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pmd addr pte
      (Hinv: high_level_invariant labd)
      (Hspec: set_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      set_pte_spec_low_step s WB ((Vint vmid)::(Vlong pmd)::(Vlong addr)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition walk_pgd_spec_low: compatsem LDATAOps :=
      csem walk_pgd_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint32::nil)) Tint64.

    Definition walk_pud_spec_low: compatsem LDATAOps :=
      csem walk_pud_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint32::nil)) Tint64.

    Definition walk_pmd_spec_low: compatsem LDATAOps :=
      csem walk_pmd_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint32::nil)) Tint64.

    Definition walk_pte_spec_low: compatsem LDATAOps :=
      csem walk_pte_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tint64.

    Definition set_pmd_spec_low: compatsem LDATAOps :=
      csem set_pmd_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint64::nil)) Tvoid.

    Definition set_pte_spec_low: compatsem LDATAOps :=
      csem set_pte_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End PTWalkSpecLow.

```
