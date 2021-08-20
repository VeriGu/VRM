# AbstractMachineSpec

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

Require Import RData.
Require Import HypsecCommLib.
Require Import Constants.
Require Import CalLock.

Local Open Scope Z_scope.

Section AbstractMachineSpec.

  Definition acquire_shared_spec (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), ZMap.get lk adt.(lock), adt.(bars) with
    | l, LockOwn false, BarrierValid =>
        let l' := TEVENT adt.(curid) (TSHARED (OPULL lk)) :: l in
        match H_CalLock l', CalState lk l' adt.(shared) with
        | Some _, sdt' => Some adt {log: ZMap.set lk (l') adt.(log)}
                                        {lock: ZMap.set lk (LockOwn true) adt.(lock)}
                                        {tstate: 0}
                                        {shared: sdt'}
        | _, _ => None
        end
    | _, _, _ => None
    end
  .

  (* NOTE: helper spec
   * we need to specialize these per-locked resource, for gensem
   *)
  Definition release_shared_spec (e: SharedMemEvent) (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), ZMap.get lk adt.(lock), adt.(bars) with
    | l, LockOwn true, BarrierValid =>
        let l' := TEVENT adt.(curid) (TSHARED e) :: l in
        match H_CalLock l' with
        | Some _ => Some adt {log: ZMap.set lk (l') adt.(log)}
                             {lock: ZMap.set lk (LockOwn false) adt.(lock)}
                             {tstate: 1}
        | _ => None
        end
    | _, _, _ => None
    end
  .

  Definition release_shared_pt_spec (vmid: Z) (adt: RData) : option RData :=
    let e := ONPT (ZMap.get vmid adt.(shared).(npts)) in
    release_shared_spec e (lock_idx_pt vmid) adt.

  Definition release_shared_spt_spec (adt: RData) : option RData :=
    let e := OSPT adt.(shared).(spts) in
    release_shared_spec e lock_idx_spt adt.

  Definition release_shared_s2page_spec (adt: RData) : option RData :=
    let e := OS2_PAGE adt.(shared).(s2page) in
    release_shared_spec e lock_idx_s2page adt.

  Definition release_shared_core_spec (adt: RData) : option RData :=
    let e := OCORE_DATA adt.(shared).(core_data) in
    release_shared_spec e lock_idx_core adt.

  Definition release_shared_vm_spec (vmid: Z) (adt: RData) : option RData :=
    let e := OVMINFO (ZMap.get vmid adt.(shared).(vminfos)) in
    release_shared_spec e (lock_idx_vm vmid) adt.

  Definition release_shared_smmu_spec (adt: RData) : option RData :=
    let e := OSMMU adt.(shared).(smmu_vmid) in
    release_shared_spec e lock_idx_smmu adt.

  (* NOTE: specs ported from mcertikos/objects/ObjMultiProcessor.v *)
  (* returns option (updated RData * now value) *)
  Definition get_now_spec (lk: Z) (adt: RData): option (RData * Z) :=
    (* if adt.(shared).(halt) then Some (adt, 0) else *)
    (* if negb adt.(icore) || negb adt.(ihost) then None else *)

    match ZMap.get lk adt.(log), adt.(bars) with
    | l, BarrierValid =>
      let l' := TEVENT adt.(curid) (TTICKET GET_NOW) ::
                (ZMap.get lk adt.(oracle)) adt.(curid) l ++ l in
          match CalTicketLockWraparound l' with
          | None => None
          | Some (_, n, _) =>
            let adt' := adt {log: ZMap.set lk (l') adt.(log)} in
            Some (adt', n)
          end
    | _, _ => None
    end.

  Definition incr_now_spec (lk: Z) (adt: RData): option RData :=
    (* if adt.(shared).(halt) then Some adt else *)
    (* if negb adt.(icore) || negb adt.(ihost) then None else *)

    match ZMap.get lk adt.(log), adt.(bars) with
    | l, Barriered =>
      let l' := TEVENT adt.(curid) (TTICKET INC_NOW) :: l in
      (* No need to query oracle when unlocking *)
      (* (ZMap.get lk adt.(oracle)) adt.(curid) l ++ *)
      Some adt {log: ZMap.set lk (l') adt.(log)}
               {bars: BarrierValid}
    | _, _ => None
    end.

  Definition barrier_spec (adt: RData): option RData :=
    match adt.(bars) with
    | BarrierValid => Some adt {bars: Barriered}
    | BarrierNeeded => Some adt {bars: BarrierValid}
    | Barriered => None
    end.

  Definition log_hold_spec (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), adt.(bars) with
    | l, BarrierValid =>
      let l' := TEVENT adt.(curid) (TTICKET HOLD_LOCK) :: l in
      Some adt {log: ZMap.set lk (l') adt.(log)} {bars: BarrierNeeded}
    | _, _ => None
    end.

  Definition incr_ticket_spec (bound lk: Z) (adt: RData): option (RData * Z) :=
    (* if adt.(shared).(halt) then Some (adt, 0) else *)
    (* if negb adt.(icore) || negb adt.(ihost) then None else *)

    match ZMap.get lk adt.(log), adt.(bars) with
    | l, BarrierValid =>
      let p  := Z.to_nat bound in
      let l' := (ZMap.get lk adt.(oracle)) adt.(curid) l ++ l in
      (* NOTE: we only CalTicketLockWraparound on the log with the query,
        *       but not with the new INC_TICKET event
        *)
      match CalTicketLockWraparound l' with
      | None => None
      | Some (t, _, _) =>
          let l''  := TEVENT adt.(curid) (TTICKET (INC_TICKET p)) :: l' in
          let adt' := adt {log: ZMap.set lk (l'') adt.(log)} in
          Some (adt', t)
      end
    | _, _ => None
    end.

  Parameter verify_img: Z -> Z64 -> Z.
  Parameter reg_desc: Z -> Z.
  Parameter shared_kvm: Z -> Z.
  Parameter shared_vcpu: Z -> Z -> Z.
  Parameter exception_vector: Z64 -> Z.

  Fixpoint sync_from_doracle (n: nat) (vmid: Z) (pfn: Z) (flatmem': ZMap.t Z) (logn: Z) (doracle': DataOracle) :=
    match n with
    | O => (pfn, flatmem', logn)
    | S n' =>
      match sync_from_doracle n' vmid pfn flatmem' logn doracle' with
      | (pfn', flatmem', logn') =>
        (pfn' + 1, mset flatmem' pfn' (doracle' vmid logn'), logn' + 1)
      end
    end.

  Definition check_spec (n: Z) (adt: RData) : option Z :=
    if halt adt then Some 0
    else Some n.

  Definition check64_spec (n: Z64) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0)
    else Some n.

  Definition fetch_from_doracle_spec (vmid: Z) (pfn: Z64) (pgnum: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match pfn, pgnum with
    | VZ64 pfn, VZ64 pgnum =>
      rely is_vmid vmid; rely is_pfn pfn; rely is_pfn pgnum; rely is_pfn (pfn + pgnum - 1);
      let id := FLATMEM_ID in
      let cpu := curid adt in
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let fmem := CalFlatmem (flatmem (shared adt)) (orac cpu l) in
      let logn := vmid @ (data_log adt) in
      match sync_from_doracle (Z.to_nat pgnum) vmid pfn fmem logn (doracle adt) with
      | (pfn', fmem', logn') =>
        let l' := (TEVENT cpu (TSHARED (OFLATMEM fmem'))) :: (orac cpu l) ++ l in
        Some adt {shared: (shared adt) {flatmem: fmem'}} {log: (log adt) # id == l'}
             {data_log: (data_log adt) # vmid == logn'}
      end
    end.

  Definition panic_spec  (adt: RData) : option RData :=
    Some adt {halt: true}.

  Definition get_shared_kvm_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    Some (VZ64 (shared_kvm vmid)).

  Definition get_shared_vcpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    Some (VZ64 (shared_vcpu vmid vcpuid)).

  Definition verify_image_spec (vmid: Z) (addr: Z64) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_addr addr;
      Some (verify_img vmid (VZ64 addr))
    end.

  Definition get_sys_reg_desc_val_spec (index: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_reg index;
    Some (VZ64 (reg_desc index)).

  Definition get_exception_vector_spec (pstate: Z64) (adt: RData) : option Z64 :=
    Some (VZ64 (exception_vector pstate)).

  Definition get_pgd_next_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pgd_next npt))
    | _ => None
    end.

  Definition get_pgd_next_spec0 (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt), bars adt with
    | LockOwn true, BarrierValid =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pgd_next npt))
    | _, _ => None
    end.

  Definition set_pgd_next_spec (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true  =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pgd_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _ => None
      end
    end.

  Definition set_pgd_next_spec0 (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pgd_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _, _ => None
      end
    end.

  Definition get_pud_next_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pud_next npt))
    | _ => None
    end.

  Definition get_pud_next_spec0 (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt), bars adt with
    | LockOwn true, BarrierValid =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pud_next npt))
    | _, _ => None
    end.

  Definition set_pud_next_spec (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pud_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _ => None
      end
    end.

  Definition set_pud_next_spec0 (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pud_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _, _ => None
      end
    end.

  Definition get_pmd_next_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pmd_next npt))
    | _ => None
    end.

  Definition get_pmd_next_spec0 (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    match ZMap.get id (lock adt), bars adt with
    | LockOwn true, BarrierValid =>
      let npt := vmid @ (npts (shared adt)) in
      Some (VZ64 (pt_pmd_next npt))
    | _, _ => None
    end.

  Definition set_pmd_next_spec (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pmd_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _ => None
      end
    end.

  Definition set_pmd_next_spec0 (vmid: Z) (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      rely is_vmid vmid;
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        let npt' := npt {pt_pmd_next: next'} in
        Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
      | _, _ => None
      end
    end.

  Definition pt_load_spec (vmid: Z) (addr: Z64) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely (pool_start vmid <=? addr); rely (addr <? pool_end vmid);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pool_start vmid <=? addr) && (addr <? pgd_start vmid) then
          Some (VZ64 (addr @ (pt_vttbr_pool npt)))
        else
          if (pgd_start vmid <=? addr) && (addr <? pud_start vmid) then
            Some (VZ64 (addr @ (pt_pgd_pool npt)))
          else
            if (pud_start vmid <=? addr) && (addr <? pmd_start vmid) then
              Some (VZ64 (addr @ (pt_pud_pool npt)))
            else
              Some (VZ64 (addr @ (pt_pmd_pool npt)))
      | _ => None
      end
    end.

  Definition pt_load_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely (pool_start vmid <=? addr); rely (addr <? pool_end vmid);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        if (pool_start vmid <=? addr) && (addr <? pgd_start vmid) then
          Some (VZ64 (addr @ (pt_vttbr_pool npt)))
        else
          if (pgd_start vmid <=? addr) && (addr <? pud_start vmid) then
            Some (VZ64 (addr @ (pt_pgd_pool npt)))
          else
            if (pud_start vmid <=? addr) && (addr <? pmd_start vmid) then
              Some (VZ64 (addr @ (pt_pud_pool npt)))
            else
              Some (VZ64 (addr @ (pt_pmd_pool npt)))
      | _, _ => None
      end
    end.

  Definition pt_store_spec (vmid: Z) (addr: Z64) (value: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match addr, value with
    | VZ64 addr, VZ64 value' =>
      rely is_vmid vmid; rely (pool_start vmid <=? addr); rely (addr <? pool_end vmid);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let npt := vmid @ (npts (shared adt)) in
        if (pool_start vmid <=? addr) && (addr <? pgd_start vmid) then
          let npt' := npt {pt_vttbr_pool: (pt_vttbr_pool npt) # addr == value'} in
          Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
        else
          if (pgd_start vmid <=? addr) && (addr <? pud_start vmid) then
            let npt' := npt {pt_pgd_pool: (pt_pgd_pool npt) # addr == value'} in
            Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
          else
            if (pud_start vmid <=? addr) && (addr <? pmd_start vmid) then
              let npt' := npt {pt_pud_pool: (pt_pud_pool npt) # addr == value'} in
              if (pmd_table value') =? PMD_TYPE_TABLE then
                Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
              else
                if (tstate adt) =? 0 then
                  Some adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
                else
                  None
            else
              let npt' := npt {pt_pmd_pool: (pt_pmd_pool npt) # addr == value'} in
              if (tstate adt) =? 0 then
                Some adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
              else
                None
      | _ => None
      end
    end.

  Definition pt_store_spec0 (vmid: Z) (addr: Z64) (value: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match addr, value with
    | VZ64 addr, VZ64 value' =>
      rely is_vmid vmid; rely (pool_start vmid <=? addr); rely (addr <? pool_end vmid);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        if (pool_start vmid <=? addr) && (addr <? pgd_start vmid) then
          let npt' := npt {pt_vttbr_pool: (pt_vttbr_pool npt) # addr == value'} in
          Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
        else
          if (pgd_start vmid <=? addr) && (addr <? pud_start vmid) then
            let npt' := npt {pt_pgd_pool: (pt_pgd_pool npt) # addr == value'} in
            Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
          else
            if (pud_start vmid <=? addr) && (addr <? pmd_start vmid) then
              let npt' := npt {pt_pud_pool: (pt_pud_pool npt) # addr == value'} in
              if (pmd_table value') =? PMD_TYPE_TABLE then
                Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
              else
                if (tstate adt) =? 0 then
                  Some adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
                else
                  None
            else
              let npt' := npt {pt_pmd_pool: (pt_pmd_pool npt) # addr == value'} in
              if (tstate adt) =? 0 then
                Some adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
              else
                None
      | _, _ => None
      end
    end.

  Definition get_pt_vttbr_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    Some (VZ64 (pt_vttbr vmid)).

  Definition set_pt_vttbr_spec (vmid: Z) (vttbr: Z64) (adt: RData) : option RData :=
    Some adt.

  Definition get_smmu_pgd_next_spec  (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some (VZ64 (spt_pgd_next (spts (shared adt))))
    | _ => None
    end.

  Definition set_smmu_pgd_next_spec (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spts' := (spts (shared adt)) {spt_pgd_next: next'} in
        Some adt {shared: (shared adt) {spts: spts'}}
      | _ => None
      end
    end.

  Definition get_smmu_pmd_next_spec  (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some (VZ64 (spt_pmd_next (spts (shared adt))))
    | _ => None
    end.

  Definition set_smmu_pmd_next_spec (next: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match next with
    | VZ64 next' =>
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spts' := (spts (shared adt)) {spt_pmd_next: next'} in
        Some adt {shared: (shared adt) {spts: spts'}}
      | _ => None
      end
    end.

  Definition get_smmu_cfg_hw_ttbr_spec (cbndx: Z) (index: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_smmu index; rely is_smmu_cfg cbndx;
    Some (VZ64 (SMMU_TTBR index cbndx)).

  Definition smmu_pt_load_spec (addr: Z64) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    match addr with
    | VZ64 addr =>
      rely (SMMU_POOL_START <=? addr); rely (addr <? SMMU_POOL_END);
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        if (SMMU_POOL_START <=? addr) && (addr <? SMMU_PGD_START) then
          Some (VZ64 (addr @ (spt_vttbr_pool (spts (shared adt)))))
        else
          if (SMMU_PGD_START <=? addr) && (addr <? SMMU_PMD_START) then
            Some (VZ64 (addr @ (spt_pgd_pool (spts (shared adt)))))
          else
            Some (VZ64 (addr @ (spt_pmd_pool (spts (shared adt)))))
      | _ => None
      end
    end.

  Definition smmu_pt_store_spec (addr: Z64) (value: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match addr, value with
    | VZ64 addr, VZ64 value' =>
      rely (SMMU_POOL_START <=? addr); rely (addr <? SMMU_POOL_END);
      let id := SPT_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let spt := spts (shared adt) in
        if (SMMU_POOL_START <=? addr) && (addr <? SMMU_PGD_START) then
          let pool' := (spt_vttbr_pool spt) # addr == value' in
          let spt' := spt {spt_vttbr_pool: pool'} in
          Some adt {shared: (shared adt) {spts: spt'}}
        else
          if (SMMU_PGD_START <=? addr) && (addr <? SMMU_PMD_START) then
            let pool' := (spt_pgd_pool spt) # addr == value' in
            let spt' := spt {spt_pgd_pool: pool'} in
            Some adt {shared: (shared adt) {spts: spt'}}
          else
            let pool' := (spt_pmd_pool spt) # addr == value' in
            let spt' := spt {spt_pmd_pool: pool'} in
            if (tstate adt) =? 0 then
              Some adt {tstate: 1} {shared: (shared adt) {spts: spt'}}
            else None
      | _ => None
      end
    end.

  Fixpoint smmu_pt_clear_loop (n: nat) (addr: Z) (spt: SPT) :=
    match n with
    | O => (addr, spt)
    | S n' =>
      match smmu_pt_clear_loop n' addr spt with
      | (addr', spt') =>
        (addr' + 8, spt' {spt_vttbr_pool: (spt_vttbr_pool spt') # addr == 0})
      end
    end.

  Definition smmu_pt_clear_spec (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_smmu index; rely is_smmu_cfg cbndx;
    let id := SPT_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      if (tstate adt) =? 0 then
        let ttbr := SMMU_TTBR index cbndx in
        match smmu_pt_clear_loop (1024%nat) ttbr (spts (shared adt)) with
        | (_, spt') =>
          Some adt {shared: (shared adt) {spts: spt'}}
        end
      else None
    | _ => None
    end.

  Definition get_mem_region_cnt_spec  (adt: RData) : option Z :=
    Some (region_cnt adt).

  Definition get_mem_region_base_spec (index: Z) (adt: RData) : option Z64 :=
    rely is_memblock index;
    let region := index @ (regions adt) in
    Some (VZ64 (mb_base region)).

  Definition get_mem_region_size_spec (index: Z) (adt: RData) : option Z64 :=
    rely is_memblock index;
    let region := index @ (regions adt) in
    Some (VZ64 (mb_size region)).

  Definition get_mem_region_index_spec (index: Z) (adt: RData) : option Z64 :=
    rely is_memblock index;
    let region := index @ (regions adt) in
    Some (VZ64 (mb_index region)).

  Definition get_mem_region_flag_spec (index: Z) (adt: RData) : option Z64 :=
    rely is_memblock index;
    let region := index @ (regions adt) in
    Some (VZ64 (mb_flag region)).

  Definition get_s2_page_vmid_spec (index: Z64) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    match index with
    | VZ64 idx =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        Some (s2_owner (idx @ (s2page (shared adt))))
      | _ => None
      end
    end.

  Definition set_s2_page_vmid_spec (index: Z64) (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match index with
    | VZ64 idx =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let s2p := idx @ (s2page (shared adt)) in
        let s2p' := s2p {s2_owner: vmid} in
        Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # idx == s2p'}}
      | _ => None
      end
    end.

  Definition get_s2_page_count_spec (index: Z64) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    match index with
    | VZ64 idx =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        Some (s2_count (idx @ (s2page (shared adt))))
      | _ => None
      end
    end.

  Definition set_s2_page_count_spec (index: Z64) (count: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match index with
    | VZ64 idx =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let s2p := idx @ (s2page (shared adt)) in
        let s2p' := s2p {s2_count: count} in
        Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # idx == s2p'}}
      | _ => None
      end
    end.

  Definition get_s2_page_gfn_spec (index: Z64) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    match index with
    | VZ64 idx =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        Some (VZ64 (s2_gfn (idx @ (s2page (shared adt)))))
      | _ => None
      end
    end.

  Definition set_s2_page_gfn_spec (index: Z64) (gfn: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match index, gfn with
    | VZ64 idx, VZ64 gfn =>
      rely is_s2page idx;
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let s2p := idx @ (s2page (shared adt)) in
        let s2p' := s2p {s2_gfn: gfn} in
        Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # idx == s2p'}}
      | _ => None
      end
    end.

  Definition get_next_vmid_spec (adt: RData) : option Z :=
    if halt adt then Some 0 else
    let id := CORE_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some (next_vmid (core_data (shared adt)))
    | _ => None
    end.

  Definition set_next_vmid_spec (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    let id := CORE_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some adt {shared: (shared adt) {core_data: (core_data (shared adt)) {next_vmid: vmid}}}
    | _ => None
    end.

  Definition get_next_remap_ptr_spec (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    let id := CORE_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some (VZ64 (next_remap_ptr (core_data (shared adt))))
    | _ => None
    end.

  Definition set_next_remap_ptr_spec (remap: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    let id := CORE_ID in
    match remap with
    | VZ64 remap =>
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        Some adt {shared: (shared adt) {core_data: (core_data (shared adt)) {next_remap_ptr: remap}}}
      | _ => None
      end
    end.

  Definition get_vm_state_spec (vmid: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (vm_state (VS info))
    | _ => None
    end.

  Definition set_vm_state_spec (vmid: Z) (state: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      let info' := info {vm_state: state} in
      Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
    | _ => None
    end.

  Definition get_vcpu_state_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (vcpuid @ (vm_vcpu_state (VS info)))
    | _ => None
    end.

  Definition set_vcpu_state_spec (vmid: Z) (vcpuid: Z) (state: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      let vcpu_state' := (vm_vcpu_state (VS info)) # vcpuid == state in
      let info' := info {vm_vcpu_state: vcpu_state'} in
      Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
    | _ => None
    end.

  Definition get_vm_kvm_spec (vmid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (vm_kvm (VS info)))
    | _ => None
    end.

  Definition set_vm_kvm_spec (vmid: Z) (kvm: Z64) (adt: RData) : option RData :=
    match kvm with
    | VZ64 kvm =>
      if halt adt then Some adt else
      rely is_vmid vmid;
      let id := INFO_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let info' := info {vm_kvm: kvm} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_vcpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (vcpuid @ (vm_vcpu (VS info))))
    | _ => None
    end.

  Definition set_vm_vcpu_spec (vmid: Z) (vcpuid: Z) (vcpu: Z64) (adt: RData) : option RData :=
    match vcpu with
    | VZ64 vcpu =>
      if halt adt then Some adt else
      rely is_vmid vmid; rely is_vcpu vcpuid;
      let id := INFO_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let vcpu' := (vm_vcpu (VS info)) # vcpuid == vcpu in
        let info' := info {vm_vcpu: vcpu'} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_next_load_idx_spec (vmid: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (vm_next_load_info (VB info))
    | _ => None
    end.

  Definition set_vm_next_load_idx_spec (vmid: Z) (load_idx: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      let info' := info {vm_next_load_info: load_idx} in
      Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
    | _ => None
    end.

  Definition get_vm_load_addr_spec (vmid: Z) (load_idx: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_load_idx load_idx;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (load_idx @ (vm_load_addr (VB info))))
    | _ => None
    end.

  Definition set_vm_load_addr_spec (vmid: Z) (load_idx: Z) (load_addr: Z64) (adt: RData) : option RData :=
    match load_addr with
    | VZ64 load_addr =>
      if halt adt then Some adt else
      rely is_vmid vmid; rely is_load_idx load_idx;
      let id := INFO_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let load' := (vm_load_addr (VB info)) # load_idx == load_addr in
        let info' := info {vm_load_addr: load'} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_load_size_spec (vmid: Z) (load_idx: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_load_idx load_idx;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (load_idx @ (vm_load_size (VB info))))
    | _ => None
    end.

  Definition set_vm_load_size_spec (vmid: Z) (load_idx: Z) (size: Z64) (adt: RData) : option RData :=
    match size with
    | VZ64 size =>
      if halt adt then Some adt else
      let id := INFO_ID + vmid in
      rely is_vmid vmid; rely is_load_idx load_idx;
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let load' := (vm_load_size (VB info)) # load_idx == size in
        let info' := info {vm_load_size: load'} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_remap_addr_spec (vmid: Z) (load_idx: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_load_idx load_idx;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (load_idx @ (vm_remap_addr (VB info))))
    | _ => None
    end.

  Definition set_vm_remap_addr_spec (vmid: Z) (load_idx: Z) (remap_addr: Z64) (adt: RData) : option RData :=
    match remap_addr with
    | VZ64 remap_addr =>
      if halt adt then Some adt else
      rely is_vmid vmid; rely is_load_idx load_idx;
      let id := INFO_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let load' := (vm_remap_addr (VB info)) # load_idx == remap_addr in
        let info' := info {vm_remap_addr: load'} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_mapped_pages_spec (vmid: Z) (load_idx: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_load_idx load_idx;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (VZ64 (load_idx @ (vm_mapped_pages (VB info))))
    | _ => None
    end.

  Definition set_vm_mapped_pages_spec (vmid: Z) (load_idx: Z) (mapped: Z64) (adt: RData) : option RData :=
    match mapped with
    | VZ64 mapped =>
      if halt adt then Some adt else
      rely is_vmid vmid; rely is_load_idx load_idx;
      let id := INFO_ID + vmid in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let info := vmid @ (vminfos (shared adt)) in
        let load' := (vm_mapped_pages (VB info)) # load_idx == mapped in
        let info' := info {vm_mapped_pages: load'} in
        Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
      | _ => None
      end
    end.

  Definition get_vm_inc_exe_spec (vmid: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      Some (vm_inc_exe (VB info))
    | _ => None
    end.

  Definition set_vm_inc_exe_spec (vmid: Z) (inc_exe: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let info := vmid @ (vminfos (shared adt)) in
      let info' := info {vm_next_load_info: inc_exe} in
      Some adt {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
    | _ => None
    end.

  Definition get_shadow_ctxt_specx index cregs cstates :=
    if index =? X0 then (x0 cregs) else
    if index =? X1 then (x1 cregs) else
    if index =? X2 then (x2 cregs) else
    if index =? X3 then (x3 cregs) else
    if index =? X4 then (x4 cregs) else
    if index =? X5 then (x5 cregs) else
    if index =? X6 then (x6 cregs) else
    if index =? X7 then (x7 cregs) else
    if index =? X8 then (x8 cregs) else
    if index =? X9 then (x9 cregs) else
    if index =? X10 then (x10 cregs) else
    if index =? X11 then (x11 cregs) else
    if index =? X12 then (x12 cregs) else
    if index =? X13 then (x13 cregs) else
    if index =? X14 then (x14 cregs) else
    if index =? X15 then (x15 cregs) else
    if index =? X16 then (x16 cregs) else
    if index =? X17 then (x17 cregs) else
    if index =? X18 then (x18 cregs) else
    if index =? X19 then (x19 cregs) else
    if index =? X20 then (x20 cregs) else
    if index =? X21 then (x21 cregs) else
    if index =? X22 then (x22 cregs) else
    if index =? X23 then (x23 cregs) else
    if index =? X24 then (x24 cregs) else
    if index =? X25 then (x25 cregs) else
    if index =? X26 then (x26 cregs) else
    if index =? X27 then (x27 cregs) else
    if index =? X28 then (x28 cregs) else
    if index =? X29 then (x29 cregs) else
    if index =? X30 then (x30 cregs) else
    if index =? PC then (pc cstates) else
    if index =? PSTATE then (pstate cstates) else
    if index =? ELR_EL1 then (elr_el1 cregs) else
    if index =? SPSR_EL1 then (spsr_el1 cregs) else
    if index =? FAR_EL2 then (far_el2 cregs) else
    if index =? HPFAR_EL2 then (hpfar_el2 cregs) else
    if index =? HCR_EL2 then (hcr_el2 cregs) else
    if index =? EC then (ec cregs) else
    if index =? DIRTY then (dirty cstates) else
    if index =? FLAGS then (flags cstates) else
    if index =? MPIDR_EL1 then (mpidr_el1 cregs) else
    if index =? CSSELR_EL1 then (csselr_el1 cregs) else
    if index =? SCTLR_EL1 then (sctlr_el1 cregs) else
    if index =? ACTLR_EL1 then (actlr_el1 cregs) else
    if index =? CPACR_EL1 then (cpacr_el1 cregs) else
    if index =? TTBR0_EL1 then (ttbr0_el1 cregs) else
    if index =? TTBR1_EL1 then (ttbr1_el1 cregs) else
    if index =? TCR_EL1 then (tcr_el1 cregs) else
    if index =? ESR_EL1 then (esr_el1 cstates) else
    if index =? AFSR0_EL1 then (afsr0_el1 cregs) else
    if index =? AFSR1_EL1 then (afsr1_el1 cregs) else
    if index =? FAR_EL1 then (far_el1 cregs) else
    if index =? MAIR_EL1 then (mair_el1 cregs) else
    if index =? VBAR_EL1 then (vbar_el1 cregs) else
    if index =? CONTEXTIDR_EL1 then (contextidr_el1 cregs) else
    if index =? TPIDR_EL0 then (tpidr_el0 cregs) else
    if index =? TPIDRRO_EL0 then (tpidrro_el0 cregs) else
    if index =? TPIDR_EL1 then (tpidr_el1 cregs) else
    if index =? AMAIR_EL1 then (amair_el1 cregs) else
    if index =? CNTKCTL_EL1 then (cntkctl_el1 cregs) else
    if index =? PAR_EL1 then (par_el1 cregs) else
    if index =? MDSCR_EL1 then (mdscr_el1 cregs) else
    if index =? MDCCINT_EL1 then 0 else
    if index =? ELR_EL2 then (elr_el2 cregs) else
    if index =? SPSR_0 then (spsr_0 cstates) else
    if index =? ESR_EL2 then (esr_el2 cregs) else
    0.

  Definition get_shadow_ctxt_spec (vmid: Z) (vcpuid: Z) (index: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
    let res := get_shadow_ctxt_specx index (ctxt_regs ctxt) (ctxt_states ctxt) in
    Some (VZ64 res).

  Definition set_shadow_ctxt_specx index val cregs cstates :=
    if index =? X0 then (cregs {x0: val}, cstates) else
    if index =? X1 then (cregs {x1: val}, cstates) else
    if index =? X2 then (cregs {x2: val}, cstates) else
    if index =? X3 then (cregs {x3: val}, cstates) else
    if index =? X4 then (cregs {x4: val}, cstates) else
    if index =? X5 then (cregs {x5: val}, cstates) else
    if index =? X6 then (cregs {x6: val}, cstates) else
    if index =? X7 then (cregs {x7: val}, cstates) else
    if index =? X8 then (cregs {x8: val}, cstates) else
    if index =? X9 then (cregs {x9: val}, cstates) else
    if index =? X10 then (cregs {x10: val}, cstates) else
    if index =? X11 then (cregs {x11: val}, cstates) else
    if index =? X12 then (cregs {x12: val}, cstates) else
    if index =? X13 then (cregs {x13: val}, cstates) else
    if index =? X14 then (cregs {x14: val}, cstates) else
    if index =? X15 then (cregs {x15: val}, cstates) else
    if index =? X16 then (cregs {x16: val}, cstates) else
    if index =? X17 then (cregs {x17: val}, cstates) else
    if index =? X18 then (cregs {x18: val}, cstates) else
    if index =? X19 then (cregs {x19: val}, cstates) else
    if index =? X20 then (cregs {x20: val}, cstates) else
    if index =? X21 then (cregs {x21: val}, cstates) else
    if index =? X22 then (cregs {x22: val}, cstates) else
    if index =? X23 then (cregs {x23: val}, cstates) else
    if index =? X24 then (cregs {x24: val}, cstates) else
    if index =? X25 then (cregs {x25: val}, cstates) else
    if index =? X26 then (cregs {x26: val}, cstates) else
    if index =? X27 then (cregs {x27: val}, cstates) else
    if index =? X28 then (cregs {x28: val}, cstates) else
    if index =? X29 then (cregs {x29: val}, cstates) else
    if index =? X30 then (cregs {x30: val}, cstates) else
    if index =? PC then (cregs, cstates {pc: val}) else
    if index =? PSTATE then (cregs, cstates {pstate: val}) else
    if index =? ELR_EL1 then (cregs {elr_el1: val}, cstates) else
    if index =? SPSR_EL1 then (cregs {spsr_el1: val}, cstates) else
    if index =? FAR_EL2 then (cregs {far_el2: val}, cstates) else
    if index =? HPFAR_EL2 then (cregs {hpfar_el2: val}, cstates) else
    if index =? HCR_EL2 then (cregs {hcr_el2: val}, cstates) else
    if index =? EC then (cregs {ec: val}, cstates) else
    if index =? DIRTY then (cregs, cstates {dirty: val}) else
    if index =? FLAGS then (cregs, cstates {flags: val}) else
    if index =? MPIDR_EL1 then (cregs {mpidr_el1: val}, cstates) else
    if index =? CSSELR_EL1 then (cregs {csselr_el1: val}, cstates) else
    if index =? SCTLR_EL1 then (cregs {sctlr_el1: val}, cstates) else
    if index =? ACTLR_EL1 then (cregs {actlr_el1: val}, cstates) else
    if index =? CPACR_EL1 then (cregs {cpacr_el1: val}, cstates) else
    if index =? TTBR0_EL1 then (cregs {ttbr0_el1: val}, cstates) else
    if index =? TTBR1_EL1 then (cregs {ttbr1_el1: val}, cstates) else
    if index =? TCR_EL1 then (cregs {tcr_el1: val}, cstates) else
    if index =? ESR_EL1 then (cregs, cstates {esr_el1: val}) else
    if index =? AFSR0_EL1 then (cregs {afsr0_el1: val}, cstates) else
    if index =? AFSR1_EL1 then (cregs {afsr1_el1: val}, cstates) else
    if index =? FAR_EL1 then (cregs {far_el1: val}, cstates) else
    if index =? MAIR_EL1 then (cregs {mair_el1: val}, cstates) else
    if index =? VBAR_EL1 then (cregs {vbar_el1: val}, cstates) else
    if index =? CONTEXTIDR_EL1 then (cregs {contextidr_el1: val}, cstates) else
    if index =? TPIDR_EL0 then (cregs {tpidr_el0: val}, cstates) else
    if index =? TPIDRRO_EL0 then (cregs {tpidrro_el0: val}, cstates) else
    if index =? TPIDR_EL1 then (cregs {tpidr_el1: val}, cstates) else
    if index =? AMAIR_EL1 then (cregs {amair_el1: val}, cstates) else
    if index =? CNTKCTL_EL1 then (cregs {cntkctl_el1: val}, cstates) else
    if index =? PAR_EL1 then (cregs {par_el1: val}, cstates) else
    if index =? MDSCR_EL1 then (cregs {mdscr_el1: val}, cstates) else
    if index =? MDCCINT_EL1 then (cregs, cstates) else
    if index =? ELR_EL2 then (cregs {elr_el2: val}, cstates) else
    if index =? SPSR_0 then (cregs, cstates {spsr_0: val}) else
    if index =? ESR_EL2 then (cregs {esr_el2: val}, cstates) else
    (cregs, cstates).

  Definition set_shadow_ctxt_spec (vmid: Z) (vcpuid: Z) (index: Z) (value: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    match value with
    | VZ64 val =>
      let ctxtid := ctxt_id vmid vcpuid in
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      let cregs := ctxt_regs ctxt in
      let cstates := ctxt_states ctxt in
      match set_shadow_ctxt_specx index val cregs cstates with
      | (cregs', cstates') =>
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ((ctxtid @ (shadow_ctxts adt)) {ctxt_regs: cregs'} {ctxt_states: cstates'})}
      end
    end.

  Definition get_shadow_esr_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    Some (VZ64 (esr_el2 (ctxt_regs ctxt))).

  Definition get_int_esr_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (data_log adt) in
    let val := (doracle adt) vmid n in
    Some (adt {data_log: (data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_int_gpr_spec (vmid: Z) (vcpuid: Z) (index: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (data_log adt) in
    let val := (doracle adt) vmid n in
    Some (adt {data_log: (data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_int_pc_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (data_log adt) in
    let val := (doracle adt) vmid n in
    Some (adt {data_log: (data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_int_pstate_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (data_log adt) in
    let val := (doracle adt) vmid n in
    Some (adt {data_log: (data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition set_int_gpr_spec (vmid: Z) (vcpuid: Z) (index: Z) (value: Z64) (adt: RData) : option RData :=
    Some adt.

  Definition clear_shadow_gp_regs_specx (gp: CtxtRegs) :=
    gp {x0: 0} {x1: 0} {x2: 0} {x3: 0} {x4: 0} {x5: 0} {x6: 0} {x7: 0}
        {x8: 0} {x9: 0} {x10: 0} {x11: 0} {x12: 0} {x13: 0} {x14: 0} {x15: 0}
        {x16: 0} {x17: 0} {x18: 0} {x19: 0} {x20: 0} {x21: 0} {x22: 0} {x23: 0}
        {x24: 0} {x25: 0} {x26: 0} {x27: 0} {x28: 0} {x29: 0} {x30: 0}.

  Definition clear_shadow_gp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let ctxt' := ctxt {ctxt_regs: clear_shadow_gp_regs_specx (ctxt_regs ctxt)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition reset_fp_regs_specx (gp: CtxtRegs) :=
    gp {fp_q0: 0} {fp_q1: 0} {fp_q2: 0} {fp_q3: 0} {fp_q4: 0} {fp_q5: 0} {fp_q6: 0} {fp_q7: 0}
       {fp_q8: 0} {fp_q9: 0} {fp_q10: 0} {fp_q11: 0} {fp_q12: 0} {fp_q13: 0} {fp_q14: 0} {fp_q15: 0}
       {fp_q16: 0} {fp_q17: 0} {fp_q18: 0} {fp_q19: 0} {fp_q20: 0} {fp_q21: 0} {fp_q22: 0} {fp_q23: 0}
       {fp_q24: 0} {fp_q25: 0} {fp_q26: 0} {fp_q27: 0} {fp_q28: 0} {fp_q29: 0} {fp_q30: 0}
       {fp_q31: 0} {fp_fpsr: 0} {fp_fpcr: 0}.

  Definition reset_fp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let ctxt' := ctxt {ctxt_regs: reset_fp_regs_specx (ctxt_regs ctxt)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition get_shadow_dirty_bit_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    Some (VZ64 (dirty (ctxt_states ctxt))).

  Definition set_shadow_dirty_bit_spec (vmid: Z) (vcpuid: Z) (value: Z64) (adt: RData) : option RData :=
    match value with
    | VZ64 val =>
      if halt adt then Some adt else
      rely is_vmid vmid; rely is_vcpu vcpuid;
      let ctxtid := ctxt_id vmid vcpuid in
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_states: (ctxt_states ctxt) {dirty: val}})}
    end.

  Definition get_vm_fault_addr_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (core_data_log adt) in
    let val := (core_doracle adt) vmid n in
    Some (adt {core_data_log: (core_data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_int_new_pte_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (core_data_log adt) in
    let val := (core_doracle adt) vmid n in
    Some (adt {core_data_log: (core_data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_int_new_level_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let n := vmid @ (core_data_log adt) in
    let val := (core_doracle adt) vmid n in
    Some (adt {core_data_log: (core_data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition get_cur_vmid_spec  (adt: RData) : option Z :=
    if halt adt then Some 0
    else Some (cur_vmid adt).

  Definition get_cur_vcpuid_spec  (adt: RData) : option Z :=
    if halt adt then Some 0
    else Some (cur_vcpuid adt).

  Definition clear_phys_page_spec (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      if halt adt then Some adt else
      rely is_pfn pfn;
      let id := FLATMEM_ID in
      let cpu := curid adt in
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let fmem := CalFlatmem (flatmem (shared adt)) (orac cpu l) in
      let fmem' := fmem # pfn == 0 in
      let shared' := (shared adt) {flatmem: fmem'} in
      let l' := (TEVENT cpu (TSHARED (OFLATMEM fmem'))) :: (orac cpu l) ++ l in
      Some adt {tstate: 1} {shared: shared'} {log: (log adt) # id == l'}
    end.

  Definition set_per_cpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    if vmid =? HOSTVISOR then
      Some adt {cur_vmid: HOSTVISOR} {cur_vcpuid: curid adt}
    else if vmid =? COREVISOR then
           Some adt {cur_vmid: COREVISOR} {cur_vcpuid: curid adt}
         else Some adt {cur_vmid: vmid} {cur_vcpuid: vcpuid}.

  Definition encrypt_gp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    Some adt.

  Definition encrypt_sys_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    Some adt.

  Parameter decrypt_gp_regs_specx : CtxtRegs -> CtxtStates -> (Z -> Z) -> Z -> ((CtxtRegs * CtxtStates) * Z).

  Definition decrypt_gp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let dorc := (doracle adt) vmid in
    let logn := vmid @ (data_log adt) in
    match decrypt_gp_regs_specx (ctxt_regs ctxt) (ctxt_states ctxt) dorc logn with
    | (cregs', cstates', logn') =>
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'})} {data_log: (data_log adt) # vmid == logn'}
    end.

  Parameter decrypt_sys_regs_specx : CtxtRegs -> CtxtStates -> (Z -> Z) -> Z -> ((CtxtRegs * CtxtStates) * Z).

  Definition decrypt_sys_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let dorc := (doracle adt) vmid in
    let logn := vmid @ (data_log adt) in
    match decrypt_sys_regs_specx (ctxt_regs ctxt) (ctxt_states ctxt) dorc logn with
    | (cregs', cstates', logn') =>
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'})} {data_log: (data_log adt) # vmid == logn'}
    end.

  Definition get_int_run_vcpuid_spec (vmid: Z) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    rely is_vmid vmid;
    let n := vmid @ (core_data_log adt) in
    let val := (core_doracle adt) vmid n in
    Some (adt {core_data_log: (core_data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition host_to_core_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
    gp {x0: (x0 rgp)} {x1: (x1 rgp)} {x2: (x2 rgp)} {x3: (x3 rgp)}
       {x4: (x4 rgp)} {x5: (x5 rgp)} {x6: (x6 rgp)} {x7: (x7 rgp)}
       {x8: (x8 rgp)} {x9: (x9 rgp)} {x10: (x10 rgp)} {x11: (x11 rgp)}
       {x12: (x12 rgp)} {x13: (x13 rgp)} {x14: (x14 rgp)} {x15: (x15 rgp)}
       {x16: (x16 rgp)} {x17: (x17 rgp)} {x18: (x18 rgp)} {x19: (x19 rgp)}
       {x20: (x20 rgp)} {x21: (x21 rgp)} {x22: (x22 rgp)} {x23: (x23 rgp)}
       {x24: (x24 rgp)} {x25: (x25 rgp)} {x26: (x26 rgp)} {x27: (x27 rgp)}
       {x28: (x28 rgp)} {x29: (x29 rgp)} {x30: (x30 rgp)}.

  Definition host_to_core_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let ctxt' := ctxt {ctxt_regs: host_to_core_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition vm_to_core_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
    gp {x0: (x0 rgp)} {x1: (x1 rgp)} {x2: (x2 rgp)} {x3: (x3 rgp)}
       {x4: (x4 rgp)} {x5: (x5 rgp)} {x6: (x6 rgp)} {x7: (x7 rgp)}
       {x8: (x8 rgp)} {x9: (x9 rgp)} {x10: (x10 rgp)} {x11: (x11 rgp)}
       {x12: (x12 rgp)} {x13: (x13 rgp)} {x14: (x14 rgp)} {x15: (x15 rgp)}
       {x16: (x16 rgp)} {x17: (x17 rgp)} {x18: (x18 rgp)} {x19: (x19 rgp)}
       {x20: (x20 rgp)} {x21: (x21 rgp)} {x22: (x22 rgp)} {x23: (x23 rgp)}
       {x24: (x24 rgp)} {x25: (x25 rgp)} {x26: (x26 rgp)} {x27: (x27 rgp)}
       {x28: (x28 rgp)} {x29: (x29 rgp)} {x30: (x30 rgp)}.

  Definition vm_to_core_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let ctxt' := ctxt {ctxt_regs: vm_to_core_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition core_to_host_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
    rgp {x0: (x0 gp)} {x1: (x1 gp)} {x2: (x2 gp)} {x3: (x3 gp)}
        {x4: (x4 gp)} {x5: (x5 gp)} {x6: (x6 gp)} {x7: (x7 gp)}
        {x8: (x8 gp)} {x9: (x9 gp)} {x10: (x10 gp)} {x11: (x11 gp)}
        {x12: (x12 gp)} {x13: (x13 gp)} {x14: (x14 gp)} {x15: (x15 gp)}
        {x16: (x16 gp)} {x17: (x17 gp)} {x18: (x18 gp)} {x19: (x19 gp)}
        {x20: (x20 gp)} {x21: (x21 gp)} {x22: (x22 gp)} {x23: (x23 gp)}
        {x24: (x24 gp)} {x25: (x25 gp)} {x26: (x26 gp)} {x27: (x27 gp)}
        {x28: (x28 gp)} {x29: (x29 gp)} {x30: (x30 gp)}.

  Definition core_to_host_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let regc' := regc {ctxt_regs: core_to_host_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {regs: regc'}.

  Definition core_to_vm_specx (gp: CtxtRegs) (rgp: CtxtRegs) :=
    rgp {x0: (x0 gp)} {x1: (x1 gp)} {x2: (x2 gp)} {x3: (x3 gp)}
        {x4: (x4 gp)} {x5: (x5 gp)} {x6: (x6 gp)} {x7: (x7 gp)}
        {x8: (x8 gp)} {x9: (x9 gp)} {x10: (x10 gp)} {x11: (x11 gp)}
        {x12: (x12 gp)} {x13: (x13 gp)} {x14: (x14 gp)} {x15: (x15 gp)}
        {x16: (x16 gp)} {x17: (x17 gp)} {x18: (x18 gp)} {x19: (x19 gp)}
        {x20: (x20 gp)} {x21: (x21 gp)} {x22: (x22 gp)} {x23: (x23 gp)}
        {x24: (x24 gp)} {x25: (x25 gp)} {x26: (x26 gp)} {x27: (x27 gp)}
        {x28: (x28 gp)} {x29: (x29 gp)} {x30: (x30 gp)}.

  Definition core_to_vm_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let regc' := regc {ctxt_regs: core_to_host_specx (ctxt_regs regc) (ctxt_regs ctxt)} in
    Some adt {regs: regc'}.

  Definition exit_populate_fault_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
    gp {esr_el2: esr_el2 rgp} {ec: ec rgp} {far_el2: far_el2 rgp} {hpfar_el2: hpfar_el2 rgp}.

  Definition exit_populate_fault_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let ctxt' := ctxt {ctxt_regs: exit_populate_fault_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition save_sysregs_specx (sys: CtxtRegs) (rsys: CtxtRegs): CtxtRegs :=
    sys {csselr_el1: (csselr_el1 rsys)} {sctlr_el1: (sctlr_el1 rsys)}
        {cpacr_el1: (cpacr_el1 rsys)} {ttbr0_el1: (ttbr0_el1 rsys)}
        {ttbr1_el1: (ttbr1_el1 rsys)} {tcr_el1: (tcr_el1 rsys)}
        {afsr0_el1: (afsr0_el1 rsys)} {afsr1_el1: (afsr1_el1 rsys)}
        {far_el1: (far_el1 rsys)} {mair_el1: (mair_el1 rsys)}
        {vbar_el1: (vbar_el1 rsys)} {contextidr_el1: (contextidr_el1 rsys)}
        {amair_el1: (amair_el1 rsys)} {cntkctl_el1: (cntkctl_el1 rsys)}
        {par_el1: (par_el1 rsys)} {tpidr_el1: (tpidr_el1 rsys)}
        {spsr_el1: (spsr_el1 rsys)} {mdscr_el1: (mdscr_el1 rsys)}
        {sp_el0: (sp_el0 rsys)} {tpidr_el0: (tpidr_el0 rsys)}
        {tpidrro_el0: (tpidrro_el0 rsys)}
        {mpidr_el1: (vmpidr_el2 rsys)} {actlr_el1: (actlr_el1 rsys)}
        {sp_el1: (sp_el1 rsys)} {elr_el1: (elr_el1 rsys)}.

  Definition save_sysregs_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let ctxt' := ctxt {ctxt_regs: save_sysregs_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition restore_sysregs_specx (sys: CtxtRegs) (csts: CtxtStates) (rsys: CtxtRegs) :=
    rsys {csselr_el1: (csselr_el1 sys)} {sctlr_el1: (sctlr_el1 sys)}
         {cpacr_el1: (cpacr_el1 sys)} {ttbr0_el1: (ttbr0_el1 sys)}
         {ttbr1_el1: (ttbr1_el1 sys)} {tcr_el1: (tcr_el1 sys)}
         {afsr0_el1: (afsr0_el1 sys)} {afsr1_el1: (afsr1_el1 sys)}
         {far_el1: (far_el1 sys)} {mair_el1: (mair_el1 sys)}
         {vbar_el1: (vbar_el1 sys)} {contextidr_el1: (contextidr_el1 sys)}
         {amair_el1: (amair_el1 sys)} {cntkctl_el1: (cntkctl_el1 sys)}
         {par_el1: (par_el1 sys)} {tpidr_el1: (tpidr_el1 sys)}
         {spsr_el1: (spsr_el1 sys)} {mdscr_el1: (mdscr_el1 sys)}
         {sp_el0: (sp_el0 sys)} {tpidr_el0: (tpidr_el0 sys)}
         {tpidrro_el0: (tpidrro_el0 sys)} {spsr_el2: (pstate csts)}
         {vmpidr_el2: (mpidr_el1 sys)} {mpidr_el1: (mpidr_el1 sys)}
         {actlr_el1: (actlr_el1 sys)} {sp_el1: (sp_el1 sys)}
         {elr_el2: (pc csts)} {elr_el1: (elr_el1 sys)}
         {esr_el2: (esr_el2 sys)} {ec: (ec sys)}
         {far_el2: (far_el2 sys)} {hpfar_el2: (hpfar_el2 sys)}.

  Definition restore_sysregs_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
    let regc := regs adt in
    Some (adt {regs: regc {ctxt_regs: restore_sysregs_specx (ctxt_regs ctxt) (ctxt_states ctxt) (ctxt_regs regc)}}).

  Definition fpsimd_save_state_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
    gp {fp_q0: (fp_q0 rgp)} {fp_q1: (fp_q1 rgp)} {fp_q2: (fp_q2 rgp)}
       {fp_q3: (fp_q3 rgp)} {fp_q4: (fp_q4 rgp)} {fp_q5: (fp_q5 rgp)}
       {fp_q6: (fp_q6 rgp)} {fp_q7: (fp_q7 rgp)} {fp_q8: (fp_q8 rgp)}
       {fp_q9: (fp_q9 rgp)} {fp_q10: (fp_q10 rgp)} {fp_q11: (fp_q11 rgp)}
       {fp_q12: (fp_q12 rgp)} {fp_q13: (fp_q13 rgp)} {fp_q14: (fp_q14 rgp)}
       {fp_q15: (fp_q15 rgp)} {fp_q16: (fp_q16 rgp)} {fp_q17: (fp_q17 rgp)}
       {fp_q18: (fp_q18 rgp)} {fp_q19: (fp_q19 rgp)} {fp_q20: (fp_q20 rgp)}
       {fp_q21: (fp_q21 rgp)} {fp_q22: (fp_q22 rgp)} {fp_q23: (fp_q23 rgp)}
       {fp_q24: (fp_q24 rgp)} {fp_q25: (fp_q25 rgp)} {fp_q26: (fp_q26 rgp)}
       {fp_q27: (fp_q27 rgp)} {fp_q28: (fp_q28 rgp)} {fp_q29: (fp_q29 rgp)}
       {fp_q30: (fp_q30 rgp)} {fp_q31: (fp_q31 rgp)} {fp_fpsr: (fp_fpsr rgp)}
       {fp_fpcr: (fp_fpcr rgp)}.

  Definition fpsimd_save_state_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let regc := regs adt in
    let ctxt' := ctxt {ctxt_regs: fpsimd_save_state_specx (ctxt_regs ctxt) (ctxt_regs regc)} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition fpsimd_restore_state_specx (gp: CtxtRegs) (rgp: CtxtRegs) :=
    rgp {fp_q0: (fp_q0 gp)} {fp_q1: (fp_q1 gp)} {fp_q2: (fp_q2 gp)}
        {fp_q3: (fp_q3 gp)} {fp_q4: (fp_q4 gp)} {fp_q5: (fp_q5 gp)}
        {fp_q6: (fp_q6 gp)} {fp_q7: (fp_q7 gp)} {fp_q8: (fp_q8 gp)}
        {fp_q9: (fp_q9 gp)} {fp_q10: (fp_q10 gp)} {fp_q11: (fp_q11 gp)}
        {fp_q12: (fp_q12 gp)} {fp_q13: (fp_q13 gp)} {fp_q14: (fp_q14 gp)}
        {fp_q15: (fp_q15 gp)} {fp_q16: (fp_q16 gp)} {fp_q17: (fp_q17 gp)}
        {fp_q18: (fp_q18 gp)} {fp_q19: (fp_q19 gp)} {fp_q20: (fp_q20 gp)}
        {fp_q21: (fp_q21 gp)} {fp_q22: (fp_q22 gp)} {fp_q23: (fp_q23 gp)}
        {fp_q24: (fp_q24 gp)} {fp_q25: (fp_q25 gp)} {fp_q26: (fp_q26 gp)}
        {fp_q27: (fp_q27 gp)} {fp_q28: (fp_q28 gp)} {fp_q29: (fp_q29 gp)}
        {fp_q30: (fp_q30 gp)} {fp_q31: (fp_q31 gp)} {fp_fpsr: (fp_fpsr gp)}
        {fp_fpcr: (fp_fpcr gp)}.

  Definition fpsimd_restore_state_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
    let regc := regs adt in
    Some (adt {regs: regc {ctxt_regs: fpsimd_restore_state_specx (ctxt_regs ctxt) (ctxt_regs regc)}}).

  Definition activate_traps_specx (regt: TrapRegs) :=
    regt {pmuselr_el0: 0} {pmuserenr_el0: ARMV8_PMU_USERENR_MASK} {mdcr_el2: HYPSEC_MDCR_EL2_FLAG} {cptr_el2: CPTR_VM}.

  Definition activate_traps_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    Some (adt {regs: (regs adt) {trap_regs: activate_traps_specx (trap_regs (regs adt))}}).

  Definition deactivate_traps_specx (regt: TrapRegs) :=
    regt {pmuserenr_el0: 0} {mdcr_el2: 0} {cptr_el2: CPTR_EL2_DEFAULT }.

  Definition deactivate_traps_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    Some (adt {regs: (regs adt) {trap_regs: deactivate_traps_specx (trap_regs (regs adt))}}).

  Definition timer_enable_traps_specx (regt: TrapRegs) :=
    let v' := (cnthctl_el2 regt) - CNTHCTL_EL1PCEN + CNTHCTL_EL1PCTEN in
    regt {cnthctl_el2: v'}.

  Definition timer_enable_traps_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    Some (adt {regs: (regs adt) {trap_regs: timer_enable_traps_specx (trap_regs (regs adt))}}).

  Definition core_handle_sys64_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let pc := (elr_el2 (ctxt_regs (regs adt))) in
    Some (adt {regs: (regs adt) {ctxt_regs: (ctxt_regs (regs adt)) {esr_el2: pc + 4}}}).

  Definition timer_set_cntvoff_spec  (adt: RData) : option RData :=
    Some adt.

  Definition vm_el2_restore_state_specx (regc: CtxtRegs) (ctxt: CtxtRegs) vttbr :=
    regc {vttbr_el2: vttbr} {tpidr_el2: tpidr_el2 ctxt} {hcr_el2: HCR_HYPSEC_VM_FLAGS}.

  Definition vm_el2_restore_state_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
    let vttbr := pt_vttbr vmid in
    Some (adt {regs: (regs adt) {ctxt_regs: vm_el2_restore_state_specx (ctxt_regs (regs adt)) (ctxt_regs ctxt) vttbr}}).

  Definition host_el2_restore_state_specx (regc: CtxtRegs) vttbr :=
    regc {vttbr_el2: vttbr} {hcr_el2: HCR_HOST_NVHE_FLAGS} {tpidr_el2: 0}.

  Definition host_el2_restore_state_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vttbr := pt_vttbr HOSTVISOR in
    Some (adt {regs: (regs adt) {ctxt_regs:  host_el2_restore_state_specx (ctxt_regs (regs adt)) vttbr}}).

  Definition get_smmu_cfg_vmid_spec (cbndx: Z) (index: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_smmu index; rely is_smmu_cfg cbndx;
    let id := SMMU_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some ((smmu_id index cbndx) @ (smmu_vmid (shared adt)))
    | _ => None
    end.

  Definition set_smmu_cfg_vmid_spec (cbndx: Z) (index: Z) (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_smmu index; rely is_smmu_cfg cbndx;
    let id := SMMU_ID in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      Some (adt {shared: (shared adt) {smmu_vmid: (smmu_vmid (shared adt)) # (smmu_id index cbndx) == vmid}})
    | _ => None
    end.

  Definition get_smmu_num_context_banks_spec (index: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_smmu index;
    Some (index @ (smmu_dev_context_banks (smmu_conf adt))).

  Definition get_smmu_pgshift_spec (index: Z) (adt: RData) : option Z :=
    if halt adt then Some 0 else
    rely is_smmu index;
    Some (index @ (smmu_pgshift (smmu_conf adt))).

  Definition get_smmu_num_spec  (adt: RData) : option Z :=
    if halt adt then Some 0 else
    Some (smmu_num (smmu_conf adt)).

  Definition get_smmu_size_spec (index: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_smmu index;
    Some (VZ64 (index @ (smmu_size (smmu_conf adt)))).

  Definition get_smmu_base_spec (index: Z) (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    rely is_smmu index;
    Some (VZ64 (index @ (smmu_phys_base (smmu_conf adt)))).

  Definition host_dabt_get_rd_spec (hsr: Z) (adt: RData) : option Z :=
    Some (host_dabt_get_rd' hsr).

  Definition host_dabt_is_write_spec (hsr: Z) (adt: RData) : option Z :=
    Some (host_dabt_is_write' hsr).

  Definition host_dabt_get_as_spec (hsr: Z) (adt: RData) : option Z :=
    Some (host_dabt_get_as' hsr).

  Definition mem_load_raw_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

  Definition mem_store_raw_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

  Definition dev_load_raw_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    Some adt.

  Definition dev_store_raw_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    Some adt.

  Definition writel_relaxed_spec (value: Z64) (addr: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else Some adt.

  Definition writeq_relaxed_spec (value: Z64) (addr: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else Some adt.

  Definition readq_relaxed_spec (addr: Z64) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    let n := HOSTVISOR @ (data_log adt) in
    let val := (doracle adt) HOSTVISOR n in
    Some (adt {data_log: (data_log adt) # HOSTVISOR == (n + 1)}, (VZ64 val)).

  Definition readl_relaxed_spec (addr: Z64) (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    let n := HOSTVISOR @ (data_log adt) in
    let val := (doracle adt) HOSTVISOR n in
    Some (adt {data_log: (data_log adt) # HOSTVISOR == (n + 1)}, (VZ64 (Z.land val INVALID))).

  Definition host_skip_instr_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let pc := (elr_el2 (ctxt_regs (regs adt))) in
    Some (adt {regs: (regs adt) {ctxt_regs: (ctxt_regs (regs adt)) {esr_el2: pc + 4}}}).

  Definition host_get_fault_ipa_spec (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      if halt adt then Some (VZ64 0) else
      let far_el2 := (far_el2 (ctxt_regs (regs adt))) in
      let far_el2' := Z.land far_el2 4095 in
      let addr' := Z.lor addr far_el2' in
      Some (VZ64 addr')
    end.

  Definition read_actlr_el1_spec (adt: RData) : option (RData * Z64) :=
    if halt adt then Some (adt, VZ64 0) else
    let vmid := cur_vmid adt in
    let n := vmid @ (data_log adt) in
    let val := (doracle adt) vmid n in
    Some (adt {data_log: (data_log adt) # vmid == (n + 1)}, (VZ64 val)).

  Definition read_hpfar_el2_spec (adt: RData) : option Z64 :=
    if halt adt then Some (VZ64 0) else
    Some (VZ64 (hpfar_el2 (ctxt_regs (regs adt)))).

  Definition read_esr_el2_spec (adt: RData) : option Z :=
    if halt adt then Some 0 else
    Some (esr_el2 (ctxt_regs (regs adt))).

  Definition encrypt_mem_buf_spec (vmid: Z) (inbuf: Z64) (outbuf: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match inbuf, outbuf with
    | VZ64 inbuf, VZ64 outbuf =>
      rely is_pfn inbuf; rely is_pfn outbuf;
      let id := FLATMEM_ID in
      let cpu := curid adt in
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let fmem := CalFlatmem (flatmem (shared adt)) (orac cpu l) in
      let logn := HOSTVISOR @ (data_log adt) in
      let fmem' := fmem # outbuf == ((doracle adt) HOSTVISOR logn) in
      let shared' := (shared adt) {flatmem: fmem'} in
      let l' := (TEVENT cpu (TSHARED (OFLATMEM fmem'))) :: (orac cpu l) ++ l in
      Some adt {tstate: 1} {shared: shared'} {log: (log adt) # id == l'} {data_log: (data_log adt) # HOSTVISOR == (logn + 1)}
    end.

  Definition decrypt_mem_buf_spec (vmid: Z) (inbuf: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match inbuf with
    | VZ64 inbuf =>
      rely is_pfn inbuf;
      let id := FLATMEM_ID in
      let cpu := curid adt in
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let fmem := CalFlatmem (flatmem (shared adt)) (orac cpu l) in
      let logn := HOSTVISOR @ (data_log adt) in
      let fmem' := fmem # inbuf == ((doracle adt) HOSTVISOR logn) in
      let shared' := (shared adt) {flatmem: fmem'} in
      let l' := (TEVENT cpu (TSHARED (OFLATMEM fmem'))) :: (orac cpu l) ++ l in
      Some adt {tstate: 1} {shared: shared'} {log: (log adt) # id == l'} {data_log: (data_log adt) # HOSTVISOR == (logn + 1)}
    end.

End AbstractMachineSpec.

```
