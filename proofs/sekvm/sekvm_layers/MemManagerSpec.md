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

Require Import PageManager.Spec.
Require Import NPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import RData.
Require Import PageManager.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioSPTOps.Spec.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.

Local Open Scope Z_scope.

Section MemManagerSpec.

  Definition map_page_host_spec (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely is_paddr addr;
      let pfn := addr / PAGE_SIZE in
      if halt adt then Some adt else
      let cpu := curid adt in
      let ptid := NPT_ID in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt), ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt) with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let pt := CalNPT (HOSTVISOR @ (npts (shared adt))) (pto cpu ptl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page);
          if (s2_owner page =? INVALID) || (s2_owner page =? HOSTVISOR) || (s2_count page >? 0) then
            let pte := (if s2_owner page =? INVALID then Z.lor (pfn * PAGE_SIZE) (Z.lor PAGE_S2_DEVICE S2_RDWR)
                        else Z.lor (pfn * PAGE_SIZE) PAGE_S2_KERNEL) in
            match local_mmap HOSTVISOR addr 3 pte pt with
            | Some (halt', npt') =>
              let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
              Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                   {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'} {s2page: s2p}}
                   {log: ((log adt) # S2PAGE_ID == (if halt' then spl else spl'))
                            # ptid == (if halt' then ptl else ptl')}
                   {lock: ((lock adt) # S2PAGE_ID == (if halt' then LockOwn true else LockFalse))
                             # ptid == (if halt' then LockOwn true else LockFalse)}
            | _ => None
            end
          else
            Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                 {log: (log adt) # S2PAGE_ID == spl} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

  Definition clear_vm_page_spec (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_vmid vmid; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt), FLATMEM_ID @ (log adt), FLATMEM_ID @ (oracle adt) with
      | LockFalse, spl0, spo, fml0, fmo =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let fmem := CalFlatmem (flatmem (shared adt)) (fmo cpu fml0) in
        match H_CalLock ((spo cpu spl0) ++ spl0) with
        | Some (_, LEMPTY, None) =>
          let page := pfn @ s2p in
          rely is_int (s2_owner page);
          if s2_owner page =? vmid then
            let page' := mkS2Page HOSTVISOR 0 (pfn + SMMU_HOST_OFFSET) in
            let s2p' := s2p # pfn == page' in
            let fmem' := fmem # pfn == 0 in
            let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
            let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
            Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p'} {flatmem: fmem'}}
                 {log: ((log adt) # S2PAGE_ID == spl') # FLATMEM_ID == fml'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
          else
            let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
            Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p}}
                 {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
        | _ => None
        end
      | _, _, _, _, _ => None
      end
    end.


  Definition assign_pfn_to_vm_spec (vmid: Z) (gfn: Z64) (pfn: Z64) (adt: RData) : option RData :=
    match gfn, pfn with
    | VZ64 gfn, VZ64 pfn =>
      rely is_vmid vmid; rely is_gfn gfn; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      let ptid := NPT_ID in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt),
            FLATMEM_ID @ (log adt), FLATMEM_ID @ (oracle adt)
      with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let npt := CalNPT (HOSTVISOR @ (npts (shared adt))) (pto cpu ptl0) in
        let fmem := CalFlatmem (flatmem (shared adt)) (fmo cpu fml0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
          if s2_owner page =? HOSTVISOR then
            if s2_count page =? 0 then
              let s2p' := s2p # pfn == (mkS2Page vmid 0 gfn) in
              let logn := vmid @ (data_log adt) in
              let fmem' := fmem # pfn == ((doracle adt) vmid logn) in
              match pfn @ (pt npt) with
              | (_, level, pte) =>
                rely is_int level;
                match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                      else local_mmap HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
                | Some (halt', npt') =>
                  let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                  let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                  Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                       {data_log: if halt' then (data_log adt) else (data_log adt) # vmid == (logn + 1)}
                       {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: if halt' then (flatmem (shared adt)) else fmem'}}
                       {log: if halt' then (((log adt) # S2PAGE_ID == spl) # ptid == ptl)
                             else (((log adt) # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                       {lock: ((lock adt) # S2PAGE_ID == (if halt' then LockOwn true else LockFalse))
                                # ptid == (if halt' then LockOwn true else LockFalse)}
                | _ => None
                end
              end
            else
              Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                  {log: ((log adt) # S2PAGE_ID == spl)} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
          else
            if (s2_owner page =? vmid) && ((s2_gfn page =? INVALID64) || (gfn =? s2_gfn page)) then
              let page' := page {s2_count: if s2_count page =? INVALID then 0 else (s2_count page)} {s2_gfn: gfn} in
              let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE (s2p # pfn == page'))) :: spl in
              Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p # pfn == page'}}
                    {log: ((log adt) # S2PAGE_ID == spl')} {lock: (lock adt) # S2PAGE_ID == LockFalse}
            else
              Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                  {log: ((log adt) # S2PAGE_ID == spl)} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
      | _, _ => None
      end
    | _, _, _, _, _, _, _, _ => None
    end
  end.

  Definition map_pfn_vm_spec (vmid: Z) (addr: Z64) (pte: Z64) (level: Z) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      let id := NPT_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt), id @ (log adt), id @ (oracle adt) with
      | LockFalse, l, orac =>
        let npt := CalNPT (vmid @ (npts (shared adt))) (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l) ++ l in
        match H_CalLock ((orac cpu l) ++ l) with
        | Some (_, LEMPTY, None) =>
          let paddr := phys_page pte in
          let perm := PAGE_S2_KERNEL in
          let pte' := (if level =? 2 then Z.land (Z.lor paddr perm) NOT_PMD_TABLE_BIT else Z.lor paddr perm) in
          let level' := (if level =? 2 then 2 else 3) in
          match local_mmap vmid addr level' pte' npt with
          | Some (halt', npt') =>
            let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: l' in
            Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                 {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
                 {log: (log adt) # id == (if halt' then l' else l'')}
                 {lock: (lock adt) # id == (if halt' then LockOwn true else LockFalse)}
          | _ => None
          end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition map_vm_io_spec (vmid: Z) (gpa: Z64) (pa: Z64) (adt: RData) : option RData :=
    match gpa, pa with
    | VZ64 gpa, VZ64 pa =>
      rely is_vmid vmid; rely is_addr gpa; rely is_addr pa;
      if halt adt then Some adt else
      let cpu := curid adt in
      let ptid := NPT_ID + vmid in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt), ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt) with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let npt := CalNPT (vmid @ (npts (shared adt))) (pto cpu ptl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
          let gfn := gpa / PAGE_SIZE in
          let pfn := pa / PAGE_SIZE in
          let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
          let page := pfn @ s2p in
          rely is_int (s2_owner page);
          if s2_owner page =? INVALID then
            match local_mmap vmid gpa 3 pte npt with
            | Some (halt', npt') =>
              let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
              Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                   {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'} {s2page: s2p}}
                   {log: ((log adt) # S2PAGE_ID == (if halt' then spl else spl'))
                            # ptid == (if halt' then ptl else ptl')}
                   {lock: ((lock adt) # S2PAGE_ID == (if halt' then LockOwn true else LockFalse))
                             # ptid == (if halt' then LockOwn true else LockFalse)}
            | _ => None
            end
          else
            Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p}}
                 {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

  Definition grant_vm_page_spec (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_vmid vmid; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt) with
      | LockFalse, spl0, spo =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0) with
        | Some (_, LEMPTY, None) =>
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page);
          let s2p' := (if (s2_owner page =? vmid) && (s2_count page <? MAX_SHARE_COUNT)
                       then s2p # pfn == (page {s2_count: (s2_count page) + 1})
                       else s2p) in
          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
          Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p'}}
               {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition revoke_vm_page_spec (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_vmid vmid; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      let ptid := NPT_ID in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt),
            FLATMEM_ID @ (log adt), FLATMEM_ID @ (oracle adt)
      with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let npt := CalNPT (HOSTVISOR @ (npts (shared adt))) (pto cpu ptl0) in
        let fmem := CalFlatmem (flatmem (shared adt)) (fmo cpu fml0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page);
          if (s2_owner page =? vmid) && (s2_count page >? 0) then
            let s2p' := s2p # pfn == (page {s2_count: (s2_count page) - 1}) in
            let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
            if s2_count page =? 1 then
              let logn := vmid @ (data_log adt) in
              let fmem' := fmem # pfn == ((doracle adt) vmid logn) in
              match pfn @ (pt npt) with
              | (_, level, pte) =>
                rely is_int level;
                match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                      else local_mmap HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
                | Some (halt', npt') =>
                  let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                  let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                  Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                       {data_log: if halt' then (data_log adt) else (data_log adt) # vmid == (logn + 1)}
                       {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'}
                                             {s2page: s2p'} {flatmem: if halt' then (flatmem (shared adt)) else fmem'}}
                       {log: if halt' then (((log adt) # S2PAGE_ID == spl) # ptid == ptl)
                             else (((log adt) # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                       {lock: ((lock adt) # S2PAGE_ID == (if halt' then LockOwn true else LockFalse))
                                # ptid == (if halt' then LockOwn true else LockFalse)}
                | _ => None
                end
              end
            else
              Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p'}}
                  {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
          else
            let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
            Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p}}
                 {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
        | _, _ => None
        end
      | _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition assign_pfn_to_smmu_spec (vmid: Z) (gfn: Z64) (pfn: Z64) (adt: RData) : option RData :=
    match gfn, pfn with
    | VZ64 gfn, VZ64 pfn =>
      rely is_vmid vmid; rely is_gfn gfn; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      let ptid := NPT_ID in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt),
            FLATMEM_ID @ (log adt), FLATMEM_ID @ (oracle adt)
      with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let npt := CalNPT (HOSTVISOR @ (npts (shared adt))) (pto cpu ptl0) in
        let fmem := CalFlatmem (flatmem (shared adt)) (fmo cpu fml0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
          if s2_owner page =? HOSTVISOR then
            if s2_count page =? 0 then
              let s2p' := s2p # pfn == (mkS2Page vmid INVALID gfn) in
              let logn := vmid @ (data_log adt) in
              let fmem' := fmem # pfn == ((doracle adt) vmid logn) in
              match pfn @ (pt npt) with
              | (_, level, pte) =>
                rely is_int level;
                match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                      else local_mmap HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
                | Some (halt', npt') =>
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                  let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                  let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                  Some adt {halt: halt'} {tstate: if halt' then 0 else 1}
                      {data_log: if halt' then (data_log adt) else (data_log adt) # vmid == (logn + 1)}
                      {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'}
                                            {s2page: if halt' then s2p else s2p'}
                                            {flatmem: if halt' then (flatmem (shared adt)) else fmem'}}
                      {log: if halt' then (((log adt) # S2PAGE_ID == spl) # ptid == ptl)
                            else (((log adt) # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                      {lock: ((lock adt) # S2PAGE_ID == (if halt' then LockOwn true else LockFalse))
                                # ptid == (if halt' then LockOwn true else LockFalse)}
                | _ => None
                end
              end
            else
              Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                  {log: (log adt) # S2PAGE_ID == spl} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
          else
            if s2_owner page =? vmid then
              let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
              Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p}}
                  {log: (log adt) # S2PAGE_ID == spl'} {lock: (lock adt) # S2PAGE_ID == LockFalse}
            else
              Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                  {log: (log adt) # S2PAGE_ID == spl} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
        | _, _ => None
        end
      | _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition update_smmu_page_spec (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    match iova, pte with
    | VZ64 iova, VZ64 pte =>
      rely is_vmid vmid; rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova; rely is_int64 pte;
      if halt adt then Some adt else
      let cpu := curid adt in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            SPT_ID @ (lock adt), SPT_ID @ (log adt), SPT_ID @ (oracle adt) with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let pfn := phys_page pte / PAGE_SIZE in
          let gfn := iova / PAGE_SIZE in
          let page := pfn @ s2p in
          rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
          if (vmid =? s2_owner page) && (gfn =? s2_gfn page) then
            match local_spt_map cbndx index iova pte spt with
            | Some (halt', spt') =>
              if halt' then
                Some adt {halt: halt'} {tstate: 0} {shared: (shared adt) {spts: spt'} {s2page: s2p}}
                    {log: ((log adt) # S2PAGE_ID == spl) # SPT_ID == ptl}
                    {lock: ((lock adt) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
              else
                let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page <? EL2_SMMU_CFG_SIZE)
                              then s2p # pfn == (page {s2_count: (s2_count page) + 1}) else s2p) in
                let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
                let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                Some adt {halt: halt'} {tstate: 1} {shared: (shared adt) {spts: spt'} {s2page: s2p'}}
                    {log: ((log adt) # S2PAGE_ID == spl') # SPT_ID == ptl'}
                    {lock: ((lock adt) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
            | _ => None
            end
          else
            Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p}}
                {log: (log adt) # S2PAGE_ID == spl} {lock: (lock adt) # S2PAGE_ID == (LockOwn true)}
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

  Definition unmap_smmu_page_spec (cbndx: Z) (index: Z) (iova: Z64) (adt: RData) : option RData :=
    match iova with
    | VZ64 iova =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova;
      if halt adt then Some adt else
      let cpu := curid adt in
      match S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            SPT_ID @ (lock adt), SPT_ID @ (log adt), SPT_ID @ (oracle adt) with
      | LockFalse, spl0, spo, LockFalse, ptl0, pto =>
        let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
        let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
        let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
        let ptl := TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
        match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let ttbr := SMMU_TTBR index cbndx in
          let pt := ttbr @ (spt_pt spt) in
          let gfn := iova / PAGE_SIZE in
          let (_, pte) := gfn @ pt in
          rely is_int64 pte;
          match (if pte =? 0 then Some (false, spt) else local_spt_map cbndx index iova 0 spt) with
          | Some (halt', spt') =>
            if halt' then
              Some adt {halt: halt'} {tstate: 0} {shared: (shared adt) {spts: spt'} {s2page: s2p}}
                  {log: ((log adt) # S2PAGE_ID == spl) # SPT_ID == ptl}
                  {lock: ((lock adt) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
            else
              let pfn := phys_page pte / PAGE_SIZE in
              let page := pfn @ s2p in
              rely is_int (s2_owner page); rely is_int (s2_count page);
              let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page >? 0)
                            then s2p # pfn == (page {s2_count: (s2_count page) - 1}) else s2p) in
              let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
              let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
              Some adt {halt: halt'} {tstate: 1} {shared: (shared adt) {spts: spt'} {s2page: s2p'}}
                  {log: ((log adt) # S2PAGE_ID == spl') # SPT_ID == ptl'}
                  {lock: ((lock adt) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
          | _ => None
          end
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

End MemManagerSpec.

Section MemManagerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := PageManager_ops) LDATA).

  Definition map_page_host_spec0 (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely is_addr addr;
      let pfn := addr / PAGE_SIZE in
      when adt0 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt0;
      rely is_int owner;
      when count == get_pfn_count_spec (VZ64 pfn) adt0;
      rely is_int count;
      if owner =? INVALID then
        let perm := Z.lor PAGE_S2_DEVICE S2_RDWR in
        let pte := Z.lor (pfn * PAGE_SIZE) perm in
        when adt1 == map_s2pt_spec HOSTVISOR (VZ64 addr) 3 (VZ64 pte) adt0;
        release_lock_s2page_spec adt1
      else
        if (owner =? HOSTVISOR) || (count >? 0) then
          let perm := PAGE_S2_KERNEL in
          let pte := Z.lor (pfn * PAGE_SIZE) perm in
          when adt1 == map_s2pt_spec HOSTVISOR (VZ64 addr) 3 (VZ64 pte) adt0;
          release_lock_s2page_spec adt1
        else
          when adt1 == panic_spec adt0;
          release_lock_s2page_spec adt1
  end.

  Definition clear_vm_page_spec0 (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_pfn pfn;
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      if owner =? vmid then
        when adt2 == clear_pfn_host_spec (VZ64 pfn) adt1;
        when adt3 == set_pfn_owner_spec (VZ64 pfn) HOSTVISOR adt2;
        when adt4 == set_pfn_count_spec (VZ64 pfn) 0 adt3;
        when adt5 == set_pfn_map_spec (VZ64 pfn) (VZ64 (pfn + SMMU_HOST_OFFSET)) adt4;
        when adt6 == clear_phys_page_spec (VZ64 pfn) adt5;
        release_lock_s2page_spec adt6
      else
        release_lock_s2page_spec adt1
    end.

  Definition assign_pfn_to_vm_spec0 (vmid: Z) (gfn: Z64) (pfn: Z64) (adt: RData) : option RData :=
    match gfn, pfn with
    | VZ64 gfn, VZ64 pfn =>
      rely is_gfn gfn; rely is_pfn pfn;
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      when count == get_pfn_count_spec (VZ64 pfn) adt1;
      rely is_int count;
      if (owner =? HOSTVISOR) then
        if (count =? 0) then
          when adt2 == clear_pfn_host_spec (VZ64 pfn) adt1;
          when adt3 == set_pfn_owner_spec (VZ64 pfn) vmid adt2;
          when adt4 == set_pfn_map_spec (VZ64 pfn) (VZ64 gfn) adt3;
          when adt5 == fetch_from_doracle_spec vmid (VZ64 pfn) (VZ64 1) adt4;
          release_lock_s2page_spec adt5
        else
          when adt2 == panic_spec adt1;
          release_lock_s2page_spec adt2
      else
        if owner =? vmid then
          when' map == get_pfn_map_spec (VZ64 pfn) adt1;
          rely is_int64 map;
          if (map =? INVALID64) || (gfn =? map) then
            if (map =? INVALID64) then
              if count =? INVALID then
                when adt2 == set_pfn_map_spec (VZ64 pfn) (VZ64 gfn) adt1;
                when adt3 == set_pfn_count_spec (VZ64 pfn) 0 adt2;
                release_lock_s2page_spec adt3
              else
                when adt2 == set_pfn_map_spec (VZ64 pfn) (VZ64 gfn) adt1;
                release_lock_s2page_spec adt2
            else
              if count =? INVALID then
                when adt2 == set_pfn_count_spec (VZ64 pfn) 0 adt1;
                release_lock_s2page_spec adt2
              else
                release_lock_s2page_spec adt1
          else
            when adt2 == panic_spec adt1;
            release_lock_s2page_spec adt2
        else
          when adt2 == panic_spec adt1;
          release_lock_s2page_spec adt2
    end.

  Definition map_pfn_vm_spec0 (vmid: Z) (addr: Z64) (pte: Z64) (level: Z) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_addr addr;
      let paddr := phys_page pte in
      let perm := PAGE_S2_KERNEL in
      if level =? 2 then
        let pte := Z.land (Z.lor paddr perm) NOT_PMD_TABLE_BIT in
        map_s2pt_spec vmid (VZ64 addr) 2 (VZ64 pte) adt
      else
        let pte := Z.lor paddr perm in
        map_s2pt_spec vmid (VZ64 addr) 3 (VZ64 pte) adt
    end.

  Definition map_vm_io_spec0 (vmid: Z) (gpa: Z64) (pa: Z64) (adt: RData) : option RData :=
    match gpa, pa with
    | VZ64 gpa, VZ64 pa =>
      rely is_addr gpa; rely is_addr pa;
      let gfn := gpa / PAGE_SIZE in
      let pfn := pa / PAGE_SIZE in
      let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      if owner =? INVALID then
        when adt2 == map_s2pt_spec vmid (VZ64 gpa) 3 (VZ64 pte) adt1;
        release_lock_s2page_spec adt2
      else
        release_lock_s2page_spec adt1
    end.

  Definition grant_vm_page_spec0 (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_addr pfn;
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      when count == get_pfn_count_spec (VZ64 pfn) adt1;
      rely is_int count;
      if (owner =? vmid) && (count <? MAX_SHARE_COUNT) then
        when adt2 == set_pfn_count_spec (VZ64 pfn) (count + 1) adt1;
        release_lock_s2page_spec adt2
      else
        release_lock_s2page_spec adt1
    end.

  Definition revoke_vm_page_spec0 (vmid: Z) (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_addr pfn;
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      when count == get_pfn_count_spec (VZ64 pfn) adt1;
      rely is_int count;
      if (owner =? vmid) && (count >? 0) then
        when adt2 == set_pfn_count_spec (VZ64 pfn) (count - 1) adt1;
          if count =? 1 then
            when adt3 == clear_pfn_host_spec (VZ64 pfn) adt2;
            when adt4 == fetch_from_doracle_spec vmid (VZ64 pfn) (VZ64 1) adt3;
            release_lock_s2page_spec adt4
          else
            release_lock_s2page_spec adt2
      else
        release_lock_s2page_spec adt1
    end.

  Definition assign_pfn_to_smmu_spec0 (vmid: Z) (gfn: Z64) (pfn: Z64) (adt: RData) : option RData :=
    match gfn, pfn with
    | VZ64 gfn, VZ64 pfn =>
      rely is_vmid vmid; rely is_gfn gfn; rely is_pfn pfn;
      when adt1 == acquire_lock_s2page_spec adt;
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      when count == get_pfn_count_spec (VZ64 pfn) adt1;
      rely is_int count;
      when' map == get_pfn_map_spec (VZ64 pfn) adt1;
      rely is_int64 map;
      if owner =? HOSTVISOR then
        if count =? 0 then
          when adt3 == clear_pfn_host_spec (VZ64 pfn) adt1;
          when adt4 == set_pfn_owner_spec (VZ64 pfn) vmid adt3;
          when adt5 == set_pfn_map_spec (VZ64 pfn) (VZ64 gfn) adt4;
          when adt6 == set_pfn_count_spec (VZ64 pfn) INVALID adt5;
          release_lock_s2page_spec adt6
        else
          when adt2 == panic_spec adt1;
          release_lock_s2page_spec adt2
      else
        if owner =? vmid then
          release_lock_s2page_spec adt1
        else
          when adt2 == panic_spec adt1;
          release_lock_s2page_spec adt2
    end.

  Definition update_smmu_page_spec0 (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    match iova, pte with
    | VZ64 iova, VZ64 pte =>
      rely is_addr iova;
      when adt1 == acquire_lock_s2page_spec adt;
      let pfn := phys_page pte / PAGE_SIZE in
      let gfn := iova / PAGE_SIZE in
      when owner == get_pfn_owner_spec (VZ64 pfn) adt1;
      rely is_int owner;
      when' map == get_pfn_map_spec (VZ64 pfn) adt1;
      rely is_int64 map;
      if (vmid =? owner) && (gfn =? map) then
        when adt2 == map_spt_spec cbndx index (VZ64 iova) (VZ64 pte) adt1;
        if owner =? HOSTVISOR then
          when count == get_pfn_count_spec (VZ64 pfn) adt2;
          rely is_int count;
          if count <? EL2_SMMU_CFG_SIZE then
            when adt3 == set_pfn_count_spec (VZ64 pfn) (count+1) adt2;
            release_lock_s2page_spec adt3
          else
            release_lock_s2page_spec adt2
        else
          release_lock_s2page_spec adt2
      else
        when adt2 == panic_spec adt1;
        release_lock_s2page_spec adt2
    end.

  Definition unmap_smmu_page_spec0 (cbndx: Z) (index: Z) (iova: Z64) (adt: RData) : option RData :=
    match iova with
    | VZ64 iova =>
      rely is_addr iova;
      when adt1 == acquire_lock_s2page_spec adt;
      when' pte, adt2 == unmap_spt_spec cbndx index (VZ64 iova) adt1;
      rely is_int64 pte;
      let pfn := phys_page pte / PAGE_SIZE in
      when owner == get_pfn_owner_spec (VZ64 pfn) adt2;
      rely is_int owner;
      if owner =? HOSTVISOR then
        when count == get_pfn_count_spec (VZ64 pfn) adt2;
        rely is_int count;
        if count >? 0 then
          when adt3 == set_pfn_count_spec (VZ64 pfn) (count-1) adt2;
          release_lock_s2page_spec adt3
        else
          release_lock_s2page_spec adt2
      else
        release_lock_s2page_spec adt2
    end.

  Inductive map_page_host_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_page_host_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' addr
      (Hinv: high_level_invariant labd)
      (Hspec: map_page_host_spec0 (VZ64 (Int64.unsigned addr)) labd = Some labd'):
      map_page_host_spec_low_step s WB ((Vlong addr)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive clear_vm_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_vm_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn
      (Hinv: high_level_invariant labd)
      (Hspec: clear_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      clear_vm_page_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive assign_pfn_to_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | assign_pfn_to_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid gfn pfn
      (Hinv: high_level_invariant labd)
      (Hspec: assign_pfn_to_vm_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gfn)) (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      assign_pfn_to_vm_spec_low_step s WB ((Vint vmid)::(Vlong gfn)::(Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive map_pfn_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_pfn_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr pte level
      (Hinv: high_level_invariant labd)
      (Hspec: map_pfn_vm_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) (Int.unsigned level) labd = Some labd'):
      map_pfn_vm_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vlong pte)::(Vint level)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive map_vm_io_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_vm_io_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid gpa pa
      (Hinv: high_level_invariant labd)
      (Hspec: map_vm_io_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gpa)) (VZ64 (Int64.unsigned pa)) labd = Some labd'):
      map_vm_io_spec_low_step s WB ((Vint vmid)::(Vlong gpa)::(Vlong pa)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive grant_vm_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | grant_vm_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn
      (Hinv: high_level_invariant labd)
      (Hspec: grant_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      grant_vm_page_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive revoke_vm_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | revoke_vm_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn
      (Hinv: high_level_invariant labd)
      (Hspec: revoke_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      revoke_vm_page_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive assign_pfn_to_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | assign_pfn_to_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid gfn pfn
      (Hinv: high_level_invariant labd)
      (Hspec: assign_pfn_to_smmu_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gfn)) (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      assign_pfn_to_smmu_spec_low_step s WB ((Vint vmid)::(Vlong gfn)::(Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive update_smmu_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | update_smmu_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid cbndx index iova pte
      (Hinv: high_level_invariant labd)
      (Hspec: update_smmu_page_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      update_smmu_page_spec_low_step s WB ((Vint vmid)::(Vint cbndx)::(Vint index)::(Vlong iova)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive unmap_smmu_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | unmap_smmu_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index iova
      (Hinv: high_level_invariant labd)
      (Hspec: unmap_smmu_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) labd = Some labd'):
      unmap_smmu_page_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong iova)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition map_page_host_spec_low: compatsem LDATAOps :=
      csem map_page_host_spec_low_step (type_of_list_type (Tint64::nil)) Tvoid.

    Definition clear_vm_page_spec_low: compatsem LDATAOps :=
      csem clear_vm_page_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tvoid.

    Definition assign_pfn_to_vm_spec_low: compatsem LDATAOps :=
      csem assign_pfn_to_vm_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition map_pfn_vm_spec_low: compatsem LDATAOps :=
      csem map_pfn_vm_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint32::nil)) Tvoid.

    Definition map_vm_io_spec_low: compatsem LDATAOps :=
      csem map_vm_io_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition grant_vm_page_spec_low: compatsem LDATAOps :=
      csem grant_vm_page_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tvoid.

    Definition revoke_vm_page_spec_low: compatsem LDATAOps :=
      csem revoke_vm_page_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tvoid.

    Definition assign_pfn_to_smmu_spec_low: compatsem LDATAOps :=
      csem assign_pfn_to_smmu_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition update_smmu_page_spec_low: compatsem LDATAOps :=
      csem update_smmu_page_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition unmap_smmu_page_spec_low: compatsem LDATAOps :=
      csem unmap_smmu_page_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::nil)) Tvoid.

  End WITHMEM.

End MemManagerSpecLow.

```
