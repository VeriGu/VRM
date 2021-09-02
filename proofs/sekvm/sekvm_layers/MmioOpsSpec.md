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

Require Import VMPower.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import MmioOpsAux.Spec.
Require Import MmioSPTWalk.Spec.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioSPTOps.Spec.
Require Import MmioOpsAux.Layer.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.


Local Open Scope Z_scope.

Section MmioOpsSpec.

  Definition emulate_mmio_spec (addr: Z64) (hsr: Z) (adt: RData) : option (RData * Z) :=
    match addr with
    | VZ64 addr =>
      let fault_ipa := Z.lor addr (Z.land (far_el2 (ctxt_regs (regs adt))) 4095) in
      let len := host_dabt_get_as' hsr in
      let is_write := host_dabt_is_write' hsr in
      let rt := host_dabt_get_rd' hsr in
      let vcpuid := cur_vcpuid adt in
      rely is_addr addr; rely is_int hsr;
      rely is_addr fault_ipa; rely is_int len; rely is_int is_write;
      rely is_int rt; rely is_vcpu vcpuid;
      if halt adt then Some (adt, 0) else
      let cpu := curid adt in
      match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
      | LockFalse, sorc, sl0 =>
        match H_CalLock (sorc cpu sl0 ++ sl0) with
        | Some (_, EMPTY, None) =>
          let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
          let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
          let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
          let conf := smmu_conf adt in
          let num := smmu_num conf in
          rely is_smmu num;
          match is_smmu_range_loop (Z.to_nat num) addr 0 INVALID conf with
          | Some (idx, res) =>
            rely is_int res;
            if res =? INVALID then
              Some (adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                        {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse},
                    INVALID)
            else
              rely is_smmu res;
              let logn := HOSTVISOR @ (data_log adt) in
              let ctxt := (ctxt_id HOSTVISOR vcpuid) @ (shadow_ctxts adt) in
              match
                handle_host_mmio_specx res fault_ipa len is_write rt (ctxt_regs ctxt) (ctxt_states ctxt) (ctxt_regs (regs adt)) (doracle adt) logn smmu
              with
              | Some (halt', logn', cregs', cstates', rcregs') =>
                if halt' then
                  Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {smmu_vmid: smmu}}
                            {data_log : if logn =? logn' then data_log adt else (data_log adt) # HOSTVISOR == logn'}
                            {regs : (regs adt) {ctxt_regs : rcregs'}}
                            {log: (log adt) # SMMU_ID == sl} {lock: (lock adt) # SMMU_ID == (LockOwn true)},
                        0)
                else
                  Some (adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                            {data_log : if logn =? logn' then data_log adt else (data_log adt) # HOSTVISOR == logn'}
                            {shadow_ctxts: if (is_write =? 0)
                                           then (shadow_ctxts adt) # (ctxt_id HOSTVISOR vcpuid) == ((ctxt {ctxt_regs : cregs'}) {ctxt_states : cstates'})
                                           else (shadow_ctxts adt)}
                            {regs : (regs adt) {ctxt_regs : rcregs'}}
                            {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse},
                        res)
              | _ => None
              end
          | _ => None
          end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition el2_free_smmu_pgd_spec (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    rely is_smmu index; rely is_smmu_cfg cbndx;
    if halt adt then Some adt else
    let cpu := curid adt in
    match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
    | LockFalse, sorc, sl0 =>
      match H_CalLock (sorc cpu sl0 ++ sl0) with
      | Some (_, EMPTY, None) =>
        let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
        let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
        let vmid := (smmu_id index cbndx) @ smmu in
        if vmid =? INVALID then
          let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
          Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
               {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse}
        else
          rely is_vmid vmid;
          let id := INFO_ID + vmid in
          match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
          | LockFalse, orac, l0 =>
            match H_CalLock ((orac cpu l0) ++ l0) with
            | Some (_, LEMPTY, None) =>
              let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
              rely is_int (vm_state (VS info));
              let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) ::
                                TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                                (orac cpu l0) ++ l0 in
              if vm_state (VS info) =? POWEROFF then
                let smmu' := smmu # (smmu_id index cbndx) == INVALID in
                let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu')) :: sl in
                Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                    {log: ((log adt) # SMMU_ID == sl') # id == l'} {lock: ((lock adt) # SMMU_ID == LockFalse) # id == LockFalse}
              else
                Some adt {halt: true} {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                    {log: ((log adt) # SMMU_ID == sl) # id == l'} {lock: ((lock adt) # SMMU_ID == (LockOwn true)) # id == LockFalse}
            | _ => None
            end
          | _, _, _ => None
        end
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition el2_alloc_smmu_pgd_spec (cbndx: Z) (vmid: Z) (index: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_smmu index; rely is_smmu_cfg cbndx;
    if halt adt then Some adt else
    let cpu := curid adt in
    let num := index @ (smmu_dev_context_banks (smmu_conf adt)) in
    rely is_int num;
    match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
    | LockFalse, sorc, sl0 =>
      match H_CalLock (sorc cpu sl0 ++ sl0) with
      | Some (_, EMPTY, None) =>
        let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
        let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
        if cbndx <? num then
          let target := (smmu_id index cbndx) @ smmu in
          rely is_int target;
          if target =? INVALID then
            let smmu' := smmu # (smmu_id index cbndx) == vmid in
            let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu')) :: sl in
            match SPT_ID @ (lock adt), SPT_ID @ (oracle adt), SPT_ID @ (log adt) with
            | LockFalse, pto, ptl0 =>
              match H_CalLock (pto cpu ptl0 ++ ptl0) with
              | Some (_, EMPTY, None) =>
                let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
                let ttbr := SMMU_TTBR index cbndx in
                let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (ZMap.init (0, 0))}
                                {spt_pgd_t: (spt_pgd_t spt) # ttbr == (ZMap.init false)}
                                {spt_pmd_t: (spt_pmd_t spt) # ttbr == (ZMap.init (ZMap.init false))} in
                let ptl' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt'))) ::
                              TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
                Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu'} {spts: spt'}}
                    {log: ((log adt) # SMMU_ID == sl') # SPT_ID == ptl'} {lock: ((lock adt) # SMMU_ID == LockFalse) # SPT_ID == LockFalse}
              | _ => None
              end
            | _, _, _ => None
            end
          else
            let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
            Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse}
        else
          Some adt {halt: true} {tstate: 0} {shared: (shared adt) {smmu_vmid: smmu}}
               {log: (log adt) # SMMU_ID == sl} {lock: (lock adt) # SMMU_ID == (LockOwn true)}
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition smmu_assign_page_spec (cbndx: Z) (index: Z) (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    match pfn, gfn with
    | VZ64 pfn, VZ64 gfn =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_gfn gfn; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
      | LockFalse, sorc, sl0 =>
        match H_CalLock (sorc cpu sl0 ++ sl0) with
        | Some (_, EMPTY, None) =>
          let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
          let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
          let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
          let vmid := (smmu_id index cbndx) @ smmu in
          if vmid =? INVALID then
            Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse}
          else
            rely is_vmid vmid;
            let id := INFO_ID + vmid in
            let ptid := NPT_ID in
            let cpu := curid adt in
            match id @ (lock adt), id @ (oracle adt), id @ (log adt),
                  S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
                  ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt),
                  FLATMEM_ID @ (log adt), FLATMEM_ID @ (oracle adt) with
            | LockFalse, vmo, vml0, LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
              match H_CalLock ((vmo cpu vml0) ++ vml0), H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
              | Some (_, LEMPTY, None), Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
                let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
                let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
                let npt := CalNPT (HOSTVISOR @ (npts (shared adt))) (pto cpu ptl0) in
                let fmem := CalFlatmem (flatmem (shared adt)) (fmo cpu fml0) in
                let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
                let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
                let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((vmo cpu vml0) ++ vml0) in
                let vml' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
                let state := vm_state (VS info) in
                rely is_int state;
                if (HOSTVISOR <? vmid) && (vmid <? COREVISOR)  then
                  if state =? VERIFIED then
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
                            if halt' then
                              Some adt {halt: true} {tstate: 0}
                                  {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'} {smmu_vmid: smmu}
                                                        {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                                  {log: (((((log adt) # SMMU_ID == sl) # id == vml)# S2PAGE_ID == spl) # ptid == ptl)}
                                  {lock: ((((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)}
                            else
                              Some adt {tstate: 1} {data_log: (data_log adt) # vmid == (logn + 1)}
                                  {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'} {smmu_vmid: smmu}
                                                        {s2page: s2p'} {flatmem: fmem'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                                  {log: (((((log adt) # SMMU_ID == sl') # id == vml')# S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                                  {lock: ((((lock adt) # SMMU_ID == LockFalse) # id == LockFalse) # S2PAGE_ID == LockFalse) # ptid == LockFalse}
                          | _ => None
                          end
                        end
                      else
                        Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((log adt) # SMMU_ID == sl) # id == vml) # S2PAGE_ID == spl} {lock: (((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
                    else
                      if s2_owner page =? vmid then
                        let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
                        Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((log adt) # SMMU_ID == sl') # id == vml') # S2PAGE_ID == spl'} {lock: (((lock adt) # SMMU_ID == LockFalse) # id == LockFalse) # S2PAGE_ID == LockFalse}
                      else
                        Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((log adt) # SMMU_ID == sl) # id == vml) # S2PAGE_ID == spl} {lock: (((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
                  else
                    Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                              {log: ((log adt) # SMMU_ID == sl) # id == vml} {lock: ((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)})
                else
                  Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: ((log adt) # SMMU_ID == sl') # id == vml'} {lock: ((lock adt) # SMMU_ID == LockFalse) # id == LockFalse}
              | _, _, _ => None
              end
            | _, _, _, _, _, _, _, _, _, _, _ => None
            end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition smmu_map_page_spec (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    match iova, pte with
    | VZ64 iova, VZ64 pte =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova; rely is_int64 pte;
      if halt adt then Some adt else
      let cpu := curid adt in
      match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
      | LockFalse, sorc, sl0 =>
        match H_CalLock (sorc cpu sl0 ++ sl0) with
        | Some (_, EMPTY, None) =>
          let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
          let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
          let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
          let vmid := (smmu_id index cbndx) @ smmu in
          if vmid =? INVALID then
            Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse}
          else
            rely is_vmid vmid;
            let id := INFO_ID + vmid in
            match id @ (lock adt), id @ (oracle adt), id @ (log adt),
                  S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
                  SPT_ID @ (lock adt), SPT_ID @ (log adt), SPT_ID @ (oracle adt) with
            | LockFalse, vmo, vml0, LockFalse, spl0, spo, LockFalse, ptl0, pto =>
              match H_CalLock ((vmo cpu vml0) ++ vml0), H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
              | Some (_, LEMPTY, None), Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
                let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
                let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
                let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
                let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
                let ptl := TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
                let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((vmo cpu vml0) ++ vml0) in
                let vml' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
                let state := vm_state (VS info) in
                rely is_int state;
                if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) && (state =? VERIFIED) then
                  Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: ((log adt) # SMMU_ID == sl) # id == vml} {lock: ((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)})
                else
                  let pfn := phys_page pte / PAGE_SIZE in
                  let gfn := iova / PAGE_SIZE in
                  let page := pfn @ s2p in
                  rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
                  if (vmid =? s2_owner page) && (gfn =? s2_gfn page) then
                    match local_spt_map cbndx index iova pte spt with
                    | Some (halt', spt') =>
                      if halt' then
                        Some adt {halt: true} {tstate: 0}
                            {shared: (shared adt) {spts: spt'} {s2page: s2p} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((((log adt) # SMMU_ID == sl) # id == vml)# S2PAGE_ID == spl) # SPT_ID == ptl)}
                            {lock: ((((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
                      else
                        let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page <? EL2_SMMU_CFG_SIZE)
                                      then s2p # pfn == (page {s2_count: (s2_count page) + 1}) else s2p) in
                        let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
                        let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                        Some adt {tstate: 1} {shared: (shared adt) {spts: spt'} {s2page: s2p'} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((((log adt) # SMMU_ID == sl') # id == vml') # S2PAGE_ID == spl') # SPT_ID == ptl')}
                            {lock: ((((lock adt) # SMMU_ID == LockFalse) # id == LockFalse) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
                    | _ => None
                    end
                  else
                    Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((log adt) # SMMU_ID == sl) # id == vml) # S2PAGE_ID == spl}
                            {lock: (((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
              | _, _, _ => None
              end
            | _, _, _, _, _, _, _, _, _ => None
            end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition el2_arm_lpae_iova_to_phys_spec (iova: Z64) (cbndx: Z) (index: Z) (adt: RData) : option (RData * Z64) :=
    match iova with
    | VZ64 iova =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova;
      if halt adt then Some (adt, VZ64 0) else
      let cpu := curid adt in
      match SPT_ID @ (lock adt), SPT_ID @ (oracle adt), SPT_ID @ (log adt) with
      | LockFalse, pto, ptl0 =>
        match H_CalLock (pto cpu ptl0 ++ ptl0) with
        | Some (_, EMPTY, None) =>
          let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
          let ttbr := SMMU_TTBR index cbndx in
          let pt := ttbr @ (spt_pt spt) in
          let gfn := iova / PAGE_SIZE in
          match gfn @ pt with
          | (pfn, pte) =>
            rely is_int64 pte;
            let ptl' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt))) ::
                          TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
            Some (adt {tstate: 1} {shared: (shared adt) {spts: spt}}
                      {log: (log adt) # SPT_ID == ptl'} {lock: (lock adt) # SPT_ID == LockFalse},
                  VZ64 (phys_page pte + (Z.land iova 4095)))
          end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition el2_arm_lpae_clear_spec (iova: Z64) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match iova with
    | VZ64 iova =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova;
      if halt adt then Some adt else
      let cpu := curid adt in
      match SMMU_ID @ (lock adt), SMMU_ID @ (oracle adt), SMMU_ID @ (log adt) with
      | LockFalse, sorc, sl0 =>
        match H_CalLock (sorc cpu sl0 ++ sl0) with
        | Some (_, EMPTY, None) =>
          let smmu := CalSMMU (smmu_vmid (shared adt)) (sorc cpu sl0) in
          let sl := TEVENT cpu (TSHARED (OPULL SMMU_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (sorc cpu sl0) ++ sl0 in
          let sl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSMMU smmu)) :: sl in
          let vmid := (smmu_id index cbndx) @ smmu in
          if vmid =? INVALID then
            Some adt {tstate: 1} {shared: (shared adt) {smmu_vmid: smmu}}
                {log: (log adt) # SMMU_ID == sl'} {lock: (lock adt) # SMMU_ID == LockFalse}
          else
            rely is_vmid vmid;
            let id := INFO_ID + vmid in
            match id @ (lock adt), id @ (oracle adt), id @ (log adt),
                  S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
                  SPT_ID @ (lock adt), SPT_ID @ (log adt), SPT_ID @ (oracle adt) with
            | LockFalse, vmo, vml0, LockFalse, spl0, spo, LockFalse, ptl0, pto =>
              match H_CalLock ((vmo cpu vml0) ++ vml0), H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
              | Some (_, LEMPTY, None), Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
                let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
                let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
                let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
                let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
                let ptl := TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
                let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((vmo cpu vml0) ++ vml0) in
                let vml' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
                let state := vm_state (VS info) in
                rely is_int state;
                if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) && (state =? VERIFIED) then
                  Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {smmu_vmid: smmu} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: ((log adt) # SMMU_ID == sl) # id == vml} {lock: ((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)})
                else
                  let ttbr := SMMU_TTBR index cbndx in
                  let pt := ttbr @ (spt_pt spt) in
                  let gfn := iova / PAGE_SIZE in
                  let (_, pte) := gfn @ pt in
                  rely is_int64 pte;
                  match (if pte =? 0 then Some (false, spt) else local_spt_map cbndx index iova 0 spt) with
                  | Some (halt', spt') =>
                    if halt' then
                      Some adt {halt: true} {tstate: 0} {shared: (shared adt) {spts: spt'} {smmu_vmid: smmu} {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                              {log: ((((log adt) # SMMU_ID == sl) # id == vml) # S2PAGE_ID == spl) # SPT_ID == ptl}
                              {lock: ((((lock adt) # SMMU_ID == (LockOwn true)) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
                    else
                      let pfn := phys_page pte / PAGE_SIZE in
                      let page := pfn @ s2p in
                      rely is_int (s2_owner page); rely is_int (s2_count page);
                      let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page >? 0)
                                    then s2p # pfn == (page {s2_count: (s2_count page) - 1}) else s2p) in
                      let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                      let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
                      Some adt {tstate: 1} {shared: (shared adt) {spts: spt'} {smmu_vmid: smmu} {s2page: s2p'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (((((log adt) # SMMU_ID == sl') # id == vml') # S2PAGE_ID == spl') # SPT_ID == ptl')}
                            {lock: ((((lock adt) # SMMU_ID == LockFalse) # id == LockFalse) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
                  | _ => None
                  end
              | _, _, _ => None
              end
            | _, _, _, _, _, _, _, _, _ => None
            end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

End MmioOpsSpec.

Section MmioOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioOpsAux_ops) LDATA).

  Definition emulate_mmio_spec0 (addr: Z64) (hsr: Z) (adt: RData) : option (RData * Z) :=
    match addr with
    | VZ64 addr =>
      when adt' == acquire_lock_smmu_spec adt;
      when res == is_smmu_range_spec (VZ64 addr) adt';
      rely is_int res;
      if res =? INVALID then
        when adt'' == release_lock_smmu_spec adt';
        when ret == check_spec res adt'';
        Some (adt'', ret)
      else
        when adt'' == handle_host_mmio_spec (VZ64 addr) res hsr adt';
        when adt3 == release_lock_smmu_spec adt'';
        when ret == check_spec res adt3;
        Some (adt3, ret)
     end.

  Definition el2_free_smmu_pgd_spec0 (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    when adt' == acquire_lock_smmu_spec adt;
    when vmid == get_smmu_cfg_vmid_spec cbndx index adt';
    rely is_int vmid;
    if vmid =? INVALID then
      release_lock_smmu_spec adt'
    else
      when power, adt2 == get_vm_poweron_spec vmid adt';
      rely is_int power;
      if power =? 0 then
        when adt'' == set_smmu_cfg_vmid_spec cbndx index INVALID adt2;
        release_lock_smmu_spec adt''
      else
        when adt'' == panic_spec adt2;
        release_lock_smmu_spec adt''.

  Definition el2_alloc_smmu_pgd_spec0 (cbndx: Z) (vmid: Z) (index: Z) (adt: RData) : option RData :=
    when adt' == acquire_lock_smmu_spec adt;
    when num == get_smmu_num_context_banks_spec index adt';
    rely is_int num;
    if cbndx <? num then
      when target == get_smmu_cfg_vmid_spec cbndx index adt';
      rely is_int target;
      if target =? INVALID then
        when adt2 == set_smmu_cfg_vmid_spec cbndx index vmid adt';
        when adt3 == alloc_smmu_spec vmid cbndx index adt2;
        release_lock_smmu_spec adt3
      else
        release_lock_smmu_spec adt'
    else
      when adt2 == panic_spec adt';
      release_lock_smmu_spec adt2.

  Definition smmu_assign_page_spec0 (cbndx: Z) (index: Z) (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    when adt1 == acquire_lock_smmu_spec adt;
    when vmid == get_smmu_cfg_vmid_spec cbndx index adt1;
    rely is_int vmid;
    if vmid =? INVALID then
      release_lock_smmu_spec adt1
    else
      when adt2 == assign_smmu_spec vmid pfn gfn adt1;
      release_lock_smmu_spec adt2.

  Definition smmu_map_page_spec0 (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    when adt1 == acquire_lock_smmu_spec adt;
    when vmid == get_smmu_cfg_vmid_spec cbndx index adt1;
    rely is_int vmid;
    if vmid =? INVALID then
      release_lock_smmu_spec adt1
    else
      when adt2 == map_smmu_spec vmid cbndx index iova pte adt1;
      release_lock_smmu_spec adt2.

  Definition el2_arm_lpae_iova_to_phys_spec0 (iova: Z64) (cbndx: Z) (index: Z) (adt: RData) : option (RData * Z64) :=
    match iova with
    | VZ64 iova =>
      when' pte, adt' == walk_spt_spec cbndx index (VZ64 iova) adt;
      rely is_int64 pte;
      let res := phys_page pte + (Z.land iova 4095) in
      when' ret == check64_spec (VZ64 res) adt';
      Some (adt', VZ64 ret)
    end.

  Definition el2_arm_lpae_clear_spec0 (iova: Z64) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_smmu_spec adt;
    when vmid == get_smmu_cfg_vmid_spec cbndx index adt1;
    rely is_int vmid;
    if vmid =? INVALID then
      release_lock_smmu_spec adt1
    else
      when adt2 == clear_smmu_spec vmid cbndx index iova adt1;
      release_lock_smmu_spec adt2.

  Inductive emulate_mmio_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | emulate_mmio_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' addr hsr res
      (Hinv: high_level_invariant labd)
      (Hspec: emulate_mmio_spec0 (VZ64 (Int64.unsigned addr)) (Int.unsigned hsr) labd = Some (labd', (Int.unsigned res))):
      emulate_mmio_spec_low_step s WB ((Vlong addr)::(Vint hsr)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Inductive el2_free_smmu_pgd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | el2_free_smmu_pgd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: el2_free_smmu_pgd_spec0 (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      el2_free_smmu_pgd_spec_low_step s WB ((Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive el2_alloc_smmu_pgd_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | el2_alloc_smmu_pgd_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx vmid index
      (Hinv: high_level_invariant labd)
      (Hspec: el2_alloc_smmu_pgd_spec0 (Int.unsigned cbndx) (Int.unsigned vmid) (Int.unsigned index) labd = Some labd'):
      el2_alloc_smmu_pgd_spec_low_step s WB ((Vint cbndx)::(Vint vmid)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive smmu_assign_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | smmu_assign_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index pfn gfn
      (Hinv: high_level_invariant labd)
      (Hspec: smmu_assign_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) labd = Some labd'):
      smmu_assign_page_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong pfn)::(Vlong gfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive smmu_map_page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | smmu_map_page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index iova pte
      (Hinv: high_level_invariant labd)
      (Hspec: smmu_map_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      smmu_map_page_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong iova)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive el2_arm_lpae_iova_to_phys_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | el2_arm_lpae_iova_to_phys_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' iova cbndx index res
      (Hinv: high_level_invariant labd)
      (Hspec: el2_arm_lpae_iova_to_phys_spec0 (VZ64 (Int64.unsigned iova)) (Int.unsigned cbndx) (Int.unsigned index) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      el2_arm_lpae_iova_to_phys_spec_low_step s WB ((Vlong iova)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive el2_arm_lpae_clear_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | el2_arm_lpae_clear_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' iova cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: el2_arm_lpae_clear_spec0 (VZ64 (Int64.unsigned iova)) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      el2_arm_lpae_clear_spec_low_step s WB ((Vlong iova)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition emulate_mmio_spec_low: compatsem LDATAOps :=
      csem emulate_mmio_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tint32.

    Definition el2_free_smmu_pgd_spec_low: compatsem LDATAOps :=
      csem el2_free_smmu_pgd_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition el2_alloc_smmu_pgd_spec_low: compatsem LDATAOps :=
      csem el2_alloc_smmu_pgd_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition smmu_assign_page_spec_low: compatsem LDATAOps :=
      csem smmu_assign_page_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition smmu_map_page_spec_low: compatsem LDATAOps :=
      csem smmu_map_page_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition el2_arm_lpae_iova_to_phys_spec_low: compatsem LDATAOps :=
      csem el2_arm_lpae_iova_to_phys_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::nil)) Tint64.

    Definition el2_arm_lpae_clear_spec_low: compatsem LDATAOps :=
      csem el2_arm_lpae_clear_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End MmioOpsSpecLow.

```
