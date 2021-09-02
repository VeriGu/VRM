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

Require Import NPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import MemManager.Spec.
Require Import BootAux.Spec.
Require Import MmioSPTOps.Spec.
Require Import RData.
Require Import BootAux.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import BootCore.Spec.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.
Require Import PageManager.Spec.

Local Open Scope Z_scope.

Section BootOpsSpec.

  Fixpoint search_load_info_loop (n: nat) (idx: Z) (addr: Z) (ret: Z) (binfo: BootInfo) :=
    match n with
    | O => Some (idx, ret)
    | S n' =>
      match search_load_info_loop n' idx addr ret binfo with
      | Some (idx', ret') =>
        match idx' @ (vm_load_addr binfo), idx' @ (vm_load_size binfo), idx' @ (vm_remap_addr binfo) with
        | base, size, remap =>
          rely is_addr base; rely is_addr size; rely is_addr remap; rely (remap + size <=? KVM_ADDR_SPACE);
          if (addr >=? base) && (addr <? base + size) then
            Some (idx' + 1, (addr - base) + remap)
          else
            Some (idx' + 1, ret')
        end
      | _ => None
      end
    end.

  Definition search_load_info_spec (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_int64 addr;
      if halt adt then Some (adt, VZ64 0) else
      let id := INFO_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
      | LockFalse, orac, l0 =>
        match H_CalLock ((orac cpu l0) ++ l0) with
        | Some (_, LEMPTY, None) =>
          let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
          let num := vm_next_load_info (VB info) in
          rely (0 <=? num) && (num <=? MAX_LOAD_INFO_NUM);
          match search_load_info_loop (Z.to_nat num) 0 addr 0 (VB info) with
          | Some (idx', ret') =>
            let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) ::
                              TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                              (orac cpu l0) ++ l0 in
            Some (adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse},
                  VZ64 ret')
          | _ => None
          end
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Definition set_vcpu_active_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        match vm_state (VS info), vcpuid @ (vm_vcpu_state (VS info)) with
        | vms, vcpus =>
          rely is_int vms; rely is_int vcpus;
          if (vms =? VERIFIED) && (vcpus =? READY) then
            let info' := info {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == ACTIVE} in
            let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                              TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                              (orac cpu l0) ++ l0 in
            Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
                {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse}
          else
            let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                             (orac cpu l0) ++ l0 in
            Some adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
        end
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition set_vcpu_inactive_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        let vcpus := vcpuid @ (vm_vcpu_state (VS info)) in
        rely is_int vcpus;
        if (vcpus =? ACTIVE) then
          let info' := info {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == READY} in
          let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                            TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                            (orac cpu l0) ++ l0 in
          Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
              {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse}
        else
          let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                            (orac cpu l0) ++ l0 in
          Some adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
              {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition register_vcpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        match vm_state (VS info), vcpuid @ (vm_vcpu_state (VS info)), (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) with
        | vms, vcpus, ctxt =>
          rely is_int vms; rely is_int vcpus;
          if (vms =? READY) && (vcpus =? UNUSED) then
            let vcpu := shared_vcpu vmid vcpuid in
            rely is_int64 vcpu;
            let info' := info {vm_vcpu: (vm_vcpu (VS info)) # vcpuid == vcpu} {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == READY} in
            let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: INVALID64}} in
            let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                              TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                              (orac cpu l0) ++ l0 in
            Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
                {shadow_ctxts: (shadow_ctxts adt) # (ctxt_id vmid vcpuid) == ctxt'}
                {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse}
          else
            let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                             (orac cpu l0) ++ l0 in
            Some adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                 {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
        end
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition register_kvm_spec  (adt: RData) : option (RData * Z) :=
    if halt adt then Some (adt, 0) else
    let cpu := curid adt in
    match CORE_ID @ (lock adt), CORE_ID @ (oracle adt), CORE_ID @ (log adt) with
    | LockFalse, co, cl0 =>
      match H_CalLock ((co cpu cl0) ++ cl0) with
      | Some (_, LEMPTY, None) =>
        let core := CalCoreData (core_data (shared adt)) (co cpu cl0) in
        let vmid := next_vmid core in
        rely is_vmid vmid;
        if vmid <? COREVISOR then
          let core' := core {next_vmid: vmid + 1} in
          let cl' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OCORE_DATA core')) ::
                            TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                            (co cpu cl0) ++ cl0 in
          let id := INFO_ID + vmid in
          match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
          | LockFalse, vmo, vml0 =>
            match H_CalLock ((vmo cpu vml0) ++ vml0) with
            | Some (_, LEMPTY, None) =>
              let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
              let vms := vm_state (VS info) in
              rely is_int vms;
              if (vms =? UNUSED) then
                let kvm := shared_kvm vmid in
                rely is_int64 kvm;
                let info' := info {vm_kvm: kvm} {vm_state: READY} in
                let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                                    TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                                    (vmo cpu vml0) ++ vml0 in
                Some (adt {tstate: 1} {shared: (shared adt) {core_data: core'} {vminfos: (vminfos (shared adt)) # vmid == info'}}
                          {log: ((log adt) # CORE_ID == cl') # id == vml'} {lock: ((lock adt) # CORE_ID == LockFalse) # id == LockFalse},
                      vmid)
              else
                let vml' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (vmo cpu vml0) ++ vml0 in
                Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {core_data: core'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                          {log: ((log adt) # CORE_ID == cl') # id == vml'} {lock: ((lock adt) # CORE_ID == LockFalse) # id == (LockOwn true)},
                      0)
            | _ => None
            end
          | _, _, _ => None
          end
        else
          let cl' := TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (co cpu cl0) ++ cl0 in
          Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {core_data: core}}
                    {log: (log adt) # CORE_ID == cl'} {lock: (lock adt) # CORE_ID == (LockOwn true)},
                0)
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition set_boot_info_spec (vmid: Z) (load_addr: Z64) (size: Z64) (adt: RData) : option (RData * Z) :=
    match load_addr, size with
    | VZ64 load_addr, VZ64 size =>
      rely is_vmid vmid; rely is_addr load_addr; rely is_addr size;
      if halt adt then Some (adt, 0) else
      let cpu := curid adt in
      let id := INFO_ID + vmid in
      match CORE_ID @ (lock adt), CORE_ID @ (oracle adt), CORE_ID @ (log adt),
            id @ (lock adt), id @ (oracle adt), id @ (log adt) with
      | LockFalse, co, cl0, LockFalse, vmo, vml0 =>
        match H_CalLock ((co cpu cl0) ++ cl0), H_CalLock ((vmo cpu vml0) ++ vml0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let core := CalCoreData (core_data (shared adt)) (co cpu cl0) in
          let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
          let cl := TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (co cpu cl0) ++ cl0 in
          let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (vmo cpu vml0) ++ vml0 in
          let state := vm_state (VS info) in
          rely is_int state;
          if state =? READY then
            let load_idx := vm_next_load_info (VB info) in
            rely is_int load_idx;
            if load_idx <? MAX_LOAD_INFO_NUM then
              let pgnum := (size + 4095) / PAGE_SIZE in
              let remap := next_remap_ptr core in
              rely is_addr remap; rely is_gfn pgnum;
              if remap + pgnum * PAGE_SIZE <? REMAP_END then
                let core' := core {next_remap_ptr : remap + pgnum * PAGE_SIZE} in
                let cl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OCORE_DATA core')) :: cl in
                let info' := info {vm_next_load_info: load_idx + 1}
                                  {vm_load_addr: (vm_load_addr (VB info)) # load_idx == load_addr}
                                  {vm_load_size: (vm_load_size (VB info)) # load_idx == size}
                                  {vm_remap_addr: (vm_remap_addr (VB info)) # load_idx == remap}
                                  {vm_mapped_pages: (vm_mapped_pages (VB info)) # load_idx == 0} in
                let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) :: vml in
                Some (adt {tstate: 1} {shared: (shared adt) {core_data: core'} {vminfos: (vminfos (shared adt)) # vmid == info'}}
                          {log: ((log adt) # CORE_ID == cl') # id == vml'} {lock: ((lock adt) # CORE_ID == LockFalse) # id == LockFalse},
                      load_idx)
              else
                Some (adt {halt : true} {tstate : 0}
                          {shared : (shared adt) {core_data : core} {vminfos: (vminfos (shared adt)) # vmid == (info {vm_next_load_info: load_idx + 1})}}
                          {log : ((log adt) # id == vml) # CORE_ID == cl} {lock: ((lock adt) # id == (LockOwn true)) # CORE_ID == (LockOwn true)},
                      0)
            else
              let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
              Some (adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                        {log: (log adt) # id == vml'} {lock: (lock adt) # id == LockFalse},
                    load_idx)
          else
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)},
                  0)
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

  Definition remap_vm_image_spec (vmid: Z) (pfn: Z64) (load_idx: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_vmid vmid; rely is_load_idx load_idx; rely is_pfn pfn;
      if halt adt then Some adt else
      let cpu := curid adt in
      let id := INFO_ID + vmid in
      match (NPT_ID + COREVISOR) @ (lock adt), (NPT_ID + COREVISOR) @ (oracle adt), (NPT_ID + COREVISOR) @ (log adt),
            id @ (lock adt), id @ (oracle adt), id @ (log adt) with
      | LockFalse, pto, ptl0, LockFalse, vmo, vml0 =>
        match H_CalLock ((pto cpu ptl0) ++ ptl0), H_CalLock ((vmo cpu vml0) ++ vml0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let npt := CalNPT (COREVISOR @ (npts (shared adt))) (pto cpu ptl0) in
          let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
          let ptl := TEVENT cpu (TSHARED (OPULL (NPT_ID + COREVISOR))) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
          let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (vmo cpu vml0) ++ vml0 in
          let state := vm_state (VS info) in
          rely is_int state;
          if state =? READY then
            let load_info_cnt := vm_next_load_info (VB info) in
            rely is_int load_info_cnt;
            if load_idx <? load_info_cnt then
              match load_idx @ (vm_load_size (VB info)), load_idx @ (vm_remap_addr (VB info)), load_idx @ (vm_mapped_pages (VB info)) with
              | size, remap, mapped =>
                rely is_addr size; rely is_addr mapped; rely is_addr remap;
                let pgnum := (size + 4095) / PAGE_SIZE in
                let target := remap + mapped * PAGE_SIZE in
                rely is_addr target;
                if mapped <? pgnum then
                  match local_mmap COREVISOR target 3 (Z.lor (pfn * PAGE_SIZE) PAGE_HYP) npt with
                  | Some (halt', npt') =>
                    if halt' then
                      Some (adt {halt: true} {tstate: 0}
                                {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}
                                                      {npts: (npts (shared adt)) # COREVISOR == npt'}}
                                {log: ((log adt) # id == vml) # (NPT_ID + COREVISOR) == ptl}
                                {lock: ((lock adt) # id == (LockOwn true)) # (NPT_ID + COREVISOR) == (LockOwn true)})
                    else
                      let info' := info {vm_mapped_pages: (vm_mapped_pages (VB info)) # load_idx == (mapped + 1)} in
                      let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) :: vml in
                      let ptl' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                      Some (adt {tstate: 1}
                                {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}
                                                      {npts: (npts (shared adt)) # COREVISOR == npt'}}
                                {log: ((log adt) # id == vml') # (NPT_ID + COREVISOR) == ptl'}
                                {lock: ((lock adt) # id == LockFalse) # (NPT_ID + COREVISOR) == LockFalse})
                  | _ => None
                  end
                else
                  let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
                  Some (adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: (log adt) # id == vml'} {lock: (lock adt) # id == LockFalse})
              end
            else
              let vml' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
              Some (adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                        {log: (log adt) # id == vml'} {lock: (lock adt) # id == LockFalse})
          else
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
        | _, _ => None
        end
      | _, _, _, _, _, _ => None
      end
    end.

  Fixpoint verify_and_load_loop (n: nat) (vmid: Z) (load_idx: Z) (adt: RData) :=
    match n with
    | O => Some (load_idx, adt)
    | S n' =>
      match verify_and_load_loop n' vmid load_idx adt with
      | Some (idx', adt') =>
        rely is_load_idx idx';
        when' load_addr == get_vm_load_addr_spec vmid idx' adt';
        when' remap_addr == get_vm_remap_addr_spec vmid idx' adt';
        when' mapped == get_vm_mapped_pages_spec vmid idx' adt';
        rely is_addr load_addr; rely is_addr remap_addr; rely is_addr mapped;
        when adt1 == unmap_and_load_vm_image_spec vmid (VZ64 load_addr) (VZ64 remap_addr) (VZ64 mapped) adt';
        when valid == verify_image_spec vmid (VZ64 remap_addr) adt1;
        rely is_int valid;
        if valid =? 0 then
          when adt2 == panic_spec adt1;
          Some (idx' + 1, adt2)
        else
          Some (idx' + 1, adt1)
      | _ => None
      end
    end.

  Definition verify_and_load_images_spec (vmid: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    when state == get_vm_state_spec vmid adt1;
    rely is_int state;
    if state =? READY then
      when cnt == get_vm_next_load_idx_spec vmid adt1;
      rely is_int cnt;
      match verify_and_load_loop (Z.to_nat cnt) vmid 0 adt1 with
      | Some (idx', adt') =>
        rely is_int idx';
        when adt2 == set_vm_state_spec vmid VERIFIED adt';
        release_lock_vm_spec vmid adt2
      | _ => None
      end
    else
      when adt2 == panic_spec adt1;
      release_lock_vm_spec vmid adt2.

  Definition alloc_smmu_spec (vmid: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_smmu index; rely is_smmu_cfg cbndx;
    if halt adt then Some adt else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt),
          SPT_ID @ (lock adt), SPT_ID @ (oracle adt), SPT_ID @ (log adt) with
    | LockFalse, vmo, vml0, LockFalse, pto, ptl0 =>
      match H_CalLock ((vmo cpu vml0) ++ vml0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
      | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
        let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((vmo cpu vml0) ++ vml0) in
        let ptl := TEVENT cpu (TSHARED (OPULL SPT_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((pto cpu ptl0) ++ ptl0) in
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
        let spt := CalSPT (spts (shared adt)) (pto cpu ptl0) in
        let vml' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
        let state := vm_state (VS info) in
        rely is_int state;
        if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) && (state =? VERIFIED) then
          Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                    {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
        else
          let ttbr := SMMU_TTBR index cbndx in
          let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (ZMap.init (0, 0))}
                          {spt_pgd_t: (spt_pgd_t spt) # ttbr == (ZMap.init false)}
                          {spt_pmd_t: (spt_pmd_t spt) # ttbr == (ZMap.init (ZMap.init false))} in
          let ptl' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt'))) :: ptl in
          Some adt {tstate: 1} {shared: (shared adt) {spts: spt'} {vminfos: (vminfos (shared adt)) # vmid == info}}
               {log: ((log adt) # id == vml') # SPT_ID == ptl'} {lock: ((lock adt) # id == LockFalse) # SPT_ID == LockFalse}
      | _, _ => None
      end
    | _, _, _, _, _, _ => None
    end.

  Definition assign_smmu_spec (vmid: Z) (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    match pfn, gfn with
    | VZ64 pfn, VZ64 gfn =>
      rely is_vmid vmid; rely is_gfn gfn; rely is_pfn pfn;
      if halt adt then Some adt else
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
                            {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'}
                                                  {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: ((((log adt) # id == vml)# S2PAGE_ID == spl) # ptid == ptl)}
                            {lock: (((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)}
                      else
                        Some adt {tstate: 1} {data_log: (data_log adt) # vmid == (logn + 1)}
                            {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'}
                                                  {s2page: s2p'} {flatmem: fmem'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                            {log: ((((log adt) # id == vml')# S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                            {lock: (((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse) # ptid == LockFalse}
                    | _ => None
                    end
                  end
                else
                  Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: ((log adt) # id == vml) # S2PAGE_ID == spl} {lock: ((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
              else
                if s2_owner page =? vmid then
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
                  Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                       {log: ((log adt) # id == vml') # S2PAGE_ID == spl'} {lock: ((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse}
                else
                  Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                       {log: ((log adt) # id == vml) # S2PAGE_ID == spl} {lock: ((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
            else
              Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                        {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
          else
            Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                {log: (log adt) # id == vml'} {lock: (lock adt) # id == LockFalse}
        | _, _, _ => None
        end
      | _, _, _, _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition map_smmu_spec (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    match iova, pte with
    | VZ64 iova, VZ64 pte =>
      rely is_vmid vmid; rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova; rely is_int64 pte;
      if halt adt then Some adt else
      let id := INFO_ID + vmid in
      let cpu := curid adt in
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
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
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
                       {shared: (shared adt) {spts: spt'} {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                       {log: ((((log adt) # id == vml)# S2PAGE_ID == spl) # SPT_ID == ptl)}
                       {lock: (((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
                else
                  let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page <? EL2_SMMU_CFG_SIZE)
                                then s2p # pfn == (page {s2_count: (s2_count page) + 1}) else s2p) in
                  let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                  Some adt {tstate: 1} {shared: (shared adt) {spts: spt'} {s2page: s2p'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                       {log: ((((log adt) # id == vml') # S2PAGE_ID == spl') # SPT_ID == ptl')}
                       {lock: (((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
              | _ => None
              end
            else
              Some adt {halt: true} {tstate: 0} {shared: (shared adt) {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                       {log: ((log adt) # id == vml) # S2PAGE_ID == spl}
                       {lock: ((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)}
        | _, _, _ => None
        end
      | _, _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition clear_smmu_spec (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (adt: RData) : option RData :=
    match iova with
    | VZ64 iova =>
      rely is_vmid vmid; rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr iova;
      if halt adt then Some adt else
      let id := INFO_ID + vmid in
      let cpu := curid adt in
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
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
          else
            let ttbr := SMMU_TTBR index cbndx in
            let pt := ttbr @ (spt_pt spt) in
            let gfn := iova / PAGE_SIZE in
            let (_, pte) := gfn @ pt in
            rely is_int64 pte;
            match (if pte =? 0 then Some (false, spt) else local_spt_map cbndx index iova 0 spt) with
            | Some (halt', spt') =>
              if halt' then
                Some adt {halt: true} {tstate: 0} {shared: (shared adt) {spts: spt'} {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                        {log: (((log adt) # id == vml) # S2PAGE_ID == spl) # SPT_ID == ptl}
                        {lock: (((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # SPT_ID == (LockOwn true)}
              else
                let pfn := phys_page pte / PAGE_SIZE in
                let page := pfn @ s2p in
                rely is_int (s2_owner page); rely is_int (s2_count page);
                let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page >? 0)
                              then s2p # pfn == (page {s2_count: (s2_count page) - 1}) else s2p) in
                let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OSPT spt')) :: ptl in
                Some adt {tstate: 1} {shared: (shared adt) {spts: spt'} {s2page: s2p'} {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: ((((log adt) # id == vml') # S2PAGE_ID == spl') # SPT_ID == ptl')}
                      {lock: (((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse) # SPT_ID == LockFalse}
            | _ => None
            end
        | _, _, _ => None
        end
      | _, _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition map_io_spec (vmid: Z) (gpa: Z64) (pa: Z64) (adt: RData) : option RData :=
    match gpa, pa with
    | VZ64 gpa, VZ64 pa =>
      rely is_vmid vmid; rely is_addr gpa; rely is_addr pa;
      if halt adt then Some adt else
      let id := INFO_ID + vmid in
      let cpu := curid adt in
      let ptid := NPT_ID + vmid in
      match id @ (lock adt), id @ (oracle adt), id @ (log adt),
            S2PAGE_ID @ (lock adt), S2PAGE_ID @ (log adt), S2PAGE_ID @ (oracle adt),
            ptid @ (lock adt), ptid @ (log adt), ptid @ (oracle adt) with
      | LockFalse, vmo, vml0, LockFalse, spl0, spo, LockFalse, ptl0, pto =>
        match H_CalLock ((vmo cpu vml0) ++ vml0), H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
        | Some (_, LEMPTY, None), Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
          let info := CalVMInfo (vmid @ (vminfos (shared adt))) (vmo cpu vml0) in
          let s2p := CalS2Page (s2page (shared adt)) (spo cpu spl0) in
          let npt := CalNPT (vmid @ (npts (shared adt))) (pto cpu ptl0) in
          let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
          let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
          let vml := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((vmo cpu vml0) ++ vml0) in
          let vml' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) :: vml in
          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
          let state := vm_state (VS info) in
          rely is_int state;
          if state =? READY then
            let gfn := gpa / PAGE_SIZE in
            let pfn := pa / PAGE_SIZE in
            let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
            let page := pfn @ s2p in
            rely is_int (s2_owner page);
            if s2_owner page =? INVALID then
              match local_mmap vmid gpa 3 pte npt with
              | Some (halt', npt') =>
                let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                if halt' then
                  Some adt {halt: true} {tstate: 0}
                       {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'} {npts: (npts (shared adt)) # vmid == npt'}
                                             {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (((log adt) # id == vml) # S2PAGE_ID == spl) # ptid == ptl}
                      {lock: (((lock adt) # id == (LockOwn true)) # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)}
                else
                  Some adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'} {s2page: s2p}
                                                             {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (((log adt) # id == vml') # S2PAGE_ID == spl') # ptid == ptl'}
                      {lock: (((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse) # ptid == LockFalse}
              | _ => None
              end
            else
              Some adt {tstate: 1} {shared: (shared adt) {s2page: s2p} {vminfos: (vminfos (shared adt)) # vmid == info}}
                   {log: ((log adt) # id == vml') # S2PAGE_ID == spl'} {lock: ((lock adt) # id == LockFalse) # S2PAGE_ID == LockFalse}
          else
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == vml} {lock: (lock adt) # id == (LockOwn true)})
        | _, _, _ => None
        end
      | _, _, _, _, _, _, _, _, _ => None
      end
    end.

  Definition is_inc_exe_spec (vmid: Z) (adt: RData) : option (RData * Z) :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    when inc_exe == get_vm_inc_exe_spec vmid adt1;
    rely is_int inc_exe;
    when adt2 == release_lock_vm_spec vmid adt1;
    when ret == check_spec inc_exe adt2;
    Some (adt2, ret).

  Definition save_encrypted_vcpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    when adt1 == encrypt_gp_regs_spec vmid vcpuid adt;
    encrypt_sys_regs_spec vmid vcpuid adt1.

  Definition load_encrypted_vcpu_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    when vm_state == get_vm_state_spec vmid adt1;
    rely is_int vm_state;
    when vcpu_state == get_vcpu_state_spec vmid vcpuid adt1;
    rely is_int vcpu_state;
    if (vm_state =? READY) && (vcpu_state =? READY) then
      when adt2 == decrypt_gp_regs_spec vmid vcpuid adt1;
      when adt3 == decrypt_sys_regs_spec vmid vcpuid adt2;
      when adt4 == set_vm_inc_exe_spec vmid 1 adt3;
      release_lock_vm_spec vmid adt4
    else
      when adt2 == panic_spec adt1;
      release_lock_vm_spec vmid adt2.

  Definition save_encrypt_buf_spec (vmid: Z) (inbuf: Z64) (outbuf: Z64) (adt: RData) : option RData :=
    match inbuf, outbuf with
    | VZ64 inbuf, VZ64 outbuf =>
      let inpfn := inbuf / PAGE_SIZE in
      let outpfn := outbuf / PAGE_SIZE in
      when adt1 == acquire_lock_s2page_spec adt;
      when inowner == get_pfn_owner_spec (VZ64 inpfn) adt1;
      rely is_int inowner;
      when outowner == get_pfn_owner_spec (VZ64 outpfn) adt1;
      rely is_int outowner;
      if (inowner =? vmid) && (outowner =? HOSTVISOR) then
        when adt2 == encrypt_mem_buf_spec vmid (VZ64 inbuf) (VZ64 outbuf) adt1;
        release_lock_s2page_spec adt2
      else
        when adt2 == panic_spec adt1;
        release_lock_s2page_spec adt2
    end.

  Definition load_decrypt_buf_spec (vmid: Z) (inbuf: Z64) (adt: RData) : option RData :=
    match inbuf with
    | VZ64 inbuf =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      let pfn := inbuf / PAGE_SIZE in
      when state == get_vm_state_spec vmid adt1;
      rely is_int state;
      if state =? READY then
        when adt2 == acquire_lock_s2page_spec adt1;
        when owner == get_pfn_owner_spec (VZ64 pfn) adt2;
        rely is_int owner;
        if owner =? HOSTVISOR then
          when adt3 == set_pfn_owner_spec (VZ64 pfn) vmid adt2;
          when adt4 == set_pfn_count_spec (VZ64 pfn) 0 adt3;
          when adt5 == set_pfn_map_spec (VZ64 pfn) (VZ64 INVALID64) adt4;
          when adt6 == clear_pfn_host_spec (VZ64 pfn) adt5;
          when adt7 == decrypt_mem_buf_spec vmid (VZ64 inbuf) adt6;
          when adt8 == release_lock_s2page_spec adt7;
          release_lock_vm_spec vmid adt8
        else
          when adt3 == panic_spec adt2;
          when adt4 == release_lock_s2page_spec adt3;
          release_lock_vm_spec vmid adt4
      else
        when adt2 == panic_spec adt1;
        release_lock_vm_spec vmid adt2
    end.

End BootOpsSpec.

Section BootOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := BootAux_ops) LDATA).

  Fixpoint search_load_info_loop0 (n: nat) (idx: Z) (vmid: Z) (addr: Z) (ret: Z) (adt: RData) :=
    match n with
    | O => Some (idx, ret)
    | S n' =>
      match search_load_info_loop0 n' idx vmid addr ret adt with
      | Some (idx', ret') =>
        rely is_load_idx idx'; rely is_addr ret';
        when' base == get_vm_load_addr_spec vmid idx' adt;
        when' size == get_vm_load_size_spec vmid idx' adt;
        when' remap_addr == get_vm_remap_addr_spec vmid idx' adt;
        rely is_addr base; rely is_addr size; rely is_addr remap_addr;
        if (addr >=? base) && (addr <? base + size) then
          Some (idx' + 1, (addr - base) + remap_addr)
        else
          Some (idx' + 1, ret')
      | _ => None
      end
    end.

  Definition search_load_info_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_int64 addr;
      when adt' == acquire_lock_vm_spec vmid adt;
      when num == get_vm_next_load_idx_spec vmid adt';
      rely (0 <=? num) && (num <=? MAX_LOAD_INFO_NUM);
      match search_load_info_loop0 (Z.to_nat num) 0 vmid addr 0 adt' with
      | Some (idx', ret') =>
        rely is_int idx'; rely is_int64 ret';
        when adt'' == release_lock_vm_spec vmid adt';
        when' res == check64_spec (VZ64 ret') adt'';
        Some (adt'', VZ64 res)
      | _ => None
      end
    end.

  Definition set_vcpu_active_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    when adt' == acquire_lock_vm_spec vmid adt;
    when vm_state == get_vm_state_spec vmid adt';
    rely is_int vm_state;
    when vcpu_state == get_vcpu_state_spec vmid vcpuid adt';
    rely is_int vcpu_state;
    if (vm_state =? VERIFIED) && (vcpu_state =? READY) then
      when adt'' == set_vcpu_state_spec vmid vcpuid ACTIVE adt';
      release_lock_vm_spec vmid adt''
    else
      when adt'' == panic_spec adt';
      release_lock_vm_spec vmid adt''.

  Definition set_vcpu_inactive_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    when adt' == acquire_lock_vm_spec vmid adt;
    when vcpu_state == get_vcpu_state_spec vmid vcpuid adt';
    rely is_int vcpu_state;
    if vcpu_state =? ACTIVE then
      when adt'' == set_vcpu_state_spec vmid vcpuid READY adt';
      release_lock_vm_spec vmid adt''
    else
      when adt'' == panic_spec adt';
      release_lock_vm_spec vmid adt''.

  Definition register_vcpu_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    when adt' == acquire_lock_vm_spec vmid adt;
    when vm_state == get_vm_state_spec vmid adt';
    rely is_int vm_state;
    when vcpu_state == get_vcpu_state_spec vmid vcpuid adt';
    rely is_int vcpu_state;
    if (vm_state =? READY) && (vcpu_state =? UNUSED) then
      when' vcpu == get_shared_vcpu_spec vmid vcpuid adt';
      rely is_int64 vcpu;
      when adt'' == set_vm_vcpu_spec vmid vcpuid (VZ64 vcpu) adt';
      when adt3 == set_vcpu_state_spec vmid vcpuid READY adt'';
      when adt4 == set_shadow_ctxt_spec vmid vcpuid DIRTY (VZ64 INVALID64) adt3;
      release_lock_vm_spec vmid adt4
    else
      when adt'' == panic_spec adt';
      release_lock_vm_spec vmid adt''.

  Definition register_kvm_spec0  (adt: RData) : option (RData * Z) :=
    when vmid, adt' == gen_vmid_spec adt;
    rely is_vmid vmid;
    when adt'' == acquire_lock_vm_spec vmid adt';
    when state == get_vm_state_spec vmid adt'';
    rely is_int state;
    if state =? UNUSED then
      when' kvm == get_shared_kvm_spec vmid adt'';
      rely is_int64 kvm;
      when adt3 == set_vm_kvm_spec vmid (VZ64 kvm) adt'';
      when adt4 == set_vm_state_spec vmid READY adt3;
      when adt5 == release_lock_vm_spec vmid adt4;
      when res == check_spec vmid adt5;
      Some (adt5, res)
    else
      when adt3 == panic_spec adt'';
      when adt4 == release_lock_vm_spec vmid adt3;
      when res == check_spec vmid adt4;
      Some (adt4, res).

  Definition set_boot_info_spec0 (vmid: Z) (load_addr: Z64) (size: Z64) (adt: RData) : option (RData * Z) :=
    match load_addr, size with
    | VZ64 load_addr, VZ64 size =>
      rely is_addr load_addr; rely is_addr size; rely is_vmid vmid;
      when adt' == acquire_lock_vm_spec vmid adt;
      when state == get_vm_state_spec vmid adt';
      rely is_int state;
      if state =? READY then
        when load_idx == get_vm_next_load_idx_spec vmid adt';
        rely is_int load_idx;
        if load_idx <? MAX_LOAD_INFO_NUM then
          when adt2 == set_vm_next_load_idx_spec vmid (load_idx + 1) adt';
          let page_count := (size + 4095) / PAGE_SIZE in
          when' remap_addr, adt3 == alloc_remap_addr_spec (VZ64 page_count) adt2;
          rely is_addr remap_addr;
          when adt4 == set_vm_load_addr_spec vmid load_idx (VZ64 load_addr) adt3;
          when adt5 == set_vm_load_size_spec vmid load_idx (VZ64 size) adt4;
          when adt6 == set_vm_remap_addr_spec vmid load_idx (VZ64 remap_addr) adt5;
          when adt7 == set_vm_mapped_pages_spec vmid load_idx (VZ64 0) adt6;
          when adt8 == release_lock_vm_spec vmid adt7;
          when res == check_spec load_idx adt8;
          Some (adt8, res)
        else
          when adt'' == release_lock_vm_spec vmid adt';
          when res == check_spec load_idx adt'';
          Some (adt'', res)
      else
        when adt'' == panic_spec adt';
        when adt3 == release_lock_vm_spec vmid adt'';
        when res == check_spec 0 adt3;
        Some (adt3, res)
    end.

  Definition remap_vm_image_spec0 (vmid: Z) (pfn: Z64) (load_idx: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_vmid vmid; rely is_load_idx load_idx; rely is_pfn pfn;
      when adt' == acquire_lock_vm_spec vmid adt;
      when state == get_vm_state_spec vmid adt';
      rely is_int state;
      if state =? READY then
        when load_info_cnt == get_vm_next_load_idx_spec vmid adt';
        rely is_int load_info_cnt;
        if load_idx <? load_info_cnt then
          when' size == get_vm_load_size_spec vmid load_idx adt';
          rely is_addr size;
          let page_count := (size + 4095) / PAGE_SIZE in
          when' mapped == get_vm_mapped_pages_spec vmid load_idx adt';
          rely is_addr mapped;
          when' remap_addr == get_vm_remap_addr_spec vmid load_idx adt';
          rely is_addr remap_addr;
          let target := remap_addr + mapped * PAGE_SIZE in
          if mapped <? page_count then
            when adt'' == map_s2pt_spec COREVISOR (VZ64 target) 3 (VZ64 (Z.lor (pfn * PAGE_SIZE)  PAGE_HYP)) adt';
            when adt3 == set_vm_mapped_pages_spec vmid load_idx (VZ64 (mapped + 1)) adt'';
            release_lock_vm_spec vmid adt3
          else
            release_lock_vm_spec vmid adt'
        else
          release_lock_vm_spec vmid adt'
      else
          when adt'' == panic_spec adt';
          release_lock_vm_spec vmid adt''
    end.

  Definition alloc_smmu_spec0 (vmid: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
      when state == get_vm_state_spec vmid adt1;
      rely is_int state;
      if state =? VERIFIED then
        when adt2 == panic_spec adt1;
        when adt3 == init_spt_spec cbndx index adt2;
        release_lock_vm_spec vmid adt3
      else
        when adt2 == init_spt_spec cbndx index adt1;
        release_lock_vm_spec vmid adt2
    else
      when adt2 == init_spt_spec cbndx index adt1;
      release_lock_vm_spec vmid adt2.

  Definition assign_smmu_spec0 (vmid: Z) (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    match pfn, gfn with
    | VZ64 pfn, VZ64 gfn =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
        when state == get_vm_state_spec vmid adt1;
        rely is_int state;
        if state =? VERIFIED then
          when adt2 == panic_spec adt1;
          release_lock_vm_spec vmid adt2
        else
          when adt2 == assign_pfn_to_smmu_spec vmid (VZ64 gfn) (VZ64 pfn) adt1;
          release_lock_vm_spec vmid adt2
      else
        release_lock_vm_spec vmid adt1
    end.

  Definition map_smmu_spec0 (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (pte: Z64) (adt: RData) : option RData :=
    match iova, pte with
    | VZ64 iova, VZ64 pte =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
        when state == get_vm_state_spec vmid adt1;
        rely is_int state;
        if state =? VERIFIED then
          when adt2 == panic_spec adt1;
          when adt3 == update_smmu_page_spec vmid cbndx index (VZ64 iova) (VZ64 pte) adt2;
          release_lock_vm_spec vmid adt3
        else
          when adt2 == update_smmu_page_spec vmid cbndx index (VZ64 iova) (VZ64 pte) adt1;
          release_lock_vm_spec vmid adt2
      else
        when adt2 == update_smmu_page_spec vmid cbndx index (VZ64 iova) (VZ64 pte) adt1;
        release_lock_vm_spec vmid adt2
    end.

  Definition clear_smmu_spec0 (vmid: Z) (cbndx: Z) (index: Z) (iova: Z64) (adt: RData) : option RData :=
    match iova with
    | VZ64 iova =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      if (HOSTVISOR <? vmid) && (vmid <? COREVISOR) then
        when state == get_vm_state_spec vmid adt1;
        rely is_int state;
        if state =? VERIFIED then
          when adt2 == panic_spec adt1;
          when adt3 == unmap_smmu_page_spec cbndx index (VZ64 iova) adt2;
          release_lock_vm_spec vmid adt3
        else
          when adt2 == unmap_smmu_page_spec cbndx index (VZ64 iova) adt1;
          release_lock_vm_spec vmid adt2
      else
        when adt2 == unmap_smmu_page_spec cbndx index (VZ64 iova) adt1;
        release_lock_vm_spec vmid adt2
    end.

  Definition map_io_spec0 (vmid: Z) (gpa: Z64) (pa: Z64) (adt: RData) : option RData :=
    match gpa, pa with
    | VZ64 gpa, VZ64 pa =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      when state == get_vm_state_spec vmid adt1;
      rely is_int state;
      if state =? READY then
        when adt2 == map_vm_io_spec vmid (VZ64 gpa) (VZ64 pa) adt1;
        release_lock_vm_spec vmid adt2
      else
        when adt2 == panic_spec adt1;
        release_lock_vm_spec vmid adt2
    end.

  Definition is_inc_exe_spec0 (vmid: Z) (adt: RData) : option (RData * Z) :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    when inc_exe == get_vm_inc_exe_spec vmid adt1;
    rely is_int inc_exe;
    when adt2 == release_lock_vm_spec vmid adt1;
    when ret == check_spec inc_exe adt2;
    Some (adt2, ret).

  Definition save_encrypted_vcpu_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    when adt1 == encrypt_gp_regs_spec vmid vcpuid adt;
    encrypt_sys_regs_spec vmid vcpuid adt1.

  Definition load_encrypted_vcpu_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_vm_spec vmid adt;
    when vm_state == get_vm_state_spec vmid adt1;
    rely is_int vm_state;
    when vcpu_state == get_vcpu_state_spec vmid vcpuid adt1;
    rely is_int vcpu_state;
    if (vm_state =? READY) && (vcpu_state =? READY) then
      when adt2 == decrypt_gp_regs_spec vmid vcpuid adt1;
      when adt3 == decrypt_sys_regs_spec vmid vcpuid adt2;
      when adt4 == set_vm_inc_exe_spec vmid 1 adt3;
      release_lock_vm_spec vmid adt4
    else
      when adt2 == panic_spec adt1;
      release_lock_vm_spec vmid adt2.

  Definition save_encrypt_buf_spec0 (vmid: Z) (inbuf: Z64) (outbuf: Z64) (adt: RData) : option RData :=
    match inbuf, outbuf with
    | VZ64 inbuf, VZ64 outbuf =>
      let inpfn := inbuf / PAGE_SIZE in
      let outpfn := outbuf / PAGE_SIZE in
      when adt1 == acquire_lock_s2page_spec adt;
      when inowner == get_pfn_owner_spec (VZ64 inpfn) adt1;
      rely is_int inowner;
      when outowner == get_pfn_owner_spec (VZ64 outpfn) adt1;
      rely is_int outowner;
      if (inowner =? vmid) && (outowner =? HOSTVISOR) then
        when adt2 == encrypt_mem_buf_spec vmid (VZ64 inbuf) (VZ64 outbuf) adt1;
        release_lock_s2page_spec adt2
      else
        when adt2 == panic_spec adt1;
        release_lock_s2page_spec adt2
    end.

  Definition load_decrypt_buf_spec0 (vmid: Z) (inbuf: Z64) (adt: RData) : option RData :=
    match inbuf with
    | VZ64 inbuf =>
      when adt1 == acquire_lock_vm_spec vmid adt;
      let pfn := inbuf / PAGE_SIZE in
      when state == get_vm_state_spec vmid adt1;
      rely is_int state;
      if state =? READY then
        when adt2 == acquire_lock_s2page_spec adt1;
        when owner == get_pfn_owner_spec (VZ64 pfn) adt2;
        rely is_int owner;
        if owner =? HOSTVISOR then
          when adt3 == set_pfn_owner_spec (VZ64 pfn) vmid adt2;
          when adt4 == set_pfn_count_spec (VZ64 pfn) 0 adt3;
          when adt5 == set_pfn_map_spec (VZ64 pfn) (VZ64 INVALID64) adt4;
          when adt6 == clear_pfn_host_spec (VZ64 pfn) adt5;
          when adt7 == decrypt_mem_buf_spec vmid (VZ64 inbuf) adt6;
          when adt8 == release_lock_s2page_spec adt7;
          release_lock_vm_spec vmid adt8
        else
          when adt3 == panic_spec adt2;
          when adt4 == release_lock_s2page_spec adt3;
          release_lock_vm_spec vmid adt4
      else
        when adt2 == panic_spec adt1;
        release_lock_vm_spec vmid adt2
    end.

  Inductive search_load_info_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | search_load_info_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr res
      (Hinv: high_level_invariant labd)
      (Hspec: search_load_info_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      search_load_info_spec_low_step s WB ((Vint vmid)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive set_vcpu_active_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_vcpu_active_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: set_vcpu_active_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      set_vcpu_active_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive set_vcpu_inactive_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_vcpu_inactive_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: set_vcpu_inactive_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      set_vcpu_inactive_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive register_vcpu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | register_vcpu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: register_vcpu_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      register_vcpu_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive register_kvm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | register_kvm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'  res
      (Hinv: high_level_invariant labd)
      (Hspec: register_kvm_spec0 labd = Some (labd', (Int.unsigned res))):
      register_kvm_spec_low_step s WB nil (m'0, labd) (Vint res) (m'0, labd').

  Inductive set_boot_info_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_boot_info_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid load_addr size res
      (Hinv: high_level_invariant labd)
      (Hspec: set_boot_info_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned load_addr)) (VZ64 (Int64.unsigned size)) labd = Some (labd', Int.unsigned res)):
      set_boot_info_spec_low_step s WB ((Vint vmid)::(Vlong load_addr)::(Vlong size)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Inductive remap_vm_image_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | remap_vm_image_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn load_idx
      (Hinv: high_level_invariant labd)
      (Hspec: remap_vm_image_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (Int.unsigned load_idx) labd = Some labd'):
      remap_vm_image_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::(Vint load_idx)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive verify_and_load_images_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | verify_and_load_images_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: verify_and_load_images_spec (Int.unsigned vmid) labd = Some labd'):
      verify_and_load_images_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive alloc_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      alloc_smmu_spec_low_step s WB ((Vint vmid)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive assign_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | assign_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid pfn gfn
      (Hinv: high_level_invariant labd)
      (Hspec: assign_smmu_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) labd = Some labd'):
      assign_smmu_spec_low_step s WB ((Vint vmid)::(Vlong pfn)::(Vlong gfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive map_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid cbndx index iova pte
      (Hinv: high_level_invariant labd)
      (Hspec: map_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      map_smmu_spec_low_step s WB ((Vint vmid)::(Vint cbndx)::(Vint index)::(Vlong iova)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive clear_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid cbndx index iova
      (Hinv: high_level_invariant labd)
      (Hspec: clear_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) labd = Some labd'):
      clear_smmu_spec_low_step s WB ((Vint vmid)::(Vint cbndx)::(Vint index)::(Vlong iova)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive map_io_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_io_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid gpa pa
      (Hinv: high_level_invariant labd)
      (Hspec: map_io_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gpa)) (VZ64 (Int64.unsigned pa)) labd = Some labd'):
      map_io_spec_low_step s WB ((Vint vmid)::(Vlong gpa)::(Vlong pa)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive is_inc_exe_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | is_inc_exe_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid res
      (Hinv: high_level_invariant labd)
      (Hspec: is_inc_exe_spec (Int.unsigned vmid) labd = Some (labd', (Int.unsigned res))):
      is_inc_exe_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Inductive save_encrypted_vcpu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | save_encrypted_vcpu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: save_encrypted_vcpu_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      save_encrypted_vcpu_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive load_encrypted_vcpu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | load_encrypted_vcpu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: load_encrypted_vcpu_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      load_encrypted_vcpu_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive save_encrypt_buf_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | save_encrypt_buf_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid inbuf outbuf
      (Hinv: high_level_invariant labd)
      (Hspec: save_encrypt_buf_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned inbuf)) (VZ64 (Int64.unsigned outbuf)) labd = Some labd'):
      save_encrypt_buf_spec_low_step s WB ((Vint vmid)::(Vlong inbuf)::(Vlong outbuf)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive load_decrypt_buf_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | load_decrypt_buf_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid inbuf
      (Hinv: high_level_invariant labd)
      (Hspec: load_decrypt_buf_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned inbuf)) labd = Some labd'):
      load_decrypt_buf_spec_low_step s WB ((Vint vmid)::(Vlong inbuf)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition search_load_info_spec_low: compatsem LDATAOps :=
      csem search_load_info_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tint64.

    Definition set_vcpu_active_spec_low: compatsem LDATAOps :=
      csem set_vcpu_active_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition set_vcpu_inactive_spec_low: compatsem LDATAOps :=
      csem set_vcpu_inactive_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition register_vcpu_spec_low: compatsem LDATAOps :=
      csem register_vcpu_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition register_kvm_spec_low: compatsem LDATAOps :=
      csem register_kvm_spec_low_step (type_of_list_type nil) Tint32.

    Definition set_boot_info_spec_low: compatsem LDATAOps :=
      csem set_boot_info_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tint32.

    Definition remap_vm_image_spec_low: compatsem LDATAOps :=
      csem remap_vm_image_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::nil)) Tvoid.

    Definition verify_and_load_images_spec_low: compatsem LDATAOps :=
      csem verify_and_load_images_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition alloc_smmu_spec_low: compatsem LDATAOps :=
      csem alloc_smmu_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition assign_smmu_spec_low: compatsem LDATAOps :=
      csem assign_smmu_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition map_smmu_spec_low: compatsem LDATAOps :=
      csem map_smmu_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition clear_smmu_spec_low: compatsem LDATAOps :=
      csem clear_smmu_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::Tint64::nil)) Tvoid.

    Definition map_io_spec_low: compatsem LDATAOps :=
      csem map_io_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition is_inc_exe_spec_low: compatsem LDATAOps :=
      csem is_inc_exe_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition save_encrypted_vcpu_spec_low: compatsem LDATAOps :=
      csem save_encrypted_vcpu_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition load_encrypted_vcpu_spec_low: compatsem LDATAOps :=
      csem load_encrypted_vcpu_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition save_encrypt_buf_spec_low: compatsem LDATAOps :=
      csem save_encrypt_buf_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition load_decrypt_buf_spec_low: compatsem LDATAOps :=
      csem load_decrypt_buf_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tvoid.

  End WITHMEM.

End BootOpsSpecLow.

```
