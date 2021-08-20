# TrapHandlerRefine

```coq
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import ZSet.
Require Import ListLemma2.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import RealParams.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import LayerCalculusLemma.
Require Import TacticsForTesting.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import TrapHandler.Layer.
Require Import RData.
Require Import TrapHandler.Spec.
Require Import TrapHandlerRaw.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import AbstractMachine.Spec.
Require Import TrapHandlerRaw.Spec.
Require Import TrapDispatcher.Spec.
Require Import FaultHandler.Spec.
Require Import MemHandler.Spec.
Require Import MmioOps.Spec.
Require Import BootOps.Spec.
Require Import MemoryOps.Spec.
Require Import MemManager.Spec.
Require Import NPTWalk.Spec.
Require Import NPTOps.Spec.
Require Import MmioSPTWalk.Spec.
Require Import MmioSPTOps.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

    Fixpoint local_mmap_loop_h (n: nat) (gfn: Z) (pfn: Z) (level: Z) (pte: Z) (pt': ZMap.t (Z*Z*Z)) :=
      match n with
      | O => (gfn, pfn, pt')
      | S m =>
        match local_mmap_loop_h m gfn pfn level pte pt' with
        | (gfn', pfn', pt0) => (gfn'+1, pfn'+1, ZMap.set gfn' (pfn', level, pte) pt0)
        end
      end.

    Definition local_mmap_h (vmid: Z) (addr: Z) (level: Z) (pte: Z) (npt: NPT) :=
      if level =? 2 then
        let gfn := addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD in
        let pfn := (phys_page pte) / PAGE_SIZE in
        let pgd_next' := (if (pgd_index addr) @ (pgd_t npt) then (pt_pgd_next npt) else (pt_pgd_next npt) + PAGE_SIZE) in
        let pud_next' := (if (pud_index addr) @ ((pgd_index addr) @ (pud_t npt))
                          then (pt_pud_next npt) else (pt_pud_next npt) + PAGE_SIZE) in
        if (pgd_next' <=? pud_start vmid) && (pud_next'  <=? pmd_start vmid) then
          match local_mmap_loop_h (Z.to_nat PTRS_PER_PMD) gfn pfn 2 pte (pt npt) with
          | (_, _, pt') =>
            let npt' := npt {pt: pt'} {pgd_t: ZMap.set (pgd_index addr) true (pgd_t npt)}
                            {pud_t: (pud_t npt) # (pgd_index addr) == (((pgd_index addr) @ (pud_t npt)) # (pud_index addr) == true)}
                            {pmd_t: (pmd_t npt) # (pgd_index addr) ==
                                    (((pgd_index addr) @ (pmd_t npt)) # (pud_index addr) ==
                                      (((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt))) # (pmd_index addr) == false))}
                            {pt_pgd_next: pgd_next'} {pt_pud_next: pud_next'}
            in
            (false, npt')
          end
        else (true, npt)
      else
        let gfn := addr / PAGE_SIZE in
        let pfn := (phys_page pte) / PAGE_SIZE in
        match gfn @ (pt npt) with
        | (pfn0, level0, pte0) =>
          if level0 =? 2 then (true, npt)
          else
            let pgd_next' := (if (pgd_index addr) @ (pgd_t npt) then (pt_pgd_next npt) else (pt_pgd_next npt) + PAGE_SIZE) in
            let pud_next' := (if (pud_index addr) @ ((pgd_index addr) @ (pud_t npt))
                              then (pt_pud_next npt) else (pt_pud_next npt) + PAGE_SIZE) in
            let pmd_next' := (if (pmd_index addr) @ ((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt)))
                              then (pt_pmd_next npt) else (pt_pmd_next npt) + PAGE_SIZE) in
            if (pgd_next' <=? pud_start vmid) && (pud_next'  <=? pmd_start vmid) && (pmd_next' <=? pool_end vmid) then
              match local_mmap_loop_h 1 gfn pfn 3 pte (pt npt) with
              | (_, _, pt') =>
                let npt' := npt {pt: pt'}
                                {pgd_t: (pgd_t npt) # (pgd_index addr) == true}
                                {pud_t: (pud_t npt) # (pgd_index addr) ==
                                        (((pgd_index addr) @ (pud_t npt)) # (pud_index addr) == true)}
                                {pmd_t: (pmd_t npt) # (pgd_index addr) ==
                                        (((pgd_index addr) @ (pmd_t npt)) # (pud_index addr) ==
                                        (((pud_index addr) @ ((pgd_index addr) @ (pmd_t npt))) # (pmd_index addr) == true))}
                                {pt_pgd_next: pgd_next'} {pt_pud_next: pud_next'} {pt_pmd_next: pmd_next'}
                in
                (false, npt')
              end
            else(true, npt)
        end.

    Definition local_spt_map_h (cbndx: Z) (index: Z) (addr: Z) (pte: Z) (spt: SPT) :=
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
          (false, spt')
        else (true, spt)
      end.

    Definition local_map_host addr sdt :=
      let ptid := NPT_ID in
      let pfn := addr / PAGE_SIZE in
      let page := pfn @ (s2page sdt) in
      if (s2_owner page =? INVALID) || (s2_owner page =? HOSTVISOR) || (s2_count page >? 0) then
        let pte := (if s2_owner page =? INVALID then Z.lor (pfn * PAGE_SIZE) (Z.lor PAGE_S2_DEVICE S2_RDWR)
                    else Z.lor (pfn * PAGE_SIZE) PAGE_S2_KERNEL) in
        match local_mmap_h HOSTVISOR addr 3 pte (HOSTVISOR @ (npts sdt)) with
        | (halt', npt') =>
          if halt' then
            (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {hlock: ((hlock sdt) # S2PAGE_ID == false) # ptid == false}, true,
             Some (s2page sdt), Some npt')
          else
            (sdt {npts: (npts sdt) # HOSTVISOR == npt'}, false,
             Some (s2page sdt), Some npt')
        end
      else (sdt {hlock: (hlock sdt) # S2PAGE_ID == false}, true, Some (s2page sdt), None).

    Definition local_set_vcpu_active vmid vcpuid sdt :=
      let info := vmid @ (vminfos sdt) in
      match vm_state (VS info), vcpuid @ (vm_vcpu_state (VS info)) with
      | vms, vcpus =>
        if (vms =? VERIFIED) && (vcpus =? READY) then
          let info' := info {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == ACTIVE} in
          (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, Some info')
        else
          (sdt, true, Some info)
        end.

    Definition local_set_vcpu_inactive vmid vcpuid sdt :=
      let info := vmid @ (vminfos sdt) in
      let vcpus := vcpuid @ (vm_vcpu_state (VS info)) in
      if vcpus =? ACTIVE then
        let info' := info {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == READY} in
        (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, Some info')
      else
        (sdt, true, Some info).
    Definition local_register_vcpu vmid vcpuid sdt :=
      let info := vmid @ (vminfos sdt) in
      match vm_state (VS info), vcpuid @ (vm_vcpu_state (VS info)) with
      | vms, vcpus =>
        if (vms =? READY) && (vcpus =? UNUSED) then
          let vcpu := shared_vcpu vmid vcpuid in
          let info' := info {vm_vcpu: (vm_vcpu (VS info)) # vcpuid == vcpu} {vm_vcpu_state: (vm_vcpu_state (VS info)) # vcpuid == READY} in
          (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, Some info')
        else
          (sdt, true, Some info)
      end.

    Definition local_gen_vmid sdt :=
      let vmid := next_vmid (core_data sdt) in
      let core' := (core_data sdt) {next_vmid: vmid + 1} in
      (sdt {core_data: core'}, core').

    Definition local_register_kvm vmid sdt :=
      let info := vmid @ (vminfos sdt) in
      let vms := vm_state (VS info) in
      if vms =? UNUSED then
        let kvm := shared_kvm vmid in
        let info' := info {vm_kvm: kvm} {vm_state: READY} in
        (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, Some info')
      else
        (sdt, true, Some info).

    Definition local_set_boot_info vmid load_addr size sdt :=
      let info := vmid @ (vminfos sdt) in
      let core := core_data sdt in
      let vms := vm_state (VS info) in
      if vms =? READY then
        let load_idx := vm_next_load_info (VB info) in
        if load_idx <? MAX_LOAD_INFO_NUM then
          let pgnum := (size + 4095) / PAGE_SIZE in
          let remap := next_remap_ptr core in
          if remap + pgnum * PAGE_SIZE <? REMAP_END then
            let core' := core {next_remap_ptr : remap + pgnum * PAGE_SIZE} in
            let info' := info {vm_next_load_info: load_idx + 1}
                              {vm_load_addr: (vm_load_addr (VB info)) # load_idx == load_addr}
                              {vm_load_size: (vm_load_size (VB info)) # load_idx == size}
                              {vm_remap_addr: (vm_remap_addr (VB info)) # load_idx == remap}
                              {vm_mapped_pages: (vm_mapped_pages (VB info)) # load_idx == 0} in
            (sdt {vminfos: (vminfos sdt) # vmid == info'} {core_data: core'}, false, Some info', Some core')
          else
            (sdt, true, Some info, Some core)
        else
          (sdt, false, Some info, None)
      else
        (sdt, true, Some info, None).

    Definition local_remap_vm_image vmid pfn load_idx sdt :=
      let info := vmid @ (vminfos sdt) in
      let npt := COREVISOR @ (npts sdt) in
      let vms := vm_state (VS info) in
      if vms =? READY then
        let load_cnt := vm_next_load_info (VB info) in
        if load_idx <? load_cnt then
          match load_idx @ (vm_load_size (VB info)), load_idx @ (vm_remap_addr (VB info)), load_idx @ (vm_mapped_pages (VB info)) with
          | size, remap, mapped =>
            let pgnum := (size + 4095) / PAGE_SIZE in
            let target := remap + mapped * PAGE_SIZE in
            if mapped <? pgnum then
              let (halt', npt') := local_mmap_h COREVISOR target 3 (Z.lor (pfn * PAGE_SIZE) PAGE_HYP) npt in
              if halt' then
                (sdt {hlock: ((hlock sdt) # (INFO_ID + vmid) == false) # (NPT_ID + COREVISOR) == false}
                     {npts: (npts sdt) # COREVISOR == npt'}, true, Some info, Some npt')
              else
                let info' := info {vm_mapped_pages: (vm_mapped_pages (VB info)) # load_idx == (mapped + 1)} in
                (sdt {vminfos: (vminfos sdt) # vmid == info'}
                     {npts: (npts sdt) # COREVISOR == npt'}, false, Some info', Some npt')
            else
              (sdt, false, Some info, None)
          end
        else
          (sdt, false, Some info, None)
      else
        (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, Some info, None).

    Definition local_clear_vm_page vmid pfn sdt :=
      let s2p := s2page sdt in
      let fmem := flatmem sdt in
      let page := pfn @ s2p in
      if s2_owner page =? vmid then
        let page' := mkS2Page HOSTVISOR 0 (pfn + SMMU_HOST_OFFSET) in
        let s2p' := s2p # pfn == page' in
        let fmem' := fmem # pfn == 0 in
        (sdt {s2page: s2p'} {flatmem: fmem'}, Some s2p', Some fmem')

      else
        (sdt, Some s2p, None).

    Definition local_assign_pfn_to_vm vmid gfn pfn (dorc: Z -> Z) logn sdt :=
      let s2p := s2page sdt in
      let npt := HOSTVISOR @ (npts sdt) in
      let fmem := flatmem sdt in
      let page := pfn @ s2p in
      if s2_owner page =? HOSTVISOR then
        if s2_count page =? 0 then
          let s2p' := s2p # pfn == (mkS2Page vmid 0 gfn) in
          let fmem' := fmem # pfn == (dorc logn) in
          match pfn @ (pt npt) with
          | (pfn', level, pte) =>
            match (if (if phys_page pte =? 0 then 0 else level) =? 0 then (false, npt)
                  else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
            | (halt', npt') =>
              if halt' then
                (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # NPT_ID == false} {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'},
                  true, logn, Some s2p', Some npt', None)
              else
                (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
                  true, logn + 1, Some s2p', Some npt', Some fmem')
            end
          end
        else
          (sdt {hlock: (hlock sdt) # S2PAGE_ID == false}, true, logn, Some s2p, None, None)
      else
        if (s2_owner page =? vmid) && (gfn =? s2_gfn page) then
          if s2_count page =? INVALID then
            let page' := page {s2_count: 0} in
            let s2p' := s2p # pfn == page in
            (sdt {s2page: s2p'}, false, logn, Some s2p', None, None)
          else
            (sdt, false, logn, Some s2p, None, None)
        else
          (sdt {hlock: (hlock sdt) # S2PAGE_ID == false}, true, logn, Some s2p, None, None).

    Definition local_map_pfn_vm vmid addr pte level sdt :=
      let npt := vmid @ (npts sdt) in
      let paddr := phys_page pte in
      let perm := PAGE_S2_KERNEL in
      let pte' := (if level =? 2 then Z.land (Z.lor paddr perm) NOT_PMD_TABLE_BIT else Z.lor paddr perm) in
      let level' := (if level =? 2 then 2 else 3) in
      let (halt', npt') := local_mmap_h vmid addr level' pte' npt in
      if halt' then
        (sdt {hlock: (hlock sdt) # (NPT_ID + vmid) == false} {npts: (npts sdt) # vmid == npt'}, true, Some npt')
      else
        (sdt {npts: (npts sdt) # vmid == npt'}, false, Some npt').

    Definition local_map_vm_io vmid gpa pa sdt :=
      let s2p := s2page sdt in
      let npt := vmid @ (npts sdt) in
      let gfn := gpa / PAGE_SIZE in
      let pfn := pa / PAGE_SIZE in
      let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
      let page := pfn @ s2p in
      if s2_owner page =? INVALID then
        let (halt', npt') := local_mmap_h vmid gpa 3 pte npt in
        if halt' then
          (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # (NPT_ID + vmid) == false} {npts: (npts sdt) # vmid == npt'},
          true, Some s2p, Some npt')
        else
          (sdt {npts: (npts sdt) # vmid == npt'}, false, Some s2p, Some npt')
      else
        (sdt, false, Some s2p, None).

    Definition local_grant_vm_page vmid pfn sdt :=
      let s2p := s2page sdt in
      let page := pfn @ s2p in
      let s2p' := (if (s2_owner page =? vmid) && (s2_count page <? MAX_SHARE_COUNT)
                  then s2p # pfn == (page {s2_count: (s2_count page) + 1})
                  else s2p) in
      (sdt {s2page: s2p'}, Some s2p').

    Definition local_revoke_vm_page vmid pfn (dorc: Z -> Z) logn sdt :=
      let s2p := s2page sdt in
      let npt := HOSTVISOR @ (npts sdt) in
      let fmem := flatmem sdt in
      let page := pfn @ s2p in
      if (s2_owner page =? vmid) && (s2_count page >? 0) then
        let s2p' := s2p # pfn == (page {s2_count: (s2_count page) - 1}) in
        if s2_count page =? 1 then
          let fmem' := fmem # pfn == (dorc logn) in
          match pfn @ (pt npt) with
          | (pfn', level, pte) =>
            match (if (if phys_page pte =? 0 then 0 else level) =? 0 then (false, npt)
                  else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
            | (halt', npt') =>
              if halt' then
                (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # NPT_ID == false} {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'},
                true, logn, Some s2p', Some npt', None)
              else
                (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
                true, logn + 1, Some s2p', Some npt', Some fmem')
            end
          end
        else
          (sdt {s2page: s2p'}, false, logn, Some s2p', None, None)
      else
        (sdt, false, logn, Some s2p, None, None).

    Definition local_free_smmu_pgd cbndx index sdt :=
      let vmid := (smmu_id index cbndx) @ (smmu_vmid sdt) in
      if vmid =? INVALID then
        (sdt, false, Some (smmu_vmid sdt), None)
      else
        let info := vmid @ (vminfos sdt) in
        if vm_state (VS info) =? POWEROFF then
          let smmu' := (smmu_vmid sdt) # vmid == INVALID in
          (sdt {smmu_vmid: smmu'}, false, Some smmu', Some info)
        else
          (sdt {hlock: (hlock sdt) # SMMU_ID == false}, true, Some (smmu_vmid sdt), Some info).

    Definition local_alloc_smmu_pgd cbndx vmid index num sdt :=
      if cbndx <? num then
        let target := (smmu_id index cbndx) @ (smmu_vmid sdt) in
        if target =? INVALID then
          let smmu' := (smmu_vmid sdt) # (smmu_id index cbndx) == vmid in
          let ttbr := SMMU_TTBR index cbndx in
          let spt := spts sdt in
          let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (ZMap.init (0, 0))}
                          {spt_pgd_t: (spt_pgd_t spt) # ttbr == (ZMap.init false)}
                          {spt_pmd_t: (spt_pmd_t spt) # ttbr == (ZMap.init (ZMap.init false))} in
          (sdt {smmu_vmid: smmu'} {spts: spt'}, false, Some smmu', Some spt')
        else
          (sdt, false, Some (smmu_vmid sdt), None)
      else
        (sdt {hlock: (hlock sdt) # SMMU_ID == false}, true, Some (smmu_vmid sdt), None).

    Definition local_smmu_assign_page cbndx index pfn gfn dorc logn sdt :=
      let smmu := smmu_vmid sdt in
      let vmid := (smmu_id index cbndx) @ (smmu_vmid sdt) in
      let info := vmid @ (vminfos sdt) in
      let s2p := s2page sdt in
      let npt := HOSTVISOR @ (npts sdt) in
      let fmem := flatmem sdt in
      if vmid =? INVALID then
        (sdt, false, logn, Some smmu, None, None, None, None)
      else
        let state := vm_state (VS info) in
        if is_vm vmid then
          if state =? VERIFIED then
            (sdt {hlock: ((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false}, true, logn, Some smmu, Some info, None, None, None)
          else
            let page := pfn @ s2p in
            if s2_owner page =? HOSTVISOR then
              if s2_count page =? 0 then
                let s2p' := s2p # pfn == (mkS2Page vmid INVALID gfn) in
                let fmem' := fmem # pfn == (dorc logn) in
                match pfn @ (pt npt) with
                | (_, level, pte) =>
                  match (if (if phys_page pte =? 0 then 0 else level) =? 0 then (false, npt)
                         else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
                  | (halt', npt') =>
                    if halt' then
                      (sdt {hlock: ((((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # NPT_ID == false}
                           {npts: (npts sdt) # HOSTVISOR == npt'},
                       true, logn, Some smmu, Some info, Some s2p, Some npt', None)
                    else
                      (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'}, false, logn + 1, Some smmu, Some info, Some s2p', Some npt', Some fmem')
                  end
                end
              else
                (sdt {hlock: (((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false}, true, logn, Some smmu, Some info, Some s2p, None, None)
            else
              if s2_owner page =? vmid then
                (sdt, false, logn, Some smmu, Some info, Some s2p, None, None)
              else
                (sdt {hlock: (((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false}, true, logn, Some smmu, Some info, Some s2p, None, None)
        else
          (sdt, false, logn, Some smmu, Some info, None, None, None).

    Definition local_smmu_map_page cbndx index iova pte sdt :=
      let smmu := smmu_vmid sdt in
      let vmid := (smmu_id index cbndx) @ smmu in
      let info := vmid @ (vminfos sdt) in
      let s2p := s2page sdt in
      let spt := spts sdt in
      if vmid =? INVALID then
        (sdt, false, Some smmu, None, None, None)
      else
        let state := vm_state (VS info) in
        if is_vm vmid && (state =? VERIFIED) then
          (sdt {hlock: ((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false}, true, Some smmu, Some info, None, None)
        else
          let pfn := phys_page pte / PAGE_SIZE in
          let gfn := iova / PAGE_SIZE in
          let page := pfn @ s2p in
          if (vmid =? s2_owner page) && (gfn =? s2_gfn page) then
            let (halt', spt') := local_spt_map_h cbndx index iova pte spt in
            if halt' then
              (sdt {hlock: ((((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # SPT_ID == false}
                   {spts: spt'}, true, Some smmu, Some info, Some s2p, Some spt')
            else
              let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page <? EL2_SMMU_CFG_SIZE)
                           then s2p # pfn == (page {s2_count: (s2_count page) + 1}) else s2p) in
              (sdt {s2page: s2p'} {spts: spt'}, false, Some smmu, Some info, Some s2p', Some spt')
          else
            (sdt {hlock: (((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false},
             true, Some smmu, Some info, Some s2p, None).

    Definition local_smmu_clear iova cbndx index sdt :=
      let smmu := smmu_vmid sdt in
      let vmid := (smmu_id index cbndx) @ smmu in
      let info := vmid @ (vminfos sdt) in
      let s2p := s2page sdt in
      let spt := spts sdt in
      if vmid =? INVALID then
        (sdt, false, Some smmu, None, None, None)
      else
        let state := vm_state (VS info) in
        if is_vm vmid && (state =? VERIFIED) then
          (sdt {hlock: ((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false}, true, Some smmu, Some info, None, None)
        else
          let ttbr := SMMU_TTBR index cbndx in
          let pt := ttbr @ (spt_pt spt) in
          let gfn := iova / PAGE_SIZE in
          let (pfn, pte) := gfn @ pt in
          let (halt', spt') :=  (if pte =? 0 then (false, spt) else local_spt_map_h cbndx index iova 0 spt) in
          if halt' then
            (sdt {hlock: ((((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # SPT_ID == false}
                  {spts: spt'}, true, Some smmu, Some info, Some s2p, Some spt')
          else
            let pfn0 := phys_page pte / PAGE_SIZE in
            let page := pfn0 @ s2p in
            let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page >? 0)
                          then s2p # pfn == (page {s2_count: (s2_count page) - 1}) else s2p) in
            (sdt {s2page: s2p'} {spts: spt'}, false, Some smmu, Some info, Some s2p', Some spt').
    (* TODO: emulate_mmio_spec *)


    Fixpoint CalStateH (slog: SingleLog) (sdt: Shared) :=
      match slog with
      | nil => sdt
      | (SEVENT _ e) :: slog' =>
        let sdt' := CalStateH slog' sdt in
        match e with
        | OMAP_HOST addr =>
          match local_map_host addr sdt with
          | (sdt', _, _, _) => sdt'
          end
        | _ => sdt
        end
      end.

    Definition query_oracle adt :=
      adt {slog: ((soracle adt) (curid adt) (slog adt)) ++ (slog adt)} {shared: CalStateH ((soracle adt) (curid adt) (slog adt)) (shared adt)}.

    Definition map_page_host_spec_h addr adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let ptid := NPT_ID in
      let log' := SEVENT (curid adt) (OMAP_HOST addr) :: (slog adt) in
      rely ptid @ (hlock (shared adt)); rely S2PAGE_ID @ (hlock (shared adt));
      match local_map_host addr (shared adt) with
      | (sdt', halt', _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition el2_free_smmu_pgd_spec_h cbndx index adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let vmid := (smmu_id index cbndx) @ (smmu_vmid (shared adt)) in
      let log' := SEVENT (curid adt) (OSMMU_FREE cbndx index 0) :: (slog adt) in
      rely SMMU_ID @ (hlock (shared adt)); rely (INFO_ID + vmid) @ (hlock (shared adt));
      match local_free_smmu_pgd cbndx index (shared adt) with
      | (sdt', halt', _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition el2_alloc_smmu_pgd_spec_h cbndx vmid index adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let num := index @ (smmu_dev_context_banks (smmu_conf adt)) in
      let log' := SEVENT (curid adt) (OSMMU_ALLOC cbndx vmid (index + num)) :: (slog adt) in
      rely SMMU_ID @ (hlock (shared adt)); rely SPT_ID @ (hlock (shared adt));
      match local_alloc_smmu_pgd cbndx vmid index num (shared adt) with
      | (sdt', halt', _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition smmu_assign_page_spec_h cbndx index pfn gfn adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let vmid := (smmu_id index cbndx) @ (smmu_vmid (shared adt)) in
      (* TODO OSMMU_ASSIGN cbndx index pfn gfn ((doracle adt) vmid) (vmid @ (data_log adt)) *)
      let log' := SEVENT (curid adt) (OSMMU_ALLOC cbndx index 0) :: (slog adt) in
      rely SMMU_ID @ (hlock (shared adt)); rely (INFO_ID + vmid) @ (hlock (shared adt));
      rely NPT_ID @ (hlock (shared adt)); rely S2PAGE_ID @ (hlock (shared adt));
      match local_smmu_assign_page cbndx index pfn gfn ((doracle adt) vmid) (vmid @ (data_log adt)) (shared adt) with
      | (sdt', halt', logn', _, _, _, _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'} {data_log: (data_log adt)}
      end.

    Definition smmu_map_page_spec_h cbndx index iova pte adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let vmid := (smmu_id index cbndx) @ (smmu_vmid (shared adt)) in
      (* TODO OSMMU_MAP cbndx index iova pte *)
      let log' := SEVENT (curid adt) (OSMMU_ALLOC cbndx index 0) :: (slog adt) in
      rely SMMU_ID @ (hlock (shared adt)); rely (INFO_ID + vmid) @ (hlock (shared adt));
      rely SPT_ID @ (hlock (shared adt)); rely S2PAGE_ID @ (hlock (shared adt));
      match local_smmu_map_page cbndx index iova pte (shared adt) with
      | (sdt', halt', _, _, _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition el2_arm_lpae_iova_to_phys_spec_h iova cbndx index adt0 :=
      if halt adt0 then Some (adt0, 0) else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) OSMMU_GET :: (slog adt) in
      rely SPT_ID @ (hlock (shared adt));
      let ttbr := SMMU_TTBR index cbndx in
      let pt := ttbr @ (spt_pt (spts (shared adt)))in
      let gfn := iova / PAGE_SIZE in
      match gfn @ pt with
      | (pfn, pte) =>
        Some (adt {slog: log'}, phys_page pte + (Z.land iova 4095))
      end.

    Definition el2_arm_lpae_clear_spec_h iova cbndx index adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let vmid := (smmu_id index cbndx) @ (smmu_vmid (shared adt)) in
      let log' := SEVENT (curid adt) (OSMMU_CLEAR iova cbndx index) :: (slog adt) in
      rely SMMU_ID @ (hlock (shared adt)); rely (INFO_ID + vmid) @ (hlock (shared adt));
      rely SPT_ID @ (hlock (shared adt)); rely S2PAGE_ID @ (hlock (shared adt));
      match local_smmu_clear iova cbndx index (shared adt) with
      | (sdt', halt', _, _, _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Fixpoint search_load_info_loop_h (n: nat) (idx: Z) (addr: Z) (ret: Z) (binfo: BootInfo) :=
      match n with
      | O => (idx, ret)
      | S n' =>
        match search_load_info_loop_h n' idx addr ret binfo with
        | (idx', ret') =>
          match idx' @ (vm_load_addr binfo), idx' @ (vm_load_size binfo), idx' @ (vm_remap_addr binfo) with
          | base, size, remap =>
            if (addr >=? base) && (addr <? base + size) then
              (idx' + 1, (addr - base) + remap)
            else
              (idx' + 1, ret')
          end
        end
      end.

    Definition search_load_info_spec_h vmid addr adt0 :=
      if halt adt0 then Some (adt0, 0) else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OVM_GET vmid) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt));
      let info := vmid @ (vminfos (shared adt)) in
      let num := vm_next_load_info (VB info) in
      let (_, ret) := search_load_info_loop_h (Z.to_nat num) 0 addr 0 (VB info) in
      Some (adt {slog: log'}, ret).

    Definition set_vcpu_active_spec_h vmid vcpuid adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OVM_ACTIVE vmid vcpuid) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt));
      match local_set_vcpu_active vmid vcpuid (shared adt) with
      | (sdt', halt', _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition set_vcpu_inactive_spec_h vmid vcpuid adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OVM_ACTIVE vmid vcpuid) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt));
      match local_set_vcpu_active vmid vcpuid (shared adt) with
      | (sdt', halt', _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition register_vcpu_spec_h vmid vcpuid adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OREG_VCPU vmid vcpuid) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt));
      match local_register_vcpu vmid vcpuid (shared adt) with
      | (sdt', halt', _) =>
        let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
        let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: INVALID64}} in
        Some adt {halt: halt'} {shared: sdt'} {slog: log'} {shadow_ctxts: (shadow_ctxts adt) # (ctxt_id vmid vcpuid) == ctxt'}
      end.

    Definition register_kvm_spec_h adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let vmid := next_vmid (core_data (shared adt)) in
      (* TODO: OGEN_VMID*)
      let log' := SEVENT (curid adt) (OGEN_VMID 0) :: (slog adt) in
      rely CORE_ID @ (hlock (shared adt));
      match local_gen_vmid (shared adt) with
      | (sdt', _) =>
        let adt1 := adt {shared: sdt'} {slog: log'} in
        let adt' := query_oracle adt1 in
        let log'' := SEVENT (curid adt) (OREG_KVM vmid) :: (slog adt) in
        rely (INFO_ID + vmid) @ (hlock (shared adt));
        match local_register_kvm vmid (shared adt) with
        | (sdt'', halt'', _) =>
          Some adt' {halt: halt''} {shared: sdt''} {slog: log''}
        end
      end.

    Definition set_boot_info_spec_h vmid load_addr size adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OBOOT_INFO vmid load_addr size) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt)); rely CORE_ID @ (hlock (shared adt));
      match local_set_boot_info vmid load_addr size (shared adt) with
      | (sdt', halt', _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition remap_vm_image_spec_h vmid pfn load_idx adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OREMAP_IMAGE vmid pfn load_idx) :: (slog adt) in
      rely (INFO_ID + vmid) @ (hlock (shared adt)); rely (NPT_ID + COREVISOR) @ (hlock (shared adt));
      match local_remap_vm_image vmid pfn load_idx (shared adt) with
      | (sdt', halt', _, _) =>
        Some adt {halt: halt'} {shared: sdt'} {slog: log'}
      end.

    Definition clear_vm_page_spec_h vmid pfn adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      let log' := SEVENT (curid adt) (OCLEAR_VM vmid pfn) :: (slog adt) in
      rely S2PAGE_ID @ (hlock (shared adt));
      match local_clear_vm_page vmid pfn (shared adt) with
      | (sdt', _, _) =>
        Some adt {shared: sdt'} {slog: log'}
      end.

    Definition assign_pfn_to_vm_spec_h vmid gfn pfn adt0 :=
      if halt adt0 then Some adt0 else
      let adt := query_oracle adt0 in
      (* TODO: OASSIGN_VM vmid gfn pfn ((doracle adt) vmid) (vmid @ (data_log adt)) *)
      let log' := SEVENT (curid adt) (OCLEAR_VM vmid pfn) :: (slog adt) in
      rely S2PAGE_ID @ (hlock (shared adt)); rely NPT_ID @ (hlock (shared adt));
      match local_assign_pfn_to_vm vmid gfn pfn ((doracle adt) vmid) (vmid @ (data_log adt)) (shared adt) with
      | (sdt', halt', logn', _, _, _) =>
        Some adt {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt) # vmid == logn'}
      end.

  Definition map_pfn_vm_spec_h vmid addr pte level adt0 :=
    if halt adt0 then Some adt0 else
    let adt := query_oracle adt0 in
    let log' := SEVENT (curid adt) (OMAP_VM vmid addr pte level) :: (slog adt) in
    rely (NPT_ID + vmid) @ (hlock (shared adt));
    match local_map_pfn_vm vmid addr pte level (shared adt) with
    | (sdt', halt', _) =>
      Some adt {halt: halt'} {shared: sdt'} {slog: log'}
    end.

  Definition map_vm_io_spec_h vmid gpa pa adt0 :=
    if halt adt0 then Some adt0 else
    let adt := query_oracle adt0 in
    (* TODO: OMAP_IO vmid gpa pa *)
    let log' := SEVENT (curid adt) (OCLEAR_VM vmid gpa) :: (slog adt) in
    rely S2PAGE_ID @ (hlock (shared adt)); rely (NPT_ID + vmid) @ (hlock (shared adt));
    match local_map_vm_io vmid gpa pa (shared adt) with
    | (sdt', halt', _, _) =>
      Some adt {halt: halt'} {shared: sdt'} {slog: log'}
    end.

  Definition grant_vm_page_spec_h vmid pfn adt0 :=
    if halt adt0 then Some adt0 else
    let adt := query_oracle adt0 in
    (* TODO: OGRANT vmid pfn *)
    let log' := SEVENT (curid adt) (OCLEAR_VM vmid pfn) :: (slog adt) in
    rely S2PAGE_ID @ (hlock (shared adt));
    match local_grant_vm_page vmid pfn (shared adt) with
    | (sdt', _) =>
      Some adt {shared: sdt'} {slog: log'}
    end.

  Definition revoke_vm_page_spec_h vmid pfn adt0 :=
    if halt adt0 then Some adt0 else
    let adt := query_oracle adt0 in
    (* TODO: OREVOKE vmid pfn dorc dlog *)
    let log' := SEVENT (curid adt) (OCLEAR_VM vmid pfn) :: (slog adt) in
    rely S2PAGE_ID @ (hlock (shared adt)); rely NPT_ID @ (hlock (shared adt));
    match local_revoke_vm_page vmid pfn ((doracle adt) vmid) (vmid @ (data_log adt)) (shared adt) with
    | (sdt', halt', logn', _, _, _) =>
      Some adt {halt: halt'} {shared: sdt'} {slog: log'} {data_log: (data_log adt) # vmid == logn'}
    end.

  Fixpoint SingleToMulti cpu obj slog :=
    match slog with
    | nil => nil
    | (SEVENT cid e) :: slog' =>
      let log0 := SingleToMulti cpu obj slog' in
      if cid =? cpu then
        let sdt0 := CalStateH slog' (shared empty_adt) in
        match e with
        | OMAP_HOST addr =>
          if obj =? S2PAGE_ID then
            match local_map_host addr sdt0 with
            | (_, _, Some s2p, _) => (TEVENT cid (TSHARED (OS2_PAGE s2p))) :: log0
            | _ => log0
            end
          else
            if obj =? NPT_ID then
              match local_map_host addr sdt0 with
              | (_, _, _, Some npt) => (TEVENT cid (TSHARED (ONPT npt))) :: log0
              | _ => log0
              end
            else log0
        | _ => log0
        end
      else log0
    end.

  Definition host_hvc_handler_spec  (adt: RData) : option RData :=
    Some adt.

  Definition host_npt_handler_spec  (adt: RData) : option RData :=
    Some adt.

  Definition host_vcpu_run_handler_spec  (adt: RData) : option RData :=
    Some adt.

  Definition vm_exit_handler_spec  (adt: RData) : option RData :=
    Some adt.

  Definition mem_load_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

  Definition mem_store_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    Some adt.

  Definition dev_load_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    Some adt.

  Definition dev_store_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    Some adt.

Section TrapHandlerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := TrapHandler_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := TrapHandlerRaw_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_local (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_local {
          id_icore: icore hadt = icore ladt;
          id_ihost: ihost hadt = ihost ladt;
          id_cur_vmid: cur_vmid hadt = cur_vmid ladt;
          id_cur_vcpuid: cur_vcpuid hadt = cur_vcpuid ladt;
          id_regs: regs hadt = regs ladt;
          id_lock: forall id, id @ (lock ladt) = LockFalse;
          id_shadow_ctxts: shadow_ctxts hadt = shadow_ctxts ladt;
          id_smmu_conf: smmu_conf hadt = smmu_conf ladt;
          id_doracle: doracle hadt = doracle ladt;
          id_core_doracle: core_doracle hadt = core_doracle ladt;
          id_data_log: data_log hadt = data_log ladt;
          id_core_data_log: core_data_log hadt = core_data_log ladt
        }.

    Record relate_log cpu (hlog: SingleLog) (llog: MultiLogPool) :=
      mkrelate_log {
          rel_flatmem: CalFlatmem (flatmem (shared empty_adt)) (SingleToMulti cpu FLATMEM_ID hlog) = CalFlatmem (flatmem (shared empty_adt)) (FLATMEM_ID @ llog);
          rel_s2page: CalS2Page (s2page (shared empty_adt)) (SingleToMulti cpu S2PAGE_ID hlog) = CalS2Page (s2page (shared empty_adt)) (S2PAGE_ID @ llog);
          rel_core_data: CalCoreData (core_data (shared empty_adt)) (SingleToMulti cpu CORE_ID hlog) = CalCoreData (core_data (shared empty_adt)) (CORE_ID @ llog);
          rel_spts: CalSPT (spts (shared empty_adt)) (SingleToMulti cpu SPT_ID hlog) = CalSPT (spts (shared empty_adt)) (SPT_ID @ llog);
          rel_smmu: CalSMMU (smmu_vmid (shared empty_adt)) (SingleToMulti cpu SMMU_ID hlog) = CalSMMU (smmu_vmid (shared empty_adt)) (SMMU_ID @ llog);
          rel_npts: forall vmid (is_vm: valid_vmid vmid), CalNPT (vmid @ (npts (shared empty_adt))) (SingleToMulti cpu (NPT_ID + vmid) hlog) =
                                                     CalNPT (vmid @ (npts (shared empty_adt))) ((NPT_ID + vmid) @ llog);
          rel_vminfos: forall vmid (is_vm: valid_vmid vmid), CalVMInfo (vmid @ (vminfos (shared empty_adt))) (SingleToMulti cpu (INFO_ID + vmid) hlog) =
                                                        CalVMInfo (vmid @ (vminfos (shared empty_adt))) ((INFO_ID + vmid) @ llog)
        }.

    Definition relate_hlock obj hlog llog :=
      obj @ (hlock (CalStateH hlog (shared empty_adt))) = true -> exists n, H_CalLock llog = Some (n, LEMPTY, None).

    Inductive range_s2page (s2p: ZMap.t S2Page) :=
    | R_S2PAGE: range_s2page s2p.

    Inductive range_core_data (core: CoreData) :=
    | R_CORE_DATA: range_core_data core.

    Inductive range_spts (spt: SPT) :=
    | R_SPT: range_spts spt.

    Inductive range_smmu (smmu: ZMap.t Z) :=
    | R_SMMU: range_smmu smmu.

    Inductive range_npt (npt: NPT) :=
    | R_NPT: range_npt npt.

    Inductive range_vminfo (info: VMInfo) :=
    | R_INFO: range_vminfo info.

    Record range_inv (adt: RData) :=
      mkrange_inv {
          r_s2page: range_s2page (s2page (shared adt));
          r_core: range_core_data (core_data (shared adt));
          r_spts: range_spts (spts (shared adt));
          r_smmu: range_smmu (smmu_vmid (shared adt));
          r_npt: forall vmid, valid_vmid vmid -> range_npt (vmid @ (npts (shared adt)));
          r_vminfo: forall vmid, valid_vmid vmid -> range_vminfo (vmid @ (vminfos (shared adt)))
        }.

    Record sync_shared (adt: RData) :=
      mksync_shared {
          sync_flatmem: CalFlatmem (flatmem (shared empty_adt)) (FLATMEM_ID @ (log adt)) = flatmem (shared adt);
          sync_s2page: CalS2Page (s2page (shared empty_adt)) (S2PAGE_ID @ (log adt)) = s2page (shared adt);
          sync_core: CalCoreData (core_data (shared empty_adt)) (CORE_ID @ (log adt)) = core_data (shared adt);
          sync_spts: CalSPT (spts (shared empty_adt)) (SPT_ID @ (log adt)) = spts (shared adt);
          sync_smmu: CalSMMU (smmu_vmid (shared empty_adt)) (SMMU_ID @ (log adt)) = smmu_vmid (shared adt);
          sync_npt: forall vmid (Hvalid: valid_vmid vmid), CalNPT (vmid @ (npts (shared empty_adt))) ((NPT_ID + vmid) @ (log adt)) = vmid @ (npts (shared adt));
          sync_vminfo: forall vmid (Hvalid: valid_vmid vmid), CalVMInfo (vmid @ (vminfos (shared empty_adt))) ((INFO_ID + vmid) @ (log adt)) = vmid @ (vminfos (shared adt))
        }.

    Inductive relate_oracle (sorc: SingleOracle) (orac: MultiOraclePool) :=
    | REL_ORACLE
        (oracle_rel_cond:
           forall cpu hlog llog (Hrel_log: relate_log cpu hlog llog),
             (flatmem (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt)) =
              CalFlatmem (flatmem (shared empty_adt)) ((FLATMEM_ID @ orac) cpu (FLATMEM_ID @ llog) ++ (FLATMEM_ID @ llog))) /\
             (s2page (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt)) =
              CalS2Page (s2page (shared empty_adt)) ((S2PAGE_ID @ orac) cpu (S2PAGE_ID @ llog) ++ (S2PAGE_ID @ llog))) /\
             (core_data (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt)) =
              CalCoreData (core_data (shared empty_adt)) ((CORE_ID @ orac) cpu (CORE_ID @ llog) ++ (CORE_ID @ llog))) /\
             (spts (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt)) =
              CalSPT (spts (shared empty_adt)) ((SPT_ID @ orac) cpu (SPT_ID @ llog) ++ (SPT_ID @ llog))) /\
             (smmu_vmid (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt)) =
              CalSMMU (smmu_vmid (shared empty_adt)) ((SMMU_ID @ orac) cpu (SMMU_ID @ llog) ++ (SMMU_ID @ llog))) /\
             (forall vmid (Hvmid: valid_vmid vmid), vmid @ (npts (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt))) =
              CalNPT (vmid @ (npts (shared empty_adt))) (((NPT_ID + vmid) @ orac) cpu ((NPT_ID + vmid) @ llog) ++ ((NPT_ID + vmid) @ llog))) /\
             (forall vmid (Hvmid: valid_vmid vmid), vmid @ (vminfos (CalStateH ((sorc cpu hlog) ++ hlog) (shared empty_adt))) =
              CalVMInfo (vmid @ (vminfos (shared empty_adt))) (((INFO_ID + vmid) @ orac) cpu ((INFO_ID + vmid) @ llog) ++ ((INFO_ID + vmid) @ llog))))
        (oracle_range_inv:
           forall cpu log, (forall s2p, range_s2page s2p -> range_s2page (CalS2Page s2p ((S2PAGE_ID @ orac) cpu log))) /\
                      (forall core, range_core_data core -> range_core_data (CalCoreData core ((CORE_ID @ orac) cpu log))) /\
                      (forall spt, range_spts spt -> range_spts (CalSPT spt ((SPT_ID @ orac) cpu log))) /\
                      (forall smmu, range_smmu smmu -> range_smmu (CalSMMU smmu ((SMMU_ID @ orac) cpu log))) /\
                      (forall vmid npt, valid_vmid vmid -> range_npt npt -> range_npt (CalNPT npt (((NPT_ID + vmid) @ orac) cpu log))) /\
                      (forall vmid info, valid_vmid vmid -> range_vminfo info -> range_vminfo (CalVMInfo info (((INFO_ID + vmid) @ orac) cpu log))))
        (oracle_lock_cond: forall cpu hlog llog (Hrel_hlock: forall obj, relate_hlock obj hlog (obj @ llog)),
            (forall obj, relate_hlock obj ((sorc cpu hlog) ++ hlog) ((obj @ orac) cpu (obj @ llog) ++ (obj @ llog)))):
        relate_oracle sorc orac.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_halt: halt hadt = halt ladt;
          id_curid: curid hadt = curid ladt;
          id_local: halt hadt = false -> relate_local hadt ladt;
          syncd_sharedh: CalStateH (slog hadt) (shared empty_adt) = shared hadt;
          syncd_sharedl: sync_shared ladt;
          rel_log: relate_log (curid hadt) (slog hadt) (log ladt);
          rel_oracle: relate_oracle (soracle hadt) (oracle ladt);
          rel_hlock: forall obj, relate_hlock obj (slog hadt) (obj @ (log ladt));
          valid_range: range_inv ladt
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    Section FreshPrim.

      Lemma host_hvc_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_hvc_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_hvc_handler_spec0  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. unfold host_hvc_handler_spec0, host_hvc_handler_raw_spec; autounfold.
        Qed.

      Lemma host_hvc_handler_spec_ref:
        compatsim (crel RData RData) (gensem host_hvc_handler_spec) host_hvc_handler_spec_low.
      Proof.
        Opaque host_hvc_handler_spec.
        compatsim_simpl (@match_RData).
        exploit host_hvc_handler_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma host_npt_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_npt_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_npt_handler_spec0 labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof host_npt_handler0; repeat hstep; try htrivial.
        Qed.

      Lemma host_npt_handler_spec_ref:
        compatsim (crel RData RData) (gensem host_npt_handler_spec) host_npt_handler_spec_low.
      Proof.
        Opaque host_npt_handler_spec.
        compatsim_simpl (@match_RData).
        exploit host_npt_handler_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma host_vcpu_run_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_vcpu_run_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_vcpu_run_handler_spec0 labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof host_vcpu_run_handler0; repeat hstep; try htrivial.
        Qed.

      Lemma host_vcpu_run_handler_spec_ref:
        compatsim (crel RData RData) (gensem host_vcpu_run_handler_spec) host_vcpu_run_handler_spec_low.
      Proof.
        Opaque host_vcpu_run_handler_spec.
        compatsim_simpl (@match_RData).
        exploit host_vcpu_run_handler_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma vm_exit_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: vm_exit_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', vm_exit_handler_spec0 labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof vm_exit_handler0; repeat hstep; try htrivial.
        Qed.

      Lemma vm_exit_handler_spec_ref:
        compatsim (crel RData RData) (gensem vm_exit_handler_spec) vm_exit_handler_spec_low.
      Proof.
        Opaque vm_exit_handler_spec.
        compatsim_simpl (@match_RData).
        exploit vm_exit_handler_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma mem_load_spec_exists:
        forall habd habd' labd gfn reg f
               (Hspec: mem_load_spec gfn reg habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', mem_load_spec0 gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof mem_load0; repeat hstep; try htrivial.
        Qed.

      Lemma mem_load_spec_ref:
        compatsim (crel RData RData) (gensem mem_load_spec) mem_load_spec_low.
      Proof.
        Opaque mem_load_spec.
        compatsim_simpl (@match_RData).
        exploit mem_load_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma mem_store_spec_exists:
        forall habd habd' labd gfn reg f
               (Hspec: mem_store_spec gfn reg habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', mem_store_spec0 gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof mem_store0; repeat hstep; try htrivial.
        Qed.

      Lemma mem_store_spec_ref:
        compatsim (crel RData RData) (gensem mem_store_spec) mem_store_spec_low.
      Proof.
        Opaque mem_store_spec.
        compatsim_simpl (@match_RData).
        exploit mem_store_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma dev_load_spec_exists:
        forall habd habd' labd gfn reg cbndx index f
               (Hspec: dev_load_spec gfn reg cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', dev_load_spec0 gfn reg cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof dev_load0; repeat hstep; try htrivial.
        Qed.

      Lemma dev_load_spec_ref:
        compatsim (crel RData RData) (gensem dev_load_spec) dev_load_spec_low.
      Proof.
        Opaque dev_load_spec.
        compatsim_simpl (@match_RData).
        exploit dev_load_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma dev_store_spec_exists:
        forall habd habd' labd gfn reg cbndx index f
               (Hspec: dev_store_spec gfn reg cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', dev_store_spec0 gfn reg cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof dev_store0; repeat hstep; try htrivial.
        Qed.

      Lemma dev_store_spec_ref:
        compatsim (crel RData RData) (gensem dev_store_spec) dev_store_spec_low.
      Proof.
        Opaque dev_store_spec.
        compatsim_simpl (@match_RData).
        exploit dev_store_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) TrapHandler_passthrough TrapHandlerRaw.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End TrapHandlerProofHigh.

```
