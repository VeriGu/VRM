# HighSpecs

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

Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.ltb Z.geb Z.gtb.

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

Definition local_clear_vm_page vmid pfn sdt :=
  let s2p := s2page sdt in
  let fmem := flatmem sdt in
  let page := pfn @ s2p in
  let npt := HOSTVISOR @ (npts sdt) in
  if s2_owner page =? vmid then
    match pfn @ (pt npt) with
    | (pfn', level, pte) =>
      match (if pte =? 0 then (false, npt)
             else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
      | (halt', npt') =>
        if halt' then
          (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # NPT_ID == false} {npts: (npts sdt) # HOSTVISOR == npt'},
           true, Some s2p, Some npt', None)
        else
          let page' := mkS2Page HOSTVISOR 0 (pfn + SMMU_HOST_OFFSET) in
          let s2p' := s2p # pfn == page' in
          let fmem' := fmem # pfn == 0 in
          (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
           false, Some s2p', Some npt', Some fmem')
      end
    end
  else
    (sdt, false, Some s2p, None, None).

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
        match (if pte =? 0 then (false, npt)
              else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
        | (halt', npt') =>
          if halt' then
            (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # NPT_ID == false} {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'},
              true, logn, Some s2p', Some npt', None)
          else
            (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
              false, logn + 1, Some s2p', Some npt', Some fmem')
        end
      end
    else
      (sdt {hlock: (hlock sdt) # S2PAGE_ID == false}, true, logn, Some s2p, None, None)
  else
    if (s2_owner page =? vmid) && ((s2_gfn page =? INVALID64) || (gfn =? s2_gfn page)) then
      let page' := page {s2_count: if s2_count page =? INVALID then 0 else s2_count page}
                        {s2_gfn: if s2_gfn page =? INVALID64 then gfn else s2_gfn page}
      in
      let s2p' := s2p # pfn == page in
      (sdt {s2page: s2p'}, false, logn, Some s2p', None, None)
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

Definition local_map_io vmid gpa pa sdt :=
  let info := vmid @ (vminfos sdt) in
  let state := vm_state (VS info) in
  if state =? READY then
    let s2p := s2page sdt in
    let npt := vmid @ (npts sdt) in
    let gfn := gpa / PAGE_SIZE in
    let pfn := pa / PAGE_SIZE in
    let pte := Z.lor (phys_page pa) (Z.lor PAGE_S2_DEVICE S2_RDWR) in
    let page := pfn @ s2p in
    if s2_owner page =? INVALID then
      let (halt', npt') := local_mmap_h vmid gpa 3 pte npt in
      if halt' then
        (sdt {hlock: (((hlock sdt) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # (NPT_ID + vmid) == false} {npts: (npts sdt) # vmid == npt'},
        true, Some info, Some s2p, Some npt')
      else
        (sdt {npts: (npts sdt) # vmid == npt'}, false, Some info, Some s2p, Some npt')
    else
      (sdt, false, Some info, Some s2p, None)
  else
    (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, Some info, None, None).

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
        match (if pte =? 0 then (false, npt)
              else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
        | (halt', npt') =>
          if halt' then
            (sdt {hlock: ((hlock sdt) # S2PAGE_ID == false) # NPT_ID == false} {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'},
            true, logn, Some s2p', Some npt', None)
          else
            (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
            false, logn + 1, Some s2p', Some npt', Some fmem')
        end
      end
    else
      (sdt {s2page: s2p'}, false, logn, Some s2p', None, None)
  else
    (sdt, false, logn, Some s2p, None, None).

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

Definition local_set_vm_poweroff vmid sdt :=
  let info := vmid @ (vminfos sdt) in
  let info' := info {vm_state: POWEROFF} in
  (sdt {vminfos: (vminfos sdt) # vmid == info'}, Some info').

Parameter verify_img: Z -> Z64 -> Z.
Parameter reg_desc: Z -> Z.
Parameter shared_kvm: Z -> Z.
Parameter shared_vcpu: Z -> Z -> Z.
Parameter exception_vector: Z64 -> Z.

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
  if vmid <? COREVISOR then
    let core' := (core_data sdt) {next_vmid: vmid + 1} in
    (sdt {core_data: core'}, false, core')
  else
    (sdt, true, (core_data sdt)).

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
      if (0 <? pgnum) && (remap + pgnum * PAGE_SIZE <? REMAP_END) then
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

Definition local_verify_vm vmid sdt :=
  let info := vmid @ (vminfos sdt) in
  let state := vm_state (VS info) in
  if state =? READY then
    let info' := info {vm_state: VERIFIED} in
    (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, Some info')
  else
    (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, Some info).

Definition local_free_smmu_pgd cbndx index sdt :=
  let vmid := (smmu_id index cbndx) @ (smmu_vmid sdt) in
  if vmid =? INVALID then
    (sdt, false, Some (smmu_vmid sdt), None)
  else
    let info := vmid @ (vminfos sdt) in
    if vm_state (VS info) =? POWEROFF then
      let smmu' := (smmu_vmid sdt) # (smmu_id index cbndx) == INVALID in
      (sdt {smmu_vmid: smmu'}, false, Some smmu', Some info)
    else
      (sdt {hlock: (hlock sdt) # SMMU_ID == false}, true, Some (smmu_vmid sdt), Some info).

Definition local_alloc_smmu_pgd cbndx vmid index num sdt :=
  if cbndx <? num then
    let target := (smmu_id index cbndx) @ (smmu_vmid sdt) in
    if target =? INVALID then
      let info := vmid @ (vminfos sdt) in
      let state := vm_state (VS info) in
      if is_vm vmid && (state =? VERIFIED) then
        (sdt {hlock: ((hlock sdt) # (INFO_ID + vmid) == false) # SMMU_ID == false}, true, Some (smmu_vmid sdt), Some info, None)
      else
        let smmu' := (smmu_vmid sdt) # (smmu_id index cbndx) == vmid in
        let ttbr := SMMU_TTBR index cbndx in
        let spt := spts sdt in
        let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (ZMap.init (0, 0))}
                        {spt_pgd_t: (spt_pgd_t spt) # ttbr == (ZMap.init false)}
                        {spt_pmd_t: (spt_pmd_t spt) # ttbr == (ZMap.init (ZMap.init false))} in
        (sdt {smmu_vmid: smmu'} {spts: spt'}, false, Some smmu', Some info, Some spt')
    else
      (sdt, false, Some (smmu_vmid sdt), None, None)
  else
    (sdt {hlock: (hlock sdt) # SMMU_ID == false}, true, Some (smmu_vmid sdt), None, None).

Definition local_smmu_assign_page cbndx index pfn gfn sdt :=
  let smmu := smmu_vmid sdt in
  let vmid := (smmu_id index cbndx) @ (smmu_vmid sdt) in
  let info := vmid @ (vminfos sdt) in
  let s2p := s2page sdt in
  let npt := HOSTVISOR @ (npts sdt) in
  if vmid =? INVALID then
    (sdt, false, Some smmu, None, None, None)
  else
    let state := vm_state (VS info) in
    if is_vm vmid then
      if state =? VERIFIED then
        (sdt {hlock: ((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false}, true, Some smmu, Some info, None, None)
      else
        let page := pfn @ s2p in
        if s2_owner page =? HOSTVISOR then
          if s2_count page =? 0 then
            let s2p' := s2p # pfn == (mkS2Page vmid INVALID gfn) in
            match pfn @ (pt npt) with
            | (_, level, pte) =>
              match (if pte =? 0 then (false, npt)
                      else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
              | (halt', npt') =>
                if halt' then
                  (sdt {hlock: ((((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # NPT_ID == false}
                        {npts: (npts sdt) # HOSTVISOR == npt'},
                    true, Some smmu, Some info, Some s2p, Some npt')
                else
                  (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'}, false, Some smmu, Some info, Some s2p', Some npt')
              end
            end
          else
            (sdt {hlock: (((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false}, true, Some smmu, Some info, Some s2p, None)
        else
          if s2_owner page =? vmid then
            (sdt, false, Some smmu, Some info, Some s2p, None)
          else
            (sdt {hlock: (((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false}, true, Some smmu, Some info, Some s2p, None)
    else
      (sdt, false, Some smmu, Some info, None, None).

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
        match local_spt_map_h cbndx index iova pte spt with
        | (halt', spt') =>
          if halt' then
            (sdt {hlock: ((((hlock sdt) # SMMU_ID == false) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # SPT_ID == false}
                  {spts: spt'}, true, Some smmu, Some info, Some s2p, Some spt')
          else
            let s2p' := (if (s2_owner page =? HOSTVISOR) && (s2_count page <? EL2_SMMU_CFG_SIZE)
                          then s2p # pfn == (page {s2_count: (s2_count page) + 1}) else s2p) in
            (sdt {s2page: s2p'} {spts: spt'}, false, Some smmu, Some info, Some s2p', Some spt')
        end
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
    if is_vm vmid && (state >=? VERIFIED) then
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
                      then s2p # pfn0 == (page {s2_count: (s2_count page) - 1}) else s2p) in
        (sdt {s2page: s2p'} {spts: spt'}, false, Some smmu, Some info, Some s2p', Some spt').

Parameter decrypt_gp_regs_specx : CtxtRegs -> CtxtStates -> (Z -> Z) -> Z -> ((CtxtRegs * CtxtStates) * Z).
Parameter decrypt_sys_regs_specx : CtxtRegs -> CtxtStates -> (Z -> Z) -> Z -> ((CtxtRegs * CtxtStates) * Z).

Definition local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn sdt :=
  let info := vmid @ (vminfos sdt) in
  let vms := vm_state (VS info) in
  let vcpus := vcpuid @ (vm_vcpu_state (VS info)) in
  if (vms =? READY) && (vcpus =? READY) then
    match decrypt_gp_regs_specx cregs cstates dorc logn with
    | (cregs', cstates', logn') =>
      match decrypt_sys_regs_specx cregs' cstates' dorc logn' with
      | (cregs'', cstates'', logn'') =>
        let info' := info {vm_inc_exe: 1} in
        (sdt {vminfos: (vminfos sdt) # vmid == info'}, false, cregs'', cstates'', logn'', Some info')
      end
    end
  else
    (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, cregs, cstates, logn, Some info).

Definition local_save_encrypt_buf vmid inbuf outbuf dorc logn sdt :=
  let inpfn := inbuf / PAGE_SIZE in
  let outpfn := outbuf / PAGE_SIZE in
  let inpage := inpfn @ (s2page sdt) in
  let outpage := outpfn @ (s2page sdt) in
  if (s2_owner inpage =? vmid) && (s2_owner outpage =? HOSTVISOR) then
    let fmem' := (flatmem sdt) # outpfn == (dorc logn) in
    (sdt {flatmem: fmem'}, false, logn + 1, Some (s2page sdt), Some fmem')
  else
    (sdt {hlock: (hlock sdt) # S2PAGE_ID == false}, true, logn, Some (s2page sdt), None).

Definition local_load_decrypt_buf vmid inbuf dorc logn sdt :=
  let pfn := inbuf / PAGE_SIZE in
  let info := vmid @ (vminfos sdt) in
  let s2p := s2page sdt in
  let npt := HOSTVISOR @ (npts sdt) in
  let vms := vm_state (VS info) in
  let page := pfn @ s2p in
  if vms =? READY then
    if (s2_owner page =? HOSTVISOR) && (s2_count page =? 0) then
      match pfn @ (pt npt) with
      | (pfn', level, pte) =>
        match (if pte =? 0 then (false, npt)
              else local_mmap_h HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
        | (halt', npt') =>
          if halt' then
            (sdt {hlock: (((hlock sdt) # (INFO_ID + vmid) == false) # S2PAGE_ID == false) # NPT_ID == false}
                 {npts: (npts sdt) # HOSTVISOR == npt'}, true, logn, Some info, Some s2p, Some npt', None)
          else
            let page' := mkS2Page vmid 0 INVALID64 in
            let s2p' := s2p # pfn == page' in
            let fmem' := (flatmem sdt) # pfn == (dorc logn) in
            (sdt {npts: (npts sdt) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'},
             false, logn + 1, Some info, Some s2p', Some npt', Some fmem')
        end
      end
    else
      (sdt {hlock: ((hlock sdt) # (INFO_ID + vmid) == false) # S2PAGE_ID == false},
       true, logn, Some info, Some s2p, None, None)
  else
    (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, logn, Some info, None, None, None).


(*****************************************************************************************************************************************************)

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

(*****************************************************************************************************************************************************)

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

Definition mem_load_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
  match gfn, icore adt with
  | VZ64 gfn, false =>
    let adt := query_oracle adt in
    let log' := (SEVENT (curid adt) (OPT_GET (cur_vmid adt))) :: (slog adt) in
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    match
      (if vmid =? HOSTVISOR then
         match gfn @ (pt (vmid @ (npts (shared adt)))) with
         | (pfn, level, pte) =>
           if pfn =? 0 then None else
           if s2_owner (pfn @ (s2page (shared adt))) =? HOSTVISOR
           then Some (pfn @ (flatmem (shared adt)))
           else Some ((doracle adt) vmid (vmid @ (data_log adt)))
         end
       else
         rely (vm_state (VS (cur_vmid adt) @ (vminfos (shared adt))) =? VERIFIED);
         match gfn @ (pt (vmid @ (npts (shared adt)))) with
         | (pfn, level, pte) =>
           if pfn =? 0 then None else
           if s2_count (pfn @ (s2page (shared adt))) =? 0
           then Some (pfn @ (flatmem (shared adt)))
           else Some ((doracle adt) vmid (vmid @ (data_log adt)))
         end
      )
    with
    | Some val =>
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      rely (reg <? X30);
      match set_shadow_ctxt_specx reg val (ctxt_regs ctxt) (ctxt_states ctxt) with
      | (cregs', cstates') =>
        let ctxt' := ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'} in
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'} {slog: log'}
      end
    | _ => None
    end
  | _, _ => None
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

Definition mem_store_spec (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
  match gfn, icore adt with
  | VZ64 gfn, false =>
    let adt := query_oracle adt in
    let log' := (SEVENT (curid adt) (OPT_GET (cur_vmid adt))) :: (slog adt) in
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let val := get_shadow_ctxt_specx reg (ctxt_regs ctxt) (ctxt_states ctxt) in
    if vmid =? HOSTVISOR then
      match gfn @ (pt (vmid @ (npts (shared adt)))) with
      | (pfn, level, pte) =>
        if pfn =? 0 then None else
          if s2_owner (pfn @ (s2page (shared adt))) =? HOSTVISOR
          then Some adt {shared: (shared adt) {flatmem: (flatmem (shared adt)) # pfn == val}} {slog: log'}
          else Some adt {slog: log'}
      end
    else
      rely (vm_state (VS (cur_vmid adt) @ (vminfos (shared adt))) =? VERIFIED);
      match gfn @ (pt (vmid @ (npts (shared adt)))) with
      | (pfn, level, pte) =>
        if pfn =? 0 then None else
          if s2_count (pfn @ (s2page (shared adt))) =? 0
          then Some adt {shared: (shared adt) {flatmem: (flatmem (shared adt)) # pfn == val}} {slog: log'}
          else Some adt {slog: log'}
      end
  | _, _ => None
  end.

Definition dev_load_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
  match gfn, icore adt with
  | VZ64 gfn, false =>
    rely is_smmu index; rely is_smmu_cfg cbndx;
    let adt := query_oracle adt in
    let log' := (SEVENT (curid adt) (OPT_GET (cur_vmid adt))) :: (slog adt) in
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let smmuid := smmu_id index cbndx  in
    rely smmuid @ (smmu_vmid (shared adt)) =? vmid;
    let spt := (SMMU_TTBR index cbndx) @ (spt_pt (spts (shared adt))) in
    match
      (if vmid =? HOSTVISOR then
        match gfn @ spt with
        | (pfn, pte) =>
          if pfn =? 0 then None else
          if s2_owner (pfn @ (s2page (shared adt))) =? HOSTVISOR
          then Some (pfn @ (flatmem (shared adt)))
          else Some ((doracle adt) vmid (vmid @ (data_log adt)))
        end
      else
        rely (vm_state (VS (cur_vmid adt) @ (vminfos (shared adt))) =? VERIFIED);
        match gfn @ spt with
        | (pfn, pte) =>
          if pfn =? 0 then None else
          if s2_count (pfn @ (s2page (shared adt))) =? 0
          then Some (pfn @ (flatmem (shared adt)))
          else Some ((doracle adt) vmid (vmid @ (data_log adt)))
        end
      )
    with
    | Some val =>
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      rely (reg <? X30);
      match set_shadow_ctxt_specx reg val (ctxt_regs ctxt) (ctxt_states ctxt) with
      | (cregs', cstates') =>
        let ctxt' := ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'} in
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'} {slog: log'}
      end
    | _ => None
    end
  | _, _ => None
  end.

Definition dev_store_spec (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
  match gfn, icore adt with
  | VZ64 gfn, false =>
    rely is_smmu index; rely is_smmu_cfg cbndx;
    let adt := query_oracle adt in
    let log' := (SEVENT (curid adt) (OPT_GET (cur_vmid adt))) :: (slog adt) in
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    let ctxtid := ctxt_id vmid vcpuid in
    let smmuid := smmu_id index cbndx in
    rely smmuid @ (smmu_vmid (shared adt)) =? vmid;
    let spt := (SMMU_TTBR index cbndx) @ (spt_pt (spts (shared adt))) in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let val := get_shadow_ctxt_specx reg (ctxt_regs ctxt) (ctxt_states ctxt) in
    if vmid =? HOSTVISOR then
      match gfn @ spt with
      | (pfn, pte) =>
        if pfn =? 0 then None else
          if s2_owner (pfn @ (s2page (shared adt))) =? HOSTVISOR
          then Some adt {shared: (shared adt) {flatmem: (flatmem (shared adt)) # pfn == val}} {slog: log'}
          else Some adt {slog: log'}
      end
    else
      rely (vm_state (VS (cur_vmid adt) @ (vminfos (shared adt))) =? VERIFIED);
      match gfn @ spt with
      | (pfn, pte) =>
        if pfn =? 0 then None else
          if s2_count (pfn @ (s2page (shared adt))) =? 0
          then Some adt {shared: (shared adt) {flatmem: (flatmem (shared adt)) # pfn == val}} {slog: log'}
          else Some adt {slog: log'}
      end
  | _, _ => None
  end.

(***********************************************************************************************************************************************)

Definition host_to_core_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
  gp {x0: (x0 rgp)} {x1: (x1 rgp)} {x2: (x2 rgp)} {x3: (x3 rgp)}
      {x4: (x4 rgp)} {x5: (x5 rgp)} {x6: (x6 rgp)} {x7: (x7 rgp)}
      {x8: (x8 rgp)} {x9: (x9 rgp)} {x10: (x10 rgp)} {x11: (x11 rgp)}
      {x12: (x12 rgp)} {x13: (x13 rgp)} {x14: (x14 rgp)} {x15: (x15 rgp)}
      {x16: (x16 rgp)} {x17: (x17 rgp)} {x18: (x18 rgp)} {x19: (x19 rgp)}
      {x20: (x20 rgp)} {x21: (x21 rgp)} {x22: (x22 rgp)} {x23: (x23 rgp)}
      {x24: (x24 rgp)} {x25: (x25 rgp)} {x26: (x26 rgp)} {x27: (x27 rgp)}
      {x28: (x28 rgp)} {x29: (x29 rgp)} {x30: (x30 rgp)}.

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

Definition vcpu_run_swith_to_core (adt: RData) :=
  let ctxtid := ctxt_id HOSTVISOR (cur_vcpuid adt) in
  let ctxt := ctxtid @ (shadow_ctxts adt) in
  let regc := regs adt in
  let cregs1 := host_to_core_specx (ctxt_regs ctxt) (ctxt_regs regc) in
  let cregs2 := save_sysregs_specx cregs1 (ctxt_regs regc) in
  let cregs3 := fpsimd_save_state_specx cregs2 (ctxt_regs regc) in
  let vmid := x0 cregs3 in
  if is_vm vmid then
    adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs3})} {icore: true} {cur_vmid: vmid} {cur_vcpuid: -1}
  else
    adt {halt: true}.

Fixpoint reset_sys_regs_loopx n i vcpuid cregs cstates (dorc: Z -> Z) logn :=
  match n with
  | O => (cregs, cstates, logn, i)
  | S n' =>
    match reset_sys_regs_loopx n' i vcpuid cregs cstates dorc logn with
    | (cregs', cstates', logn', i') =>
      if i' =? MPIDR_EL1 then
        let mpidr :=  (Z.land vcpuid 15) + (Z.land (vcpuid / 16) 255) * 256 +
                      (Z.land (vcpuid / 4096) 255) * 65536 in
        match set_shadow_ctxt_specx i' (mpidr + 2147483648) cregs' cstates' with
        | (cregs'', cstates'') => (cregs'', cstates'', logn', i' + 1)
        end
      else
        if i' =? ACTLR_EL1 then
          let val := dorc logn' in
          match set_shadow_ctxt_specx i' val cregs' cstates' with
          | (cregs'', cstates'') => (cregs'', cstates'', logn' + 1, i' + 1)
          end
        else
          let val := reg_desc i' in
          match set_shadow_ctxt_specx i' val cregs' cstates' with
          | (cregs'', cstates'') => (cregs'', cstates'', logn', i' + 1)
          end
    end
  end.

Definition reset_sys_regs_specx vcpuid cregs cstates dorc logn :=
  match reset_sys_regs_loopx (Z.to_nat SHADOW_SYS_REGS_SIZE) SYSREGS_START vcpuid cregs cstates dorc logn with
  | (cregs', cstates', logn', i') => (cregs', cstates', logn')
  end.

Fixpoint sync_dirty_to_shadow_loopx (n: nat) (i: Z) dirty cregs cstates dorc logn :=
  match n with
  | O => (i, cregs, cstates, logn)
  | S n' =>
    match sync_dirty_to_shadow_loopx n' i dirty cregs cstates dorc logn with
    | (i', cregs', cstates', logn') =>
      if (Z.land dirty (Z.shiftl 1 i')) =? 0 then
        (i' + 1, cregs', cstates', logn')
      else
        let reg := dorc logn in
        match set_shadow_ctxt_specx i' reg cregs' cstates' with
        | (cregs'', cstates'') => (i' + 1, cregs'', cstates'', logn' + 1)
        end
    end
  end.

Definition sync_dirty_to_shadow_specx (vmid: Z) (dirty: Z) (cregs: CtxtRegs) (cstates: CtxtStates) (logn: Z) (dorc: Z -> Z) :=
  match sync_dirty_to_shadow_loopx 31%nat 0 dirty cregs cstates dorc logn with
  | (i', cregs', cstates', logn') => (cregs', cstates', logn')
  end.

Definition update_exception_gp_regs_specx (cregs: CtxtRegs) (cstates: CtxtStates) :=
  let pstate0 := pstate cstates in
  let pc0 := pc cstates in
  let new_pc := (exception_vector (VZ64 pstate0)) in
  (cregs {elr_el1: pc0}, cstates {spsr_0: pstate0} {esr_el1: ESR_ELx_EC_UNKNOWN} {pstate: PSTATE_FAULT_BITS_64}).

Fixpoint prot_and_map_vm_loop_h n vmid gfn pfn adt :=
  match n with
  | O => Some (gfn, pfn, adt)
  | S n' =>
    match prot_and_map_vm_loop_h n' vmid gfn pfn adt with
    | Some (gfn', pfn', adt') =>
      if halt adt' then Some (gfn' + 1, pfn' + 1, adt') else
      let adt0 := query_oracle adt' in
      let log' := SEVENT (curid adt0) (OASSIGN_VM vmid gfn pfn (doracle adt0) (vmid @ (data_log adt0))) :: (slog adt0) in
      rely S2PAGE_ID @ (hlock (shared adt0)); rely NPT_ID @ (hlock (shared adt0));
      match local_assign_pfn_to_vm vmid gfn pfn ((doracle adt0) vmid) (vmid @ (data_log adt0)) (shared adt0) with
      | (sdt', halt', logn', _, _, _) =>
        Some (gfn' + 1, pfn' + 1, adt0 {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt) # vmid == logn'})
      end
    | _ => None
    end
  end.

Definition prot_and_map_vm_s2pt_spec_h vmid addr pte level adt :=
  if halt adt then Some adt else
  let target := phys_page pte in
  let pfn := target / PAGE_SIZE in
  let gfn := addr / PAGE_SIZE in
  if level =? 2 then
    let gfn' := gfn / PTRS_PER_PMD * PTRS_PER_PMD in
    let num := PMD_PAGE_NUM in
    match prot_and_map_vm_loop_h (Z.to_nat num) vmid gfn' pfn adt with
    | Some (gfn'', pfn'', adt') =>
      if halt adt' then Some adt' else
      let adt0 := query_oracle adt' in
      let log' := SEVENT (curid adt0) (OMAP_VM vmid addr pte 2) :: (slog adt0) in
      rely (NPT_ID + vmid) @ (hlock (shared adt0));
      match local_map_pfn_vm vmid addr pte 2 (shared adt0) with
      | (sdt', halt', _) =>
        Some adt0 {halt: halt'} {shared: sdt'} {slog: log'}
      end
    | _ => None
    end
  else
    let adt0 := query_oracle adt in
    let log' := SEVENT (curid adt0) (OASSIGN_VM vmid gfn pfn (doracle adt0) (vmid @ (data_log adt0))) :: (slog adt0) in
    rely S2PAGE_ID @ (hlock (shared adt0)); rely NPT_ID @ (hlock (shared adt0));
    match local_assign_pfn_to_vm vmid gfn pfn ((doracle adt0) vmid) (vmid @ (data_log adt0)) (shared adt0) with
    | (sdt', halt', logn', _, _, _) =>
      let adt'' := adt0 {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt) # vmid == logn'} in
      let adt0 := query_oracle adt'' in
      let log' := SEVENT (curid adt0) (OMAP_VM vmid addr pte 3) :: (slog adt0) in
      rely (NPT_ID + vmid) @ (hlock (shared adt0));
      match local_map_pfn_vm vmid addr pte 3 (shared adt0) with
      | (sdt', halt', _) =>
        Some adt0 {halt: halt'} {shared: sdt'} {slog: log'}
      end
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

Definition clear_shadow_gp_regs_specx (gp: CtxtRegs) :=
  gp {x0: 0} {x1: 0} {x2: 0} {x3: 0} {x4: 0} {x5: 0} {x6: 0} {x7: 0}
      {x8: 0} {x9: 0} {x10: 0} {x11: 0} {x12: 0} {x13: 0} {x14: 0} {x15: 0}
      {x16: 0} {x17: 0} {x18: 0} {x19: 0} {x20: 0} {x21: 0} {x22: 0} {x23: 0}
      {x24: 0} {x25: 0} {x26: 0} {x27: 0} {x28: 0} {x29: 0} {x30: 0}.

Definition reset_fp_regs_specx (gp: CtxtRegs) :=
  gp {fp_q0: 0} {fp_q1: 0} {fp_q2: 0} {fp_q3: 0} {fp_q4: 0} {fp_q5: 0} {fp_q6: 0} {fp_q7: 0}
      {fp_q8: 0} {fp_q9: 0} {fp_q10: 0} {fp_q11: 0} {fp_q12: 0} {fp_q13: 0} {fp_q14: 0} {fp_q15: 0}
      {fp_q16: 0} {fp_q17: 0} {fp_q18: 0} {fp_q19: 0} {fp_q20: 0} {fp_q21: 0} {fp_q22: 0} {fp_q23: 0}
      {fp_q24: 0} {fp_q25: 0} {fp_q26: 0} {fp_q27: 0} {fp_q28: 0} {fp_q29: 0} {fp_q30: 0}
      {fp_q31: 0} {fp_fpsr: 0} {fp_fpcr: 0}.

Definition vcpu_run_process (adt: RData) :=
  let vmid := cur_vmid adt in
  let clogn := vmid @ (core_data_log adt) in
  let vcpuid := (core_doracle adt) vmid clogn in
  let ctxtid' := ctxt_id vmid vcpuid in
  if is_vcpu vcpuid then
    let adt' := adt {cur_vcpuid: vcpuid} {core_data_log: (core_data_log adt) # vmid == (clogn + 1)} in
    let adt'' := query_oracle adt' in
    let l' := SEVENT (curid adt'') (OVM_ACTIVE vmid vcpuid) :: (slog adt'') in
    match local_set_vcpu_active vmid vcpuid (shared adt'') with
    | (sdt', halt', _) =>
      let adt0 := adt'' {halt: halt'} {shared: sdt'} {slog: l'} in
      if halt' then Some adt0 else
      let dirty0 := dirty (ctxt_states (ctxtid' @ (shadow_ctxts adt0))) in
      if dirty0 =? INVALID64 then
        let adt1 := query_oracle adt0 in
        rely (INFO_ID + vmid) @ (hlock (shared adt1));
        let l'' := SEVENT (curid adt1) (OVM_GET vmid) :: (slog adt1) in
        let inc_exe := vm_inc_exe (VB (vmid @ (vminfos (shared adt1)))) in
        if inc_exe =? 0 then
          let logn := vmid @ (data_log adt1) in
          let pc' := (doracle adt1) vmid logn in
          let adt2 := adt1 {slog: l''} {data_log: (data_log adt1) # vmid == (logn + 1)} in
          let adt3 := query_oracle adt2 in
          rely (INFO_ID + vmid) @ (hlock (shared adt3));
          let ll := SEVENT (curid adt3) (OVM_GET vmid) :: (slog adt3) in
          let info := vmid @ (vminfos (shared adt3)) in
          let num := vm_next_load_info (VB info) in
          let (_, ret) := search_load_info_loop_h (Z.to_nat num) 0 pc' 0 (VB info) in
          if ret =? 0 then Some adt3 {slog: ll} {halt: true}
          else
            let cregs' := clear_shadow_gp_regs_specx (ctxt_regs (ctxtid' @ (shadow_ctxts adt3))) in
            let logn' := vmid @ (data_log adt3) in
            let pstate' := (doracle adt3) vmid logn' in
            let cstates' := (ctxt_states (ctxtid' @ (shadow_ctxts adt3))) {pstate: pstate'} {pc: pc'} in
            let cregs'' := reset_fp_regs_specx cregs' in
            match reset_sys_regs_specx vcpuid cregs'' cstates' ((doracle adt3) vmid) (logn' + 1) with
            | (cregs''', cstates'', logn'') =>
              let cstats''' := cstates'' {dirty: 0} in
              Some adt0 {slog: ll} {data_log: (data_log adt3) # vmid == logn''}
                   {shadow_ctxts: (shadow_ctxts adt3) # ctxtid' == ((ctxtid' @ (shadow_ctxts adt3)) {ctxt_regs: cregs'''} {ctxt_states: cstats'''})}
            end
        else
          let cstates' := (ctxt_states (ctxtid' @ (shadow_ctxts adt1))) {dirty: 0} in
          Some adt1 {slog: l''} {shadow_ctxts: (shadow_ctxts adt1) # ctxtid' == ((ctxtid' @ (shadow_ctxts adt1)) {ctxt_states: cstates'})}
      else
        let cregs := ctxt_regs (ctxtid' @ (shadow_ctxts adt0)) in
        let cstates := ctxt_states (ctxtid' @ (shadow_ctxts adt0)) in
        let ec0 := ec cregs in
        let logn := vmid @ (data_log adt0) in
        match (if ec0 =? ARM_EXCEPTION_TRAP
               then sync_dirty_to_shadow_specx vmid dirty0 cregs cstates logn ((doracle adt0) vmid)
               else (cregs, cstates, logn))
        with
        | (cregs', cstates', logn') =>
          match (if (Z.land dirty0 PENDING_EXCEPT_INJECT_FLAG) =? 0
                 then update_exception_gp_regs_specx cregs' cstates'
                 else (cregs', cstates'))
          with
          | (cregs'', cstates'') =>
            match (if (Z.land dirty0 DIRTY_PC_FLAG) =? 0
                   then cstates''
                   else (cstates'' {pc: (pc cstates'') + 4}))
            with
            | cstates3 =>
              let cstates4 := cstates3 {dirty: 0} in
              let cregs3 := cregs'' {far_el2: 0} in
              let clogn := vmid @ (core_data_log adt0) in
              let addr := (core_doracle adt0) vmid clogn in
              if (PAGE_SIZE <=? addr) && (addr <? KVM_ADDR_SPACE) then
                let pte := (core_doracle adt0) vmid (clogn + 1) in
                let level := (core_doracle adt0) vmid (clogn + 2) in
                let adt1 := adt0 {core_data_log: (core_data_log adt0) # vmid == (clogn + 3)}
                                 {data_log: (data_log adt0) # vmid == logn'}
                                 {shadow_ctxts: (shadow_ctxts adt0) # ctxtid' == ((ctxtid' @ (shadow_ctxts adt0))
                                                                                   {ctxt_regs: cregs3} {ctxt_states: cstates4})}
                in prot_and_map_vm_s2pt_spec_h vmid addr pte level adt1
              else
                Some adt0 {core_data_log: (core_data_log adt0) # vmid == (clogn + 1)}
                     {data_log: (data_log adt0) # vmid == logn'}
                     {shadow_ctxts: (shadow_ctxts adt0) # ctxtid' == ((ctxtid' @ (shadow_ctxts adt0))
                                                                       {ctxt_regs: cregs3} {ctxt_states: cstates4})}
            end
          end
        end
    end
  else Some adt {halt: true}.

Definition vm_el2_restore_state_specx (regc: CtxtRegs) (ctxt: CtxtRegs) vttbr :=
  regc {vttbr_el2: vttbr} {tpidr_el2: tpidr_el2 ctxt} {hcr_el2: HCR_HYPSEC_VM_FLAGS}.

Definition activate_traps_specx (regt: TrapRegs) :=
  regt {pmuselr_el0: 0} {pmuserenr_el0: ARMV8_PMU_USERENR_MASK} {mdcr_el2: HYPSEC_MDCR_EL2_FLAG} {cptr_el2: CPTR_VM}.

Definition timer_enable_traps_specx (regt: TrapRegs) :=
  let v' := (cnthctl_el2 regt) - CNTHCTL_EL1PCEN + CNTHCTL_EL1PCTEN in
  regt {cnthctl_el2: v'}.

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

Definition core_to_vm_specx (gp: CtxtRegs) (rgp: CtxtRegs) :=
  rgp {x0: (x0 gp)} {x1: (x1 gp)} {x2: (x2 gp)} {x3: (x3 gp)}
      {x4: (x4 gp)} {x5: (x5 gp)} {x6: (x6 gp)} {x7: (x7 gp)}
      {x8: (x8 gp)} {x9: (x9 gp)} {x10: (x10 gp)} {x11: (x11 gp)}
      {x12: (x12 gp)} {x13: (x13 gp)} {x14: (x14 gp)} {x15: (x15 gp)}
      {x16: (x16 gp)} {x17: (x17 gp)} {x18: (x18 gp)} {x19: (x19 gp)}
      {x20: (x20 gp)} {x21: (x21 gp)} {x22: (x22 gp)} {x23: (x23 gp)}
      {x24: (x24 gp)} {x25: (x25 gp)} {x26: (x26 gp)} {x27: (x27 gp)}
      {x28: (x28 gp)} {x29: (x29 gp)} {x30: (x30 gp)}.

Definition vcpu_run_switch_to_vm (adt: RData) :=
  let vmid := cur_vmid adt in
  let vcpuid := cur_vcpuid adt in
  let ctxtid' := ctxt_id vmid vcpuid in
  let ctxt := ctxtid' @ (shadow_ctxts adt) in
  let creg := ctxt_regs ctxt in
  let regc := ctxt_regs (regs adt) in
  let csts := ctxt_states ctxt in
  let regt := trap_regs (regs adt) in
  let vttbr := pt_vttbr vmid in
  let regc' := vm_el2_restore_state_specx regc creg vttbr in
  let regt' := activate_traps_specx (timer_enable_traps_specx regt) in
  let regc'' := restore_sysregs_specx creg csts regc' in
  let regc3 := fpsimd_restore_state_specx creg regc'' in
  let regc4 := core_to_vm_specx creg regc3 in
  Some adt {regs: (regs adt) {ctxt_regs: regc4} {trap_regs: regt'}} {icore: false} {ihost: false}.

Definition host_vcpu_run_handler_spec  (adt: RData) : option RData :=
  match (ihost adt, icore adt) with
  | (true, false) =>
    if halt adt then Some adt else
    let adt' := vcpu_run_swith_to_core adt in
    if halt adt' then Some adt' else
    when adt'' == vcpu_run_process adt';
    if halt adt'' then Some adt'' else
    vcpu_run_switch_to_vm adt''
  | _ => None
  end.

(***********************************************************************************************************************************************)

Fixpoint grant_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
  match n with
  | O => Some (addr, adt)
  | S n' =>
    match grant_stage2_loop n' vmid addr adt with
    | Some (addr', adt') =>
      let gfn' := addr' / PAGE_SIZE in
      let adt0 := query_oracle adt' in
      rely (NPT_ID + vmid) @ (hlock (shared adt0));
      let adt' := adt0 {slog: SEVENT (curid adt0) (OVM_GET vmid) :: (slog adt0)} in
      match gfn' @ (pt (vmid @ (npts (shared adt')))) with
      | (_, _, pte) =>
        let adt1 := query_oracle adt' in
        rely (NPT_ID + vmid) @ (hlock (shared adt1));
        let adt'' := adt1 {slog: SEVENT (curid adt1) (OVM_GET vmid) :: (slog adt1)} in
        match ZMap.get gfn' (pt (vmid @ (npts (shared adt'')))) with
        | (_, level, _) =>
          let pfn := phys_page pte / PAGE_SIZE in
          if pfn =? 0 then Some (addr' + PAGE_SIZE, adt'')
          else
            let pfn' := (if level =? 2 then pfn + Z.land gfn' 511 else pfn) in
            let adt2 := query_oracle adt'' in
            rely S2PAGE_ID @ (hlock (shared adt1));
            match local_grant_vm_page vmid pfn (shared adt2) with
            | (sdt', _) =>
              Some (addr' + PAGE_SIZE, adt2 {shared: sdt'} {slog: SEVENT (curid adt2) (OGRANT vmid pfn) :: (slog adt2)})
            end
        end
      end
    | _ => None
    end
  end.

Fixpoint revoke_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
  match n with
  | O => Some (addr, adt)
  | S n' =>
    match revoke_stage2_loop n' vmid addr adt with
    | Some (addr', adt') =>
      let gfn' := addr' / PAGE_SIZE in
      let adt0 := query_oracle adt' in
      rely (NPT_ID + vmid) @ (hlock (shared adt0));
      let adt' := adt0 {slog: SEVENT (curid adt0) (OVM_GET vmid) :: (slog adt0)} in
      match gfn' @ (pt (vmid @ (npts (shared adt')))) with
      | (_, _, pte) =>
        let adt1 := query_oracle adt' in
        rely (NPT_ID + vmid) @ (hlock (shared adt1));
        let adt'' := adt1 {slog: SEVENT (curid adt1) (OVM_GET vmid) :: (slog adt1)} in
        match ZMap.get gfn' (pt (vmid @ (npts (shared adt'')))) with
        | (_, level, _) =>
          let pfn := phys_page pte / PAGE_SIZE in
          if pfn =? 0 then Some (addr' + PAGE_SIZE, adt'')
          else
            let pfn' := (if level =? 2 then pfn + Z.land gfn' 511 else pfn) in
            let adt2 := query_oracle adt'' in
            rely S2PAGE_ID @ (hlock (shared adt1)); rely NPT_ID @ (hlock (shared adt1));
            let log' := SEVENT (curid adt2) (OREVOKE vmid pfn (doracle adt2) (vmid @ (data_log adt2))) :: (slog adt2) in
            match local_revoke_vm_page vmid pfn ((doracle adt2) vmid) (vmid @ (data_log adt2)) (shared adt2) with
            | (sdt', halt', logn', _, _, _) =>
              Some (addr' + PAGE_SIZE, adt2 {halt: halt'} {shared: sdt'} {slog: log'} {data_log: (data_log adt2) # vmid == logn'})
            end
        end
      end
    | _ => None
    end
  end.

Definition vm_exit_dispatcher_spec_h (vmid vcpuid: Z) (adt: RData) :=
  let ctxt := (ctxt_id vmid vcpuid) @ (shadow_ctxts adt) in
  let cregs := ctxt_regs ctxt in
  let esrel2 := esr_el2 cregs in
  let exit_type := (esrel2 / 67108864) mod 64 in
  if exit_type =? ESR_ELx_EC_SYS64 then
    let pc := elr_el2 (ctxt_regs (regs adt)) in
    Some (adt {regs : (regs adt) {ctxt_regs : (ctxt_regs (regs adt)) {esr_el2 : pc + 4}}}, 0)
  else
    if exit_type =? ESR_ELx_EC_HVC64 then
      let arg := x0 cregs in
      let addr := x2 cregs in
      let size := x3 cregs in
      if arg =? HVC_KVM_SET_DESC_PFN then
        let len := (size + 4095) / PAGE_SIZE in
        match grant_stage2_loop (Z.to_nat len) vmid addr adt with
        | Some (_, adt') => Some (adt', 0)
        | _ => None
        end
      else
        if arg =? HVC_KVM_UNSET_DESC_PFN then
          let len := (size + 4095) / PAGE_SIZE in
          match revoke_stage2_loop (Z.to_nat len) vmid addr adt with
          | Some (_, adt') => Some (adt', 0)
          | _ => None
          end
        else Some (adt, 1)
    else Some (adt {halt: true}, 0).

Definition prep_wfx_specx (cstates: CtxtStates) :=
  cstates {dirty: DIRTY_PC_FLAG}.

Definition prep_abort_specx (cregs: CtxtRegs) (cstates: CtxtStates) (logn: Z) (doc: Z -> Z) :=
  let esr := doc logn in
  let Rd := esr / 65536 mod 32 in
  let hpfar_el2 := hpfar_el2 cregs in
  let fault_ipa := (hpfar_el2 / 16) * 4096 in
    if fault_ipa <? MAX_MMIO_ADDR then
      let cst' := cstates {dirty: DIRTY_PC_FLAG} in
      if ((Z.land esr ESR_ELx_WNR) =? 0) && ((Z.land esr ESR_ELx_S1PTW) =? 0) then
        let cst'' := cstates {dirty: (Z.shiftl 1 Rd)} in
        (cst'', logn + 1)
      else (cst', logn + 1)
    else (cstates, logn + 1).

Definition prep_hvc_spec_h (vmid vcpuid: Z) (adt: RData) :=
  let ctxtid := ctxt_id vmid vcpuid in
  let ctxt := ctxtid @ (shadow_ctxts adt) in
  let psci_fn0 := x0 (ctxt_regs ctxt) in
  let psci_fn := Z.land psci_fn0 INVALID in
  if psci_fn =? PSCI_0_2_FN_SYSTEM_OFF then
    let adt0 := query_oracle adt in
    rely (INFO_ID + vmid) @ (hlock (shared adt0));
    let l' := SEVENT (curid adt) (OVM_POWEROFF vmid) :: (slog adt0) in
    match local_set_vm_poweroff vmid (shared adt0) with
    | (sdt', _) => Some adt0 {shared: sdt'} {slog: l'}
    end
  else Some adt.

Definition deactivate_traps_specx (regt: TrapRegs) :=
  regt {pmuserenr_el0: 0} {mdcr_el2: 0} {cptr_el2: CPTR_EL2_DEFAULT }.

Definition prep_exit_vm (adt: RData) :=
  let vmid := cur_vmid adt in
  let vcpuid := cur_vcpuid adt in
  let ctxtid := ctxt_id vmid vcpuid in
  let ctxt := ctxtid @ (shadow_ctxts adt) in
  let cregs := ctxt_regs ctxt in
  let rcregs := ctxt_regs (regs adt) in
  let cregs1 := save_sysregs_specx cregs rcregs in
  let cregs2 := fpsimd_save_state_specx cregs1 rcregs in
  let rtregs1 := deactivate_traps_specx (trap_regs (regs adt)) in
  let rtregs2 := timer_enable_traps_specx rtregs1 in
  let ec' := ec cregs2 in
  match (
    if ec' =? ARM_EXCEPTION_TRAP then
      let hsr := esr_el2 cregs2 in
      let hsr_ec := Z.shiftr (Z.land hsr ESR_ELx_EC_MASK) ESR_ELx_EC_SHIFT in
      if hsr_ec =? ESR_ELx_EC_WFx then
        let cstates' := prep_wfx_specx (ctxt_states ctxt) in
        Some adt {regs:  (regs adt) {trap_regs: rtregs2}}
             {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs2} {ctxt_states: cstates'})}
      else
      if hsr_ec =? ESR_ELx_EC_HVC64 then
        let adt' := adt {regs:  (regs adt) {trap_regs: rtregs2}}
                        {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs2})} in
        prep_hvc_spec_h vmid vcpuid adt'
      else
      if (hsr_ec =? ESR_ELx_EC_IABT_LOW) || (hsr_ec =? ESR_ELx_EC_DABT_LOW) then
        match prep_abort_specx cregs2 (ctxt_states ctxt) (vmid @ (data_log adt)) ((doracle adt) vmid) with
        | (cstates', logn') =>
          Some adt {regs:  (regs adt) {trap_regs: rtregs2}} {data_log: (data_log adt) # vmid == logn'}
               {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs2} {ctxt_states: cstates'})}
        end
      else Some adt {halt: true}
    else
      Some adt {regs: (regs adt) {trap_regs: rtregs2}} {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs2})})
  with
  | Some adt1 =>
    if halt adt1 then Some adt1 else
    let adt2 := query_oracle adt1 in
    let l' := SEVENT (curid adt2) (OVM_INACTIVE vmid vcpuid) :: slog adt2 in
    match local_set_vcpu_inactive vmid vcpuid (shared adt2) with
    | (sdt', halt', _) =>
      Some adt2 {shared: sdt'} {halt: halt'} {slog: l'}
    end
  | _ => None
  end.

Definition vm_to_core_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
  gp {x0: (x0 rgp)} {x1: (x1 rgp)} {x2: (x2 rgp)} {x3: (x3 rgp)}
      {x4: (x4 rgp)} {x5: (x5 rgp)} {x6: (x6 rgp)} {x7: (x7 rgp)}
      {x8: (x8 rgp)} {x9: (x9 rgp)} {x10: (x10 rgp)} {x11: (x11 rgp)}
      {x12: (x12 rgp)} {x13: (x13 rgp)} {x14: (x14 rgp)} {x15: (x15 rgp)}
      {x16: (x16 rgp)} {x17: (x17 rgp)} {x18: (x18 rgp)} {x19: (x19 rgp)}
      {x20: (x20 rgp)} {x21: (x21 rgp)} {x22: (x22 rgp)} {x23: (x23 rgp)}
      {x24: (x24 rgp)} {x25: (x25 rgp)} {x26: (x26 rgp)} {x27: (x27 rgp)}
      {x28: (x28 rgp)} {x29: (x29 rgp)} {x30: (x30 rgp)}.

Definition exit_populate_fault_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
  gp {esr_el2: esr_el2 rgp} {ec: ec rgp} {far_el2: far_el2 rgp} {hpfar_el2: hpfar_el2 rgp}.

Definition vm_exit_pre_process (adt: RData) :=
  let vmid := cur_vmid adt in
  let vcpuid := cur_vcpuid adt in
  let ctxtid := ctxt_id vmid vcpuid in
  let ctxt := ctxtid @ (shadow_ctxts adt) in
  let cregs := ctxt_regs ctxt in
  let rcregs := ctxt_regs (regs adt) in
  let cregs1 := vm_to_core_specx cregs rcregs in
  let cregs2 := exit_populate_fault_specx cregs1 rcregs in
  let adt' := adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs2})} {icore: true} in
  let ec' := ec cregs2 in
  if ec' =? ARM_EXCEPTION_TRAP then
    match vm_exit_dispatcher_spec_h vmid vcpuid adt' with
    | Some (adt'', ret) =>
      if ret =? 0 then
        let ctxt := ctxtid @ (shadow_ctxts adt'') in
        Some (adt'' {regs: (regs adt'') {ctxt_regs: core_to_vm_specx (ctxt_regs ctxt) (ctxt_regs (regs adt''))}} {icore: false}, 0)
      else
        when adt3 == prep_exit_vm adt'';
        Some (adt3, 1)
    | _ => None
    end
  else
    if ec' =? ARM_EXCEPTION_INTERRUPT then
      when adt'' == prep_exit_vm adt';
      Some (adt'', 1)
    else Some (adt' {halt: true}, 1).

Definition host_el2_restore_state_specx (regc: CtxtRegs) vttbr :=
  regc {vttbr_el2: vttbr} {hcr_el2: HCR_HOST_NVHE_FLAGS} {tpidr_el2: 0}.

Definition core_to_host_specx (gp: CtxtRegs) (rgp: CtxtRegs): CtxtRegs :=
  rgp {x0: (x0 gp)} {x1: (x1 gp)} {x2: (x2 gp)} {x3: (x3 gp)}
      {x4: (x4 gp)} {x5: (x5 gp)} {x6: (x6 gp)} {x7: (x7 gp)}
      {x8: (x8 gp)} {x9: (x9 gp)} {x10: (x10 gp)} {x11: (x11 gp)}
      {x12: (x12 gp)} {x13: (x13 gp)} {x14: (x14 gp)} {x15: (x15 gp)}
      {x16: (x16 gp)} {x17: (x17 gp)} {x18: (x18 gp)} {x19: (x19 gp)}
      {x20: (x20 gp)} {x21: (x21 gp)} {x22: (x22 gp)} {x23: (x23 gp)}
      {x24: (x24 gp)} {x25: (x25 gp)} {x26: (x26 gp)} {x27: (x27 gp)}
      {x28: (x28 gp)} {x29: (x29 gp)} {x30: (x30 gp)}.

Definition switch_to_host (adt: RData) :=
  let vmid := HOSTVISOR in
  let adt0 := adt {cur_vmid: vmid} {cur_vcpuid: -1} in
  let vcpuid := curid adt0 in
  let ctxtid := ctxt_id vmid vcpuid in
  let cregs := ctxt_regs ctxtid @ (shadow_ctxts adt0) in
  let cstates := ctxt_states ctxtid @ (shadow_ctxts adt0) in
  let rcregs := ctxt_regs (regs adt0) in
  let vttbr := pt_vttbr HOSTVISOR in
  let rcregs1 := host_el2_restore_state_specx rcregs vttbr in
  let rcregs2 := restore_sysregs_specx cregs cstates rcregs1 in
  let rcregs3 := fpsimd_restore_state_specx cregs rcregs2 in
  let rcregs4 := core_to_host_specx cregs rcregs3 in
  adt0 {regs: (regs adt0) {ctxt_regs: rcregs4}} {cur_vcpuid: vcpuid} {ihost: true} {icore: false}.

Definition vm_exit_handler_spec  (adt: RData) : option RData :=
  match (ihost adt, icore adt) with
  | (false, false) =>
    if halt adt then Some adt else
    when ret, adt' == vm_exit_pre_process adt;
    if halt adt' then Some adt' else
    if ret =? 0 then Some adt'
    else Some (switch_to_host adt')
  | _ => None
  end.

Lemma in_range_n gfn gfn0 n :
  {gfn <= gfn0 < gfn + n} + {~ gfn <= gfn0 < gfn + n}.
Proof.
  destruct (zle gfn gfn0);
  destruct (zlt gfn0 (gfn + n));
  try omega; try (left; omega); try (right; red; intro; omega).
Qed.

Lemma local_mmap_level2:
  forall vmid addr pte npt npt',
    local_mmap_h vmid addr 2 pte npt = (false, npt') ->
    let gfn := (addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD) in
    forall gfn0, if in_range_n gfn gfn0 512 then gfn0 @ (pt npt') = (phys_page pte / PAGE_SIZE + gfn0 - gfn, 2, pte)
            else gfn0 @ (pt npt') = gfn0 @ (pt npt).
Proof.
  intros. unfold local_mmap_h in H. simpl_bool_eq.
  repeat simpl_hyp H; inv H. simpl.
  assert(Hloop: forall n gfn pfn level pte npt gfn' pfn' npt' (Hloop: local_mmap_loop_h n gfn pfn level pte npt = (gfn', pfn', npt')),
            gfn' = gfn + (Z.of_nat n) /\ pfn' = pfn + (Z.of_nat n) /\
            forall gfn0, if in_range_n gfn gfn0 (Z.of_nat n) then gfn0 @ npt' = (pfn + gfn0 - gfn, level, pte)
                    else gfn0 @ npt' = gfn0 @ npt).
  { clear C0. induction n. intros. simpl in *. inv Hloop. split_and; try omega.
    intros. destruct in_range_n. omega. reflexivity.
    intros. simpl in Hloop. repeat simpl_hyp Hloop; inversion Hloop.
    rewrite Nat2Z.inj_succ, succ_plus_1. apply IHn in C0. destruct C0 as (? & ? & ?).
    split_and; try omega. intros. pose proof (H4 gfn2). repeat destruct in_range_n; try omega.
    assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). assumption.
    assert(gfn2 = z1) by omega. rewrite H6. rewrite ZMap.gss.
    assert(z2 = pfn + z1 - gfn1) by omega. rewrite H7. reflexivity.
    assert(gfn2 <> z1) by omega. rewrite (ZMap.gso _ _ H6). assumption. }
  apply Hloop in C0. destruct C0 as (? & ? & ?). apply H1.
Qed.

Lemma local_mmap_level3:
  forall vmid addr pte npt npt',
    local_mmap_h vmid addr 3 pte npt = (false, npt') ->
    (pt npt') = (pt npt) # (addr / PAGE_SIZE) == (phys_page pte / PAGE_SIZE, 3, pte).
Proof.
  intros. unfold local_mmap_h in H. replace (3 =? 2) with false in H by reflexivity.
  repeat simpl_hyp H; try inv H. simpl in C3. inv C3. reflexivity.
Qed.

Lemma local_spt_map_pt:
  forall cbndx index addr pte spt spt',
    local_spt_map_h cbndx index addr pte spt = (false, spt') ->
    (spt_pt spt') = (spt_pt spt) # (SMMU_TTBR index cbndx) == (((SMMU_TTBR index cbndx) @ (spt_pt spt)) # (addr / PAGE_SIZE) == (phys_page pte / PAGE_SIZE, pte)).
Proof.
  intros. unfold local_spt_map_h in H.
  repeat simpl_hyp H; try inv H. reflexivity.
Qed.

Local Opaque local_mmap_h local_spt_map_h.
```
