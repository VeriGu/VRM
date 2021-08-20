# TrapHandlerSpec

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

Require Import TrapHandlerRaw.Layer.
Require Import RData.
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

Section HighPTSpec.

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

  Opaque local_mmap_h local_spt_map_h.

End HighPTSpec.

Section ConcurrentSpec.

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

  Definition local_verify_vm vmid sdt :=
    let info := vmid @ (vminfos sdt) in
    let state := vm_state (VS info) in
    if (INFO_ID + vmid) @ (hlock sdt) then
      if state =? READY then
        (sdt, false, Some info)
      else
        (sdt {hlock: (hlock sdt) # (INFO_ID + vmid) == false}, true, Some info)
    else
      let info' := info {vm_state: VERIFIED} in
      (sdt {vminfos: (vminfos sdt) # vmid == info'} {hlock: (hlock sdt) # (INFO_ID + vmid) == true}, false, Some info').

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

  Opaque query_oracle.

End ConcurrentSpec.

Section AuxSpec.

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
        match local_assign_pfn_to_vm vmid gfn' pfn' ((doracle adt0) vmid) (vmid @ (data_log adt0)) (shared adt0) with
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

  Fixpoint clear_vm_loop_h n pfn vmid adt :=
    match n with
    | O => Some (pfn, adt)
    | S n' =>
      match clear_vm_loop_h n' pfn vmid adt with
      | Some (pfn', adt') =>
        if halt adt' then Some (pfn' + 1, adt') else
        let adt1 := query_oracle adt' in
        rely S2PAGE_ID @ (hlock (shared adt1)); rely NPT_ID @ (hlock (shared adt1));
        let log' := SEVENT (curid adt1) (OCLEAR_VM vmid pfn') :: (slog adt1) in
        match local_clear_vm_page vmid pfn' (shared adt1) with
        | (sdt', halt', _, _, _) =>
          Some (pfn' + 1, adt1 {shared: sdt'} {halt: halt'} {slog: log'})
        end
      | _ => None
      end
    end.

  Fixpoint unmap_and_load_loop_h n vmid start target remap adt :=
    match n with
    | O => Some (start, target, remap, adt)
    | S n' =>
      match unmap_and_load_loop_h n' vmid start target remap adt with
      | Some (start', target', remap', adt') =>
        if halt adt' then
          Some (start' + PMD_SIZE, start' + PMD_SIZE, remap' + (start' + PMD_SIZE - target'), adt')
        else
          let adt0 := query_oracle adt' in
          rely (NPT_ID + COREVISOR) @ (hlock (shared adt0));
          let adt'' := adt0 {slog: SEVENT (curid adt0) (OPT_GET COREVISOR) :: (slog adt0)} in
          match (remap' / PAGE_SIZE) @ (pt (COREVISOR @ (npts (shared adt'')))) with
          | (_, _, pte) =>
            let pfn := phys_page pte / PMD_SIZE * PTRS_PER_PMD in
            let gfn := start' / PAGE_SIZE in
            if pte =? 0 then
              Some (start' + PMD_SIZE, start' + PMD_SIZE, remap' + (start' + PMD_SIZE - target'), adt'' {halt: true})
            else
              match prot_and_map_vm_s2pt_spec_h vmid (gfn * PAGE_SIZE) (pfn * PAGE_SIZE) 2 adt'' with
              | Some adt1 =>
                Some (start' + PMD_SIZE, start' + PMD_SIZE, remap' + (start' + PMD_SIZE - target'), adt1)
              | _ => None
              end
          end
      | _ => None
      end
    end.

  Fixpoint verify_and_load_loop_h n vmid load_idx adt :=
    match n with
    | O => Some (load_idx, adt)
    | S n' =>
      match verify_and_load_loop_h n' vmid load_idx adt with
      | Some (idx', adt') =>
        let info := vmid @ (vminfos (shared adt')) in
        let load_addr := idx' @ (vm_load_addr (VB info)) in
        let remap_addr := idx' @ (vm_remap_addr (VB info)) in
        let mapped := idx' @ (vm_mapped_pages (VB info)) in
        let start := load_addr / PMD_SIZE * PMD_SIZE in
        let end' := load_addr + mapped * PAGE_SIZE in
        let num := (end' - start + 2097151) / PMD_SIZE in
        match unmap_and_load_loop_h (Z.to_nat num) vmid start load_addr remap_addr adt' with
        | Some (start', target', remap', adt'') =>
          Some (load_idx + 1, adt'')
        | _ => None
        end
      | _ => None
      end
    end.

  Fixpoint kvm_phys_addr_ioremap_loop_h n vmid gpa pa adt :=
    match n with
    | O => Some (gpa, pa, adt)
    | S n' =>
      match kvm_phys_addr_ioremap_loop_h n' vmid gpa pa adt with
      | Some (gpa', pa', adt') =>
        if halt adt' then
          Some (gpa' + PAGE_SIZE, pa' + PAGE_SIZE, adt')
        else
          let adt1 := query_oracle adt' in
          rely (INFO_ID + vmid) @ (hlock (shared adt1)); rely S2PAGE_ID @ (hlock (shared adt1));
          rely (NPT_ID + vmid) @ (hlock (shared adt1));
          let log' :=  SEVENT (curid adt1) (OMAP_IO vmid gpa' pa') :: (slog adt1) in
          match local_map_io vmid gpa' pa' (shared adt1) with
          | (sdt', halt', _, _, _) =>
            Some (gpa' + PAGE_SIZE, pa' + PAGE_SIZE, adt1 {shared: sdt'} {halt: halt'} {slog: log'})
          end
      | _ => None
      end
    end.

  Fixpoint is_smmu_range_loop_h n addr i res conf :=
    match n with
    | O => (i, res)
    | S n' =>
      match is_smmu_range_loop_h n' addr i res conf with
      | (i', res') =>
        if (i' @ (smmu_phys_base conf) <=? addr) && (addr <? i' @ (smmu_phys_base conf) + i' @ (smmu_size conf))
        then (i' + 1, i')
        else (i' + 1, res')
      end
    end.

  Definition handle_host_mmio_spec_h index fault_ipa len is_write rt cregs cstates rcregs dorc logn smmu :=
    if is_write =? 0 then
      let data := dorc logn in
      if len =? 8 then
        match set_shadow_ctxt_specx rt data cregs cstates with
        | (cregs', cstates') =>
          (false, logn + 1, cregs', cstates', rcregs {esr_el2: (elr_el2 rcregs) + 4})
        end
      else if len =? 4 then
             match set_shadow_ctxt_specx rt (Z.land data INVALID) cregs cstates with
             | (cregs', cstates') =>
               (false, logn + 1, cregs', cstates', rcregs {esr_el2: (elr_el2 rcregs) + 4})
             end
           else (true, logn, cregs, cstates, rcregs)
    else
      let data := get_shadow_ctxt_specx rt cregs cstates in
      let ret_state := (if len =? 8 then (false, logn, cregs, cstates, rcregs {esr_el2: (elr_el2 rcregs) + 4})
                        else if len =? 4 then (false, logn, cregs, cstates, rcregs {esr_el2: (elr_el2 rcregs) + 4})
                             else (true, logn, cregs, cstates, rcregs)) in
      let offset := Z.land fault_ipa SMMU_OFFSET_MASK in
      if offset <? Spec.SMMU_GLOBAL_BASE
      then
        let ret :=
          (if (offset >=? 0) && (offset <=? ARM_SMMU_GR1_BASE)
            then
              if offset =? ARM_SMMU_GR0_sCR0
              then let smmu_enable := Z.land (Z.shiftr data sCR0_SMCFCFG_SHIFT) 1 in if smmu_enable =? 0 then 0 else 1
              else if offset =? ARM_SMMU_GR0_sCR2 then if Z.land data 255 =? 0 then 1 else 0 else 1
            else
              if (offset >=? ARM_SMMU_GR1_BASE) && (offset <? ARM_SMMU_GR1_END)
              then
                let n := (offset - ARM_SMMU_GR1_BASE) / 4 in
                let vmid := (smmu_id index n) @ smmu in
                let type := Z.shiftr data CBAR_TYPE_SHIFT in
                let t_vmid := Z.land data CBAR_VMID_MASK in
                if vmid =? 0 then 1 else if (type =? CBAR_TYPE_S2_TRANS) && (vmid =? t_vmid) then 1 else 0
              else 1) in
        if ret =? 0 then (true, logn, cregs, cstates, rcregs)
        else  ret_state
      else
        let off' := offset - Spec.SMMU_GLOBAL_BASE in
        let cb_offset := Z.land off' ARM_SMMU_PGSHIFT_MASK in
        if cb_offset =? ARM_SMMU_CB_TTBR0
        then
          let cbndx := Z.shiftr (offset - Spec.SMMU_GLOBAL_BASE) Spec.ARM_SMMU_PGSHIFT in
          ret_state
        else
          if cb_offset =? ARM_SMMU_CB_CONTEXTIDR
          then (true, logn, cregs, cstates, rcregs)
          else ret_state.

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

  Fixpoint grant_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
    match n with
    | O => Some (addr, adt)
    | S n' =>
      match grant_stage2_loop n' vmid addr adt with
      | Some (addr', adt') =>
        let gfn' := addr' / PAGE_SIZE in
        let adt0 := query_oracle adt' in
        rely (NPT_ID + vmid) @ (hlock (shared adt0));
        let adt' := adt0 {slog: SEVENT (curid adt0) (OPT_GET vmid) :: (slog adt0)} in
        match gfn' @ (pt (vmid @ (npts (shared adt')))) with
        | (_, _, pte) =>
          let adt1 := query_oracle adt' in
          rely (NPT_ID + vmid) @ (hlock (shared adt1));
          let adt'' := adt1 {slog: SEVENT (curid adt1) (OPT_GET vmid) :: (slog adt1)} in
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
        let adt' := adt0 {slog: SEVENT (curid adt0) (OPT_GET vmid) :: (slog adt0)} in
        match gfn' @ (pt (vmid @ (npts (shared adt')))) with
        | (_, _, pte) =>
          let adt1 := query_oracle adt' in
          rely (NPT_ID + vmid) @ (hlock (shared adt1));
          let adt'' := adt1 {slog: SEVENT (curid adt1) (OPT_GET vmid) :: (slog adt1)} in
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

  Lemma set_shadow_ctxt_dirty:
    forall index val cregs cstates cregs' cstates',
      set_shadow_ctxt_specx index val cregs cstates = (cregs', cstates') ->
      index <> DIRTY ->
      dirty cstates' = dirty cstates.
  Proof.
    intros. hsimpl_func H; try reflexivity.
    bool_rel; autounfold in *; omega.
  Qed.

End AuxSpec.

Section TrapHandlerSpec.

  Definition host_hvc_handler_spec (adt: RData) : option RData :=
    match (ihost adt, icore adt) with
    | (true, false) =>
      if halt adt then Some adt else
      let vmid := cur_vmid adt in
      let vcpuid := cur_vcpuid adt in
      let ctxtid := ctxt_id vmid vcpuid in
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      let ctxt' := ctxt {ctxt_regs: host_to_core_specx (ctxt_regs ctxt) (ctxt_regs (regs adt))} in
      let adt' := adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'} {icore: true} in
      let cregs' := ctxt_regs ctxt' in
      let cstates' := ctxt_states ctxt' in
      match x0 cregs', x1 cregs', x2 cregs', x3 cregs', x4 cregs', x5 cregs' with
      | arg, arg1, arg2, arg3, arg4, arg5 =>
        match (
            if arg =? HVC_TIMER_SET_CNTVOFF then
              Some adt'
            else
            if arg =? HVC_CLEAR_VM_S2_RANGE then
              if is_vm arg1 && is_paddr arg2 && is_paddr arg3 then
                let adt1 := query_oracle adt' in
                rely (NPT_ID + arg1) @ (hlock (shared adt1));
                let info := arg1 @ (vminfos (shared adt1)) in
                let adt'' := adt1 {slog: SEVENT (curid adt1) (OVM_GET vmid) :: (slog adt1)} in
                if vm_state (VS info) =? POWEROFF then
                  let pfn := arg2 / PAGE_SIZE in
                  let num := arg3 / PAGE_SIZE in
                  match clear_vm_loop_h (Z.to_nat num) pfn arg1 adt'' with
                  | Some (_, adt0) => Some adt0
                  | _ => None
                  end
                else Some adt''
              else Some adt' {halt: true}
            else
            if arg =? HVC_SET_BOOT_INFO then
              if is_vm arg1 && is_paddr arg2 && is_paddr arg1 && is_pfn (arg2 + arg3) then
                let adt1 := query_oracle adt' in
                rely (INFO_ID + arg1) @ (hlock (shared adt1)); rely CORE_ID @ (hlock (shared adt1));
                let log' := SEVENT (curid adt1) (OBOOT_INFO arg1 arg2 arg3) :: (slog adt1) in
                match local_set_boot_info arg1 arg2 arg3 (shared adt1) with
                | (sdt', halt', _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_REMAP_VM_IMAGE then
              if is_vm arg1 && is_pfn arg3 && is_load_idx arg3 then
                let adt1 := query_oracle adt' in
                rely (INFO_ID + arg1) @ (hlock (shared adt1)); rely (NPT_ID + COREVISOR) @ (hlock (shared adt1));
                let log' := SEVENT (curid adt1) (OREMAP_IMAGE arg1 arg2 arg3) :: (slog adt1) in
                match local_remap_vm_image arg1 arg2 arg3 (shared adt1) with
                | (sdt', halt', _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_VERIFY_VM_IMAGE then
              if is_vm arg1 then
                let adt1 := query_oracle adt' in
                rely (INFO_ID + arg1) @ (hlock (shared adt1));
                let info := arg1 @ (vminfos (shared adt1)) in
                let state := vm_state (VS info) in
                let sdt' := (shared adt1) {hlock: (hlock (shared adt1)) # (INFO_ID + vmid) == false} in
                let adt'' := adt1 {slog: SEVENT (curid adt1) (OVERIFY arg1) :: (slog adt1)} {shared: sdt'} in
                if state =? READY then
                  let cnt := vm_next_load_info (VB info) in
                  match verify_and_load_loop_h (Z.to_nat cnt) arg1 0 adt'' with
                  | Some (_, adt0) =>
                    if halt adt0 then Some adt0 else
                    let info' := info {vm_state: VERIFIED} in
                    let hlock' := (hlock (shared adt0)) # (INFO_ID + arg1) == true in
                    Some adt0 {shared: (shared adt0) {hlock: hlock'} {vminfos: (vminfos (shared adt0)) # arg1 == info'}}
                         {slog: SEVENT (curid adt0) (OVERIFY arg1) :: (slog adt0)}
                  | _ => None
                  end
                else Some adt'' {halt: true}
              else Some adt' {halt: true}
            else
            if arg =? HVC_SMMU_FREE_PGD then
              if is_smmu_cfg arg1 && is_smmu arg2 then
                let adt1 := query_oracle adt' in
                rely SMMU_ID @ (hlock (shared adt1)); rely (INFO_ID + vmid) @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OSMMU_FREE arg1 arg2) :: (slog adt1) in
                match local_free_smmu_pgd arg1 arg2 (shared adt1) with
                | (sdt', halt', _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_SMMU_ALLOC_PGD then
              if is_smmu_cfg arg1 && (HOSTVISOR <=? arg2) && (arg2 <? COREVISOR) && is_smmu arg3 then
                let adt1 := query_oracle adt' in
                let num := arg3 @ (smmu_dev_context_banks (smmu_conf adt1)) in
                rely SMMU_ID @ (hlock (shared adt1)); rely (INFO_ID + vmid) @ (hlock (shared adt1));
                rely SPT_ID @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OSMMU_ALLOC arg1 arg2 arg3 num) :: (slog adt1) in
                match local_alloc_smmu_pgd arg1 arg2 arg3 num (shared adt1) with
                | (sdt', halt', _, _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_SMMU_LPAE_MAP then
              if is_paddr arg1 && is_paddr arg2 && (0 <=? arg3) && (arg3 <? 9223372036854775807) && (phys_page arg3 =? 0) && is_smmu_cfg arg4 && is_smmu arg5 then
                let pfn := arg2 / PAGE_SIZE in
                let gfn := arg1 / PAGE_SIZE in
                let pte :=  Z.lor arg2 (Z.lor arg3 PTE_AF_OR_SH_IS) in
                let adt1 := query_oracle adt' in
                rely SMMU_ID @ (hlock (shared adt1)); rely (INFO_ID + vmid) @ (hlock (shared adt1));
                rely S2PAGE_ID @ (hlock (shared adt1)); rely NPT_ID @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OASSIGN_SMMU arg4 arg5 pfn gfn) :: (slog adt1) in
                match local_smmu_assign_page arg4 arg5 pfn gfn (shared adt1) with
                | (sdt', halt', _, _, _, _) =>
                  let adt'' := adt1 {shared: sdt'} {halt: halt'} {slog: log'} in
                  if halt adt'' then Some adt'' else
                  let adt2 := query_oracle adt'' in
                  let vmid := (smmu_id arg4 arg5) @ (smmu_vmid (shared adt2)) in
                  rely SMMU_ID @ (hlock (shared adt2)); rely (INFO_ID + vmid) @ (hlock (shared adt2));
                  rely SPT_ID @ (hlock (shared adt2)); rely SPT_ID @ (hlock (shared adt2));
                  let log'' :=  SEVENT (curid adt2) (OSMMU_MAP arg4 arg5 arg1 pte) :: (slog adt2) in
                  match local_smmu_map_page arg4 arg5 arg1 pte (shared adt2) with
                  | (sdt'', halt'', _, _, _, _) =>
                    Some adt2 {shared: sdt''} {halt: halt''} {slog: log''}
                  end
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_SMMU_LPAE_IOVA_TO_PHYS then
              if is_paddr arg1 && is_smmu_cfg arg2 && is_smmu arg3 then
                let adt1 := query_oracle adt' in
                rely SPT_ID @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OSMMU_GET) :: (slog adt1) in
                let ttbr := SMMU_TTBR arg3 arg2 in
                match (arg1 / PAGE_SIZE) @ (ttbr @ (spt_pt (spts (shared adt1)))) with
                | (pfn, pte) =>
                  let ret := phys_page pte + (Z.land arg1 4095) in
                  Some adt1 {shadow_ctxts: (shadow_ctxts adt') # ctxtid == (ctxt' {ctxt_regs: (ctxt_regs ctxt') {x0: ret}})}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_SMMU_CLEAR then
              if is_paddr arg1 && is_smmu_cfg arg2 && is_smmu arg3 then
                let adt1 := query_oracle adt' in
                let vmid := (smmu_id arg2 arg3) @ (smmu_vmid (shared adt1)) in
                rely SMMU_ID @ (hlock (shared adt1)); rely (INFO_ID + vmid) @ (hlock (shared adt1));
                rely S2PAGE_ID @ (hlock (shared adt1)); rely SPT_ID @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OSMMU_CLEAR arg1 arg2 arg3) :: (slog adt1) in
                match local_smmu_clear arg1 arg2 arg3 (shared adt1) with
                | (sdt', halt', _, _, _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_PHYS_ADDR_IOREMAP then
              if is_vm arg1 && is_addr arg2 && is_paddr arg3 && is_paddr arg4 && is_addr (arg2 + ((arg4 + 4095) / PAGE_SIZE) * PAGE_SIZE) && 
			     is_paddr (arg3 + ((arg4 + 4095) / PAGE_SIZE) * PAGE_SIZE) && (0 <=? arg4) then
                let num := (arg4 + 4095) / PAGE_SIZE in
                match kvm_phys_addr_ioremap_loop_h (Z.to_nat num) arg1 arg2 arg3 adt' with
                | Some (_, _, adt'') => Some adt''
                | _ => None
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_REGISTER_KVM then
              let adt1 := query_oracle adt' in
              rely CORE_ID @ (hlock (shared adt1));
              let log' :=  SEVENT (curid adt1) (OGEN_VMID) :: (slog adt1) in
              let vmid := next_vmid (core_data (shared adt1)) in
              match local_gen_vmid (shared adt1) with
              | (sdt', halt', _) =>
                let adt'' := adt1 {shared: sdt'} {halt: halt'} {slog: log'} in
                if halt adt'' then Some adt'' else
                let adt2 := query_oracle adt'' in
                rely (INFO_ID + vmid) @ (hlock (shared adt2));
                let log'' :=  SEVENT (curid adt2) (OREG_KVM vmid) :: (slog adt2) in
                match local_register_kvm vmid (shared adt2) with
                | (sdt'', halt'', _) =>
                  Some adt2 {shared: sdt''} {halt: halt''} {slog: log''}
                        {shadow_ctxts: (shadow_ctxts adt') # ctxtid == (ctxt' {ctxt_regs: (ctxt_regs ctxt') {x0: vmid}})}
                end
              end
            else
            if arg =? HVC_REGISTER_VCPU then
              if is_vm arg1 && is_vcpu arg2 then
                let adt1 := query_oracle adt' in
                rely (INFO_ID + arg1) @ (hlock (shared adt1));
                let log' :=  SEVENT (curid adt1) (OREG_VCPU arg1 arg2) :: (slog adt1) in
                match local_register_vcpu arg1 arg2 (shared adt1) with
                | (sdt', halt', _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_ENCRYPT_BUF then
              if is_vm arg1 && is_paddr arg2 && is_paddr arg3 then
                let adt1 := query_oracle adt' in
                rely S2PAGE_ID @ (hlock (shared adt1));
                let dorc := (doracle adt1) HOSTVISOR in
                let logn := HOSTVISOR @ (data_log adt1) in
                let log' :=  SEVENT (curid adt1) (OSAVE_ENC_BUF arg1 arg2 arg3 dorc logn) :: (slog adt1) in
                match local_save_encrypt_buf arg1 arg2 arg3 dorc logn (shared adt1) with
                | (sdt', halt', logn', _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt1) # HOSTVISOR == logn'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_DECRYPT_BUF then
              if is_vm arg1 && is_paddr arg2 then
                let adt1 := query_oracle adt' in
                rely S2PAGE_ID @ (hlock (shared adt1)); rely (INFO_ID + arg1) @ (hlock (shared adt1));
                rely NPT_ID @ (hlock (shared adt1));
                let dorc := (doracle adt1) HOSTVISOR in
                let logn := HOSTVISOR @ (data_log adt1) in
                let log' :=  SEVENT (curid adt1) (OLOAD_ENC_BUF arg1 arg2 dorc logn) :: (slog adt1) in
                match local_load_decrypt_buf arg1 arg2 dorc logn (shared adt1) with
                | (sdt', halt', logn', _, _, _, _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt1) # HOSTVISOR == logn'}
                end
              else Some adt' {halt: true}
            else
            if arg =? HVC_SAVE_CRYPT_VCPU then
              if is_vm arg1 && is_vcpu arg2 then
                Some adt'
              else Some adt' {halt: true}
            else
            if arg =? HVC_LOAD_CRYPT_VCPU then
              if is_vm arg1 && is_vcpu arg2 then
                let adt1 := query_oracle adt' in
                rely (INFO_ID + arg1) @ (hlock (shared adt1));
                let dorc := (doracle adt1) HOSTVISOR in
                let logn := HOSTVISOR @ (data_log adt1) in
                let log' :=  SEVENT (curid adt1) (OLOAD_ENC_VCPU arg1 arg2 cregs' cstates' dorc logn) :: (slog adt1) in
                match local_load_encryted_vcpu arg1 arg2 cregs' cstates' dorc logn (shared adt1) with
                | (sdt', halt', cregs'', cstates'', logn', _) =>
                  Some adt1 {shared: sdt'} {halt: halt'} {slog: log'} {data_log: (data_log adt1) # HOSTVISOR == logn'}
                       {shadow_ctxts: (shadow_ctxts adt') # ctxtid == (ctxt' {ctxt_regs: cregs''} {ctxt_states: cstates''})}
                end
              else Some adt' {halt: true}
            else Some adt'
          )
        with
        | Some adt'' =>
          if halt adt'' then Some adt'' else
          let ctxt := ctxtid @ (shadow_ctxts adt'') in
          Some adt'' {regs: (regs adt'') {ctxt_regs: core_to_host_specx (ctxt_regs ctxt) (ctxt_regs (regs adt''))}}
              {icore: false}
        | _ => None
        end
      end
    | _ => None
    end.

  Definition host_npt_handler_spec (adt: RData) : option RData :=
    match (ihost adt, icore adt) with
    | (true, false) =>
      if halt adt then Some adt else
      let vmid := cur_vmid adt in
      let vcpuid := cur_vcpuid adt in
      let ctxtid := ctxt_id vmid vcpuid in
      let ctxt := ctxtid @ (shadow_ctxts adt) in
      let ctxt' := ctxt {ctxt_regs: host_to_core_specx (ctxt_regs ctxt) (ctxt_regs (regs adt))} in
      let adt' := adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'} {icore: true} in
      let hpfar := hpfar_el2 (ctxt_regs (regs adt')) in
      let addr := Z.land hpfar HPFAR_MASK * 256 in
      if is_addr addr then
        let esr := esr_el2 (ctxt_regs (regs adt')) in
        match (
            let fault_ipa := Z.lor addr (Z.land (far_el2 (ctxt_regs (regs adt'))) 4095) in
            let len := host_dabt_get_as' esr in
            let is_write := host_dabt_is_write' esr in
            let rt := host_dabt_get_rd' esr in
            let adt0 := query_oracle adt' in
            let log' := SEVENT (curid adt) (OSMMU_GET) :: (slog adt0) in
            rely SMMU_ID @ (hlock (shared adt0));
            let conf := smmu_conf adt' in
            let num := smmu_num conf in
            let (_, res) := is_smmu_range_loop_h (Z.to_nat num) addr 0 INVALID conf in
            if res =? INVALID then
              let adt'' := adt0 {slog: log'} in
              let adt1 := query_oracle adt'' in
              let log' := SEVENT (curid adt1) (OMAP_HOST addr) :: (slog adt1) in
              rely S2PAGE_ID @ (hlock (shared adt1)); rely NPT_ID @ (hlock (shared adt1));
              match local_map_host addr (shared adt1) with
              | (sdt', halt', _, _) =>
                Some adt1 {shared: sdt'} {halt: halt'} {slog: log'}
              end
            else
              let smmu := smmu_vmid (shared adt0) in
              let logn := HOSTVISOR @ (data_log adt0) in
              match handle_host_mmio_spec_h res fault_ipa len is_write rt (ctxt_regs ctxt') (ctxt_states ctxt') (ctxt_regs (regs adt0)) ((doracle adt0) HOSTVISOR) logn smmu with
              | (halt', logn', cregs', cstates', rcregs') =>
                Some adt0 {halt: halt'} {slog: log'} {regs: (regs adt) {ctxt_regs: rcregs'}} {data_log: (data_log adt) # HOSTVISOR == logn'}
                    {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt' {ctxt_regs: cregs'} {ctxt_states: cstates'})}
              end
          )
        with
        | Some adt'' =>
          if halt adt'' then Some adt'' else
          let ctxt := ctxtid @ (shadow_ctxts adt'') in
          Some adt'' {regs: (regs adt'') {ctxt_regs: core_to_host_specx (ctxt_regs ctxt) (ctxt_regs (regs adt''))}}
                {icore: false}
        | _ => None
        end
      else Some adt' {halt: true}
    | _ => None
    end.

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

End TrapHandlerSpec.

Section TrapHandlerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := TrapHandlerRaw_ops) LDATA).

  Definition host_hvc_handler_spec0  (adt: RData) : option RData :=
    host_hvc_handler_raw_spec adt.

  Definition host_npt_handler_spec0  (adt: RData) : option RData :=
    host_npt_handler_raw_spec adt.

  Definition host_vcpu_run_handler_spec0  (adt: RData) : option RData :=
    host_vcpu_run_handler_raw_spec adt.

  Definition vm_exit_handler_spec0  (adt: RData) : option RData :=
    vm_exit_handler_raw_spec adt.

  Definition mem_load_spec0 (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    mem_load_ref_spec gfn reg adt.

  Definition mem_store_spec0 (gfn: Z64) (reg: Z) (adt: RData) : option RData :=
    mem_store_ref_spec gfn reg adt.

  Definition dev_load_spec0 (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    dev_load_ref_spec gfn reg cbndx index adt.

  Definition dev_store_spec0 (gfn: Z64) (reg: Z) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    dev_load_ref_spec gfn reg cbndx index adt.

  Inductive host_hvc_handler_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_hvc_handler_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_hvc_handler_spec  labd = Some labd'):
      host_hvc_handler_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive host_npt_handler_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_npt_handler_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_npt_handler_spec  labd = Some labd'):
      host_npt_handler_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive host_vcpu_run_handler_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_vcpu_run_handler_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: host_vcpu_run_handler_spec  labd = Some labd'):
      host_vcpu_run_handler_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive vm_exit_handler_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | vm_exit_handler_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: vm_exit_handler_spec  labd = Some labd'):
      vm_exit_handler_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive mem_load_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | mem_load_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg
      (Hinv: high_level_invariant labd)
      (Hspec: mem_load_spec (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) labd = Some labd'):
      mem_load_spec_low_step s WB ((Vlong gfn)::(Vint reg)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive mem_store_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | mem_store_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg
      (Hinv: high_level_invariant labd)
      (Hspec: mem_store_spec (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) labd = Some labd'):
      mem_store_spec_low_step s WB ((Vlong gfn)::(Vint reg)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive dev_load_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | dev_load_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: dev_load_spec (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      dev_load_spec_low_step s WB ((Vlong gfn)::(Vint reg)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive dev_store_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | dev_store_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' gfn reg cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: dev_store_spec (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      dev_store_spec_low_step s WB ((Vlong gfn)::(Vint reg)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition host_hvc_handler_spec_low: compatsem LDATAOps :=
      csem host_hvc_handler_spec_low_step (type_of_list_type nil) Tvoid.

    Definition host_npt_handler_spec_low: compatsem LDATAOps :=
      csem host_npt_handler_spec_low_step (type_of_list_type nil) Tvoid.

    Definition host_vcpu_run_handler_spec_low: compatsem LDATAOps :=
      csem host_vcpu_run_handler_spec_low_step (type_of_list_type nil) Tvoid.

    Definition vm_exit_handler_spec_low: compatsem LDATAOps :=
      csem vm_exit_handler_spec_low_step (type_of_list_type nil) Tvoid.

    Definition mem_load_spec_low: compatsem LDATAOps :=
      csem mem_load_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

    Definition mem_store_spec_low: compatsem LDATAOps :=
      csem mem_store_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

    Definition dev_load_spec_low: compatsem LDATAOps :=
      csem dev_load_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition dev_store_spec_low: compatsem LDATAOps :=
      csem dev_store_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End TrapHandlerSpecLow.

```
