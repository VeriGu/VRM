# RData

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Constants.
Require Import GenSem.

Require Import liblayers.compat.CompatLayers.

Open Local Scope Z_scope.

Section DataType.

  Record Memblock :=
    mkMemblock {
        mb_base: Z;
        mb_size: Z;
        mb_flag: Z;
        mb_index: Z
      }.

  Record CoreData :=
    mkCoreData {
        next_vmid: Z;
        next_remap_ptr: Z
      }.

  Record S2Page :=
    mkS2Page {
        s2_owner: Z;
        s2_count: Z;
        s2_gfn: Z
      }.

  Inductive NPT_UPDATE :=
  | UPDATE_PGD (addr: Z) (val: Z)
  | UPDATE_PUD (addr: Z) (val: Z)
  | UPDATE_PMD (addr: Z) (val: Z)
  | UPDATE_PTE (addr: Z) (val: Z).

  Record NPT :=
    mkNPT {
        (* low level *)
        pt_vttbr_pool: ZMap.t Z;
        pt_pgd_pool: ZMap.t Z;
        pt_pud_pool: ZMap.t Z;
        pt_pmd_pool: ZMap.t Z;
        pt_pgd_next: Z;
        pt_pud_next: Z;
        pt_pmd_next: Z;
        pt_pgd_par: ZMap.t Z;
        pt_pud_par: ZMap.t Z;
        pt_pmd_par: ZMap.t Z;
        pt_updates: list NPT_UPDATE;

        (* high level *)
        pt: ZMap.t (Z * Z * Z);
        pgd_t : ZMap.t bool;
        pud_t : ZMap.t (ZMap.t bool);
        pmd_t : ZMap.t (ZMap.t (ZMap.t bool))
      }.

  Record BootInfo :=
    mkBootInfo {
        vm_next_load_info: Z;
        (* vmid -> load_info_id -> load_info *)
        vm_load_addr: ZMap.t Z;
        vm_load_size: ZMap.t Z;
        vm_remap_addr: ZMap.t Z;
        vm_inc_exe: Z;
        vm_mapped_pages: ZMap.t Z
      }.

  Record StateInfo :=
    mkStateInfo {
        vm_kvm: Z;
        vm_vcpu: ZMap.t Z;
        vm_state: Z;
        vm_vcpu_state: ZMap.t Z;
        vm_power: Z
      }.

  Record VMInfo :=
    mkVMInfo {
        VS: StateInfo;
        VB: BootInfo
      }.

  Record SMMUConf :=
    mkSMMUConfig {
        smmu_num: Z;

        (* per device config *)
        smmu_phys_base: ZMap.t Z;
        smmu_size: ZMap.t Z;
        smmu_pgshift: ZMap.t Z;

        smmu_features: ZMap.t Z;

        smmu_options: ZMap.t Z;
        smmu_dev_context_banks: ZMap.t Z;
        num_s2_context_banks: ZMap.t Z;

        smmu_dev_mapping_groups: ZMap.t Z;

        smmu_va_size: ZMap.t Z;
        smmu_ipa_size: ZMap.t Z;
        smmu_pa_size: ZMap.t Z;

        smmu_dev_global_irqs: ZMap.t Z;
        smmu_dev_context_irqs: ZMap.t Z;
        smmu_exists: ZMap.t Z;

        smmu_hyp_base: ZMap.t Z
      }.

  Record SPT :=
    mkSPT {
        (* global smmu_pt pool *)
        spt_vttbr_pool: ZMap.t Z;
        spt_pgd_pool: ZMap.t Z;
        spt_pmd_pool: ZMap.t Z;
        spt_pgd_next: Z;
        spt_pmd_next: Z;
        spt_pgd_par: ZMap.t Z;
        spt_pmd_par: ZMap.t Z;

        (* dev -> cfg -> spt high *)
        spt_pt: ZMap.t (ZMap.t (Z * Z));
        spt_pgd_t : ZMap.t (ZMap.t bool);
        spt_pmd_t : ZMap.t (ZMap.t (ZMap.t bool))
      }.

  Record CtxtRegs :=
    mkCtxtRegs {
        x0: Z;
        x1: Z;
        x2: Z;
        x3: Z;
        x4: Z;
        x5: Z;
        x6: Z;
        x7: Z;
        x8: Z;
        x9: Z;
        x10: Z;
        x11: Z;
        x12: Z;
        x13: Z;
        x14: Z;
        x15: Z;
        x16: Z;
        x17: Z;
        x18: Z;
        x19: Z;
        x20: Z;
        x21: Z;
        x22: Z;
        x23: Z;
        x24: Z;
        x25: Z;
        x26: Z;
        x27: Z;
        x28: Z;
        x29: Z;
        x30: Z;
        fp_q0: Z;
        fp_q1: Z;
        fp_q2: Z;
        fp_q3: Z;
        fp_q4: Z;
        fp_q5: Z;
        fp_q6: Z;
        fp_q7: Z;
        fp_q8: Z;
        fp_q9: Z;
        fp_q10: Z;
        fp_q11: Z;
        fp_q12: Z;
        fp_q13: Z;
        fp_q14: Z;
        fp_q15: Z;
        fp_q16: Z;
        fp_q17: Z;
        fp_q18: Z;
        fp_q19: Z;
        fp_q20: Z;
        fp_q21: Z;
        fp_q22: Z;
        fp_q23: Z;
        fp_q24: Z;
        fp_q25: Z;
        fp_q26: Z;
        fp_q27: Z;
        fp_q28: Z;
        fp_q29: Z;
        fp_q30: Z;
        fp_q31: Z;
        fp_fpsr: Z;
        fp_fpcr: Z;
        csselr_el1: Z;
        sctlr_el1: Z;
        cpacr_el1: Z;
        ttbr0_el1: Z;
        ttbr1_el1: Z;
        tcr_el1: Z;
        afsr0_el1: Z;
        afsr1_el1: Z;
        far_el1: Z;
        mair_el1: Z;
        vbar_el1: Z;
        contextidr_el1: Z;
        amair_el1: Z;
        cntkctl_el1: Z;
        par_el1: Z;
        tpidr_el1: Z;
        spsr_el1: Z;
        mdscr_el1: Z;
        sp_el0: Z;
        tpidr_el0: Z;
        tpidrro_el0: Z;
        spsr_el2: Z;
        vmpidr_el2: Z;
        mpidr_el1: Z;
        actlr_el1: Z;
        sp_el1: Z;
        elr_el1: Z;
        elr_el2: Z;
        vttbr_el2: Z;
        hcr_el2: Z;
        tpidr_el2: Z;
        esr_el2: Z;
        ec: Z;
        far_el2: Z;
        hpfar_el2: Z
      }.

  Record TrapRegs :=
    mkTrapRegs {
        pmuselr_el0: Z;
        pmuserenr_el0: Z;
        mdcr_el2: Z;
        cptr_el2: Z;
        cnthctl_el2: Z
      }.

  Record CtxtStates :=
    mkCtxtStates {
        pc: Z;
        pstate: Z;
        dirty: Z;
        flags: Z;
        esr_el1: Z;
        spsr_0: Z
      }.

  Record Ctxt :=
    mkCtxt {
        ctxt_regs: CtxtRegs;
        trap_regs: TrapRegs;
        ctxt_states: CtxtStates
      }.

End DataType.

Section Concurrency.

  Definition DataOracle := Z -> Z -> Z.

  Inductive TicketOracleEvent :=
  | INC_TICKET (n: nat)
  | INC_NOW
  | GET_NOW
  | CAS_TICKET
  | HOLD_LOCK
  | WAIT_LOCK (n: nat)
  | REL_LOCK.

  Inductive SharedMemEvent :=
  | OPULL (id: Z)
  | OCORE_DATA (core_data: CoreData)
  | OS2_PAGE (s2page: ZMap.t S2Page)
  | ONPT (npt: NPT)
  | OVMINFO (info: VMInfo)
  | OSPT (smmu: SPT)
  | OSMMU (smmu_vmid: ZMap.t Z)
  | OFLATMEM (flatmem: ZMap.t Z).

  Inductive AtomicEvent :=
  | OPT_GET (vmid: Z)
  | OMAP_HOST (addr: Z)
  | OCLEAR_VM (vmid: Z) (pfn: Z)
  | OASSIGN_VM (vmid: Z) (gfn: Z) (pfn: Z) (dorc: DataOracle) (logn: Z)
  | OMAP_VM (vmid: Z) (addr: Z) (pte: Z) (level: Z)
  | OMAP_IO (vmid: Z) (gpa: Z) (pa: Z)
  | OGRANT (vmid: Z) (pfn: Z)
  | OREVOKE (vmid: Z) (pfn: Z) (dorc: DataOracle) (logn: Z)
  | OVM_GET (vmid: Z)
  | OVM_ACTIVE (vmid: Z) (vcpuid: Z)
  | OVM_INACTIVE (vmid: Z) (vcpuid: Z)
  | OVM_POWEROFF (vmid: Z)
  | OREG_VCPU (vmid: Z) (vcpuid: Z)
  | OGEN_VMID
  | OREG_KVM (vmid: Z)
  | OBOOT_INFO (vmid: Z) (load_addr: Z) (size: Z)
  | OREMAP_IMAGE (vmid: Z) (pfn: Z) (load_idx: Z)
  | OVERIFY (vmid: Z)
  | OSMMU_GET
  | OASSIGN_SMMU (cbndx: Z) (index: Z) (gfn: Z) (pfn: Z)
  | OSMMU_FREE (cbndx: Z) (index: Z)
  | OSMMU_ALLOC (cbndx: Z) (vmid: Z) (index: Z) (num: Z)
  | OSMMU_MAP (cbndx: Z) (index: Z) (iova: Z) (pte: Z)
  | OSMMU_CLEAR (iova: Z) (cbndx: Z) (index: Z)
  | OLOAD_ENC_VCPU (vmid: Z) (vcpuid: Z) (cregs: CtxtRegs) (cstates: CtxtStates) (dorc: Z -> Z) (logn: Z)
  | OSAVE_ENC_BUF (vmid: Z) (inbuf: Z) (outbuf: Z) (dorc: Z -> Z) (logn: Z)
  | OLOAD_ENC_BUF (vmid: Z) (inbuf: Z) (dorc: Z -> Z) (logn: Z).

  Inductive MultiOracleEventUnit :=
  | TTICKET (e: TicketOracleEvent)
  | TSHARED (e: SharedMemEvent).

  Inductive MultiOracleEvent :=
  | TEVENT (cpuid: Z) (e: MultiOracleEventUnit).

  Definition MultiLog := list MultiOracleEvent.
  Definition MultiLogPool := ZMap.t MultiLog.

  Definition MultiOracle := Z -> MultiLog -> MultiLog.
  Definition MultiOraclePool := ZMap.t MultiOracle.

  Inductive SingleOracleEvent :=
  | SEVENT (cpuid: Z) (e: AtomicEvent).

  Definition SingleLog := list SingleOracleEvent.

  Definition SingleOracle := Z -> SingleLog -> SingleLog.

  Inductive LockStatus :=
  | LockFalse
  | LockOwn (b: bool).

  Inductive BarrierStatus :=
  | BarrierValid
  | BarrierNeeded
  | Barriered.

End Concurrency.

Section AbsData.

  Record Shared :=
    mkShared {
        flatmem: ZMap.t Z;

        (* npt *)
        npts: ZMap.t NPT;

        (* s2page *)
        s2page: ZMap.t S2Page;

        (* core data *)
        core_data: CoreData;

        (* vm *)
        vminfos: ZMap.t VMInfo;

        (* smmu *)
        spts: SPT;
        smmu_vmid: ZMap.t Z;

        (* high lock *)
        hlock: ZMap.t bool
      }.

  Record RData :=
    mkRData {
        (* machine states *)
        halt: bool;
        icore: bool;
        ihost: bool;
        tstate: Z;

        curid: Z;
        cur_vmid: Z;
        cur_vcpuid: Z;

        (* register *)
        regs: Ctxt;

        (* lock *)
        lock: ZMap.t LockStatus;
        bars: BarrierStatus;

        (* mem region *)
        region_cnt: Z;
        regions: ZMap.t Memblock;

        (* ctxt *)
        shadow_ctxts: ZMap.t Ctxt;

        (* smmu *)
        smmu_conf: SMMUConf;

        (* concurrency *)
        log: MultiLogPool;
        oracle: MultiOraclePool;
        slog: SingleLog;
        soracle: SingleOracle;

        (* data_oracle *)
        doracle: DataOracle;
        core_doracle: DataOracle;
        data_log: ZMap.t Z;
        core_data_log: ZMap.t Z;

        (* shared obj *)
        shared: Shared
      }.
  Parameter empty_adt: RData.

End AbsData.

(* Helpful Notations *)

Notation "reg @ ctxt" := (ZMap.get reg ctxt) (at level 1).
Notation "ctxt # reg == val" := (ZMap.set reg val ctxt) (at level 1).

Definition mset{T} (ctxt: ZMap.t T) idx val :=
  ZMap.set idx val ctxt.
Definition mset2{T} (ctxt: (ZMap.t (ZMap.t T))) idx1 idx2 val :=
  ZMap.set idx1 (ZMap.set idx2 val (ZMap.get idx1 ctxt)) ctxt.
Definition mset3{T} (ctxt: (ZMap.t (ZMap.t (ZMap.t T)))) idx1 idx2 idx3 val :=
  (ZMap.set idx1 (ZMap.set idx2 (ZMap.set idx3 val (ZMap.get idx2 (ZMap.get idx1 ctxt))) (ZMap.get idx1 ctxt)) ctxt).

Definition bind {A T : Type} (a : option A) (f : A -> option T) : option T :=
  match a with
  | Some x => f x
  | None => None
  end.

Definition bind64 {T : Type} (a : option Z64) (f : Z -> option T) : option T :=
  match a with
  | Some (VZ64 x) => f x
  | None => None
  end.

Definition bind' {A T: Type} (a : option (RData * A)) (f : A -> RData -> option T) : option T :=
  match a with
  | Some (adt', x) => f x adt'
  | None => None
  end.

Definition bind64' {T : Type} (a : option (RData*Z64)) (f : Z -> RData -> option T) : option T :=
  match a with
  | Some (adt', VZ64 x) => f x adt'
  | None => None
  end.

Notation "'when' X == A ; B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).
Notation "'when' X ',' D == A ; B" := (bind' A (fun X D => B)) (at level 200, X ident, D ident, A at level 100, B at level 200).
Notation "'when'' X == A ; B" := (bind64 A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).
Notation "'when'' X ',' D == A ; B" := (bind64' A (fun X D => B)) (at level 200, X ident, D ident, A at level 100, B at level 200).

Definition Assertion {T : Type} (a : bool) (f : option T) : option T :=
  match a with
  | true => f
  | false => None
  end.
Notation "'rely' B ; F" := (Assertion B F) (at level 200, B at level 100, F at level 200).

Hint Unfold bind bind64 bind' bind64' Assertion.

Definition update_next_vmid (a: CoreData) b :=
  mkCoreData b (next_remap_ptr a).
Notation "a {next_vmid : b }" := (update_next_vmid a b) (at level 1).

Definition update_next_remap_ptr (a: CoreData) b :=
  mkCoreData (next_vmid a) b.
Notation "a {next_remap_ptr : b }" := (update_next_remap_ptr a b) (at level 1).

Definition update_s2_owner (a: S2Page) b :=
  mkS2Page b (s2_count a) (s2_gfn a).
Notation "a {s2_owner : b }" := (update_s2_owner a b) (at level 1).

Definition update_s2_count (a: S2Page) b :=
  mkS2Page (s2_owner a) b (s2_gfn a).
Notation "a {s2_count : b }" := (update_s2_count a b) (at level 1).

Definition update_s2_gfn (a: S2Page) b :=
  mkS2Page (s2_owner a) (s2_count a) b.
Notation "a {s2_gfn : b }" := (update_s2_gfn a b) (at level 1).

Definition update_pt_vttbr_pool (a: NPT) b :=
  mkNPT b (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_vttbr_pool : b }" := (update_pt_vttbr_pool a b) (at level 1).

Definition update_pt_pgd_pool (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) b (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pgd_pool : b }" := (update_pt_pgd_pool a b) (at level 1).

Definition update_pt_pud_pool (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) b (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pud_pool : b }" := (update_pt_pud_pool a b) (at level 1).

Definition update_pt_pmd_pool (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) b (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pmd_pool : b }" := (update_pt_pmd_pool a b) (at level 1).

Definition update_pt_pgd_next (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) b (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pgd_next : b }" := (update_pt_pgd_next a b) (at level 1).

Definition update_pt_pud_next (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) b (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pud_next : b }" := (update_pt_pud_next a b) (at level 1).

Definition update_pt_pmd_next (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) b
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pmd_next : b }" := (update_pt_pmd_next a b) (at level 1).

Definition update_pt_pgd_par (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        b (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pgd_par : b }" := (update_pt_pgd_par a b) (at level 1).

Definition update_pt_pud_par (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) b (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pud_par : b }" := (update_pt_pud_par a b) (at level 1).

Definition update_pt_pmd_par (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) b (pt_updates a) (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_pmd_par : b }" := (update_pt_pmd_par a b) (at level 1).

Definition update_pt_updates (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) b (pt a) (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt_updates : b }" := (update_pt_updates a b) (at level 1).

Definition update_pt (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) b (pgd_t a) (pud_t a) (pmd_t a).
Notation "a {pt : b }" := (update_pt a b) (at level 1).

Definition update_pgd_t (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) b (pud_t a) (pmd_t a).
Notation "a {pgd_t : b }" := (update_pgd_t a b) (at level 1).

Definition update_pud_t (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) b (pmd_t a).
Notation "a {pud_t : b }" := (update_pud_t a b) (at level 1).

Definition update_pmd_t (a: NPT) b :=
  mkNPT (pt_vttbr_pool a) (pt_pgd_pool a) (pt_pud_pool a) (pt_pmd_pool a) (pt_pgd_next a) (pt_pud_next a) (pt_pmd_next a)
        (pt_pgd_par a) (pt_pud_par a) (pt_pmd_par a) (pt_updates a) (pt a) (pgd_t a) (pud_t a) b.
Notation "a {pmd_t : b }" := (update_pmd_t a b) (at level 1).

Definition update_VS (a: VMInfo) b :=
  mkVMInfo b (VB a).
Notation "a {VS : b }" := (update_VS a b) (at level 1).

Definition update_VB (a: VMInfo) b :=
  mkVMInfo (VS a) b.
Notation "a {VB : b }" := (update_VB a b) (at level 1).

Definition update_vm_next_load_info (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo b (vm_load_addr (VB a)) (vm_load_size (VB a)) (vm_remap_addr (VB a)) (vm_inc_exe (VB a)) (vm_mapped_pages (VB a))).
Notation "a {vm_next_load_info : b }" := (update_vm_next_load_info a b) (at level 1).

Definition update_vm_load_addr (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo (vm_next_load_info (VB a)) b (vm_load_size (VB a)) (vm_remap_addr (VB a)) (vm_inc_exe (VB a)) (vm_mapped_pages (VB a))).
Notation "a {vm_load_addr : b }" := (update_vm_load_addr a b) (at level 1).

Definition update_vm_load_size (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo (vm_next_load_info (VB a)) (vm_load_addr (VB a)) b (vm_remap_addr (VB a)) (vm_inc_exe (VB a)) (vm_mapped_pages (VB a))).
Notation "a {vm_load_size : b }" := (update_vm_load_size a b) (at level 1).

Definition update_vm_remap_addr (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo (vm_next_load_info (VB a)) (vm_load_addr (VB a)) (vm_load_size (VB a)) b (vm_inc_exe (VB a)) (vm_mapped_pages (VB a))).
Notation "a {vm_remap_addr : b }" := (update_vm_remap_addr a b) (at level 1).

Definition update_vm_inc_exe (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo (vm_next_load_info (VB a)) (vm_load_addr (VB a)) (vm_load_size (VB a)) (vm_remap_addr (VB a)) b (vm_mapped_pages (VB a))).
Notation "a {vm_inc_exe : b }" := (update_vm_inc_exe a b) (at level 1).

Definition update_vm_mapped_pages (a: VMInfo) b :=
  mkVMInfo (VS a)
  (mkBootInfo (vm_next_load_info (VB a)) (vm_load_addr (VB a)) (vm_load_size (VB a)) (vm_remap_addr (VB a)) (vm_inc_exe (VB a)) b).
Notation "a {vm_mapped_pages : b }" := (update_vm_mapped_pages a b) (at level 1).

Definition update_vm_kvm (a: VMInfo) b :=
  mkVMInfo
    (mkStateInfo b (vm_vcpu (VS a)) (vm_state (VS a)) (vm_vcpu_state (VS a)) (vm_power (VS a)))
    (VB a).
Notation "a {vm_kvm : b }" := (update_vm_kvm a b) (at level 1).

Definition update_vm_vcpu (a: VMInfo) b :=
  mkVMInfo
    (mkStateInfo (vm_kvm (VS a)) b (vm_state (VS a)) (vm_vcpu_state (VS a)) (vm_power (VS a)))
    (VB a).
Notation "a {vm_vcpu : b }" := (update_vm_vcpu a b) (at level 1).

Definition update_vm_state (a: VMInfo) b :=
  mkVMInfo
    (mkStateInfo (vm_kvm (VS a)) (vm_vcpu (VS a)) b (vm_vcpu_state (VS a)) (vm_power (VS a)))
    (VB a).
Notation "a {vm_state : b }" := (update_vm_state a b) (at level 1).

Definition update_vm_vcpu_state (a: VMInfo) b :=
  mkVMInfo
    (mkStateInfo (vm_kvm (VS a)) (vm_vcpu (VS a)) (vm_state (VS a)) b (vm_power (VS a)))
    (VB a).
Notation "a {vm_vcpu_state : b }" := (update_vm_vcpu_state a b) (at level 1).

Definition update_vm_power (a: VMInfo) b :=
  mkVMInfo
    (mkStateInfo (vm_kvm (VS a)) (vm_vcpu (VS a)) (vm_state (VS a)) (vm_vcpu_state (VS a)) b)
    (VB a).
Notation "a {vm_power : b }" := (update_vm_power a b) (at level 1).

Definition update_spt_vttbr_pool (a: SPT) b :=
  mkSPT b (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
          (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_vttbr_pool : b }" := (update_spt_vttbr_pool a b) (at level 1).

Definition update_spt_pgd_pool (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) b (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
         (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pgd_pool : b }" := (update_spt_pgd_pool a b) (at level 1).

Definition update_spt_pmd_pool (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) b (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
        (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pmd_pool : b }" := (update_spt_pmd_pool a b) (at level 1).

Definition update_spt_pgd_next (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) b (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
        (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pgd_next : b }" := (update_spt_pgd_next a b) (at level 1).

Definition update_spt_pmd_next (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) b (spt_pgd_par a) (spt_pmd_par a)
        (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pmd_next : b }" := (update_spt_pmd_next a b) (at level 1).

Definition update_spt_pgd_par (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) b (spt_pmd_par a)
         (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pgd_par : b }" := (update_spt_pgd_par a b) (at level 1).

Definition update_spt_pmd_par (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) b
          (spt_pt a) (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pmd_par : b }" := (update_spt_pmd_par a b) (at level 1).

Definition update_spt_pt (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
        b (spt_pgd_t a) (spt_pmd_t a).
Notation "a {spt_pt : b }" := (update_spt_pt a b) (at level 1).

Definition update_spt_pgd_t (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
        (spt_pt a) b (spt_pmd_t a).
Notation "a {spt_pgd_t : b }" := (update_spt_pgd_t a b) (at level 1).

Definition update_spt_pmd_t (a: SPT) b :=
  mkSPT (spt_vttbr_pool a) (spt_pgd_pool a) (spt_pmd_pool a) (spt_pgd_next a) (spt_pmd_next a) (spt_pgd_par a) (spt_pmd_par a)
          (spt_pt a) (spt_pgd_t a) b.
Notation "a {spt_pmd_t : b }" := (update_spt_pmd_t a b) (at level 1).

Definition update_flatmem (a: Shared) b :=
  mkShared b (npts a) (s2page a) (core_data a) (vminfos a) (spts a) (smmu_vmid a) (hlock a).
Notation "a {flatmem : b }" := (update_flatmem a b) (at level 1).

Definition update_npts (a: Shared) b :=
  mkShared (flatmem a) b (s2page a) (core_data a) (vminfos a) (spts a) (smmu_vmid a) (hlock a).
Notation "a {npts : b }" := (update_npts a b) (at level 1).

Definition update_s2page (a: Shared) b :=
  mkShared (flatmem a) (npts a) b (core_data a) (vminfos a) (spts a) (smmu_vmid a) (hlock a).
Notation "a {s2page : b }" := (update_s2page a b) (at level 1).

Definition update_core_data (a: Shared) b :=
  mkShared (flatmem a) (npts a) (s2page a) b (vminfos a) (spts a) (smmu_vmid a) (hlock a).
Notation "a {core_data : b }" := (update_core_data a b) (at level 1).

Definition update_vminfos (a: Shared) b :=
  mkShared (flatmem a) (npts a) (s2page a) (core_data a) b (spts a) (smmu_vmid a) (hlock a).
Notation "a {vminfos : b }" := (update_vminfos a b) (at level 1).

Definition update_spts (a: Shared) b :=
  mkShared (flatmem a) (npts a) (s2page a) (core_data a) (vminfos a) b (smmu_vmid a) (hlock a).
Notation "a {spts : b }" := (update_spts a b) (at level 1).

Definition update_smmu_vmid (a: Shared) b :=
  mkShared (flatmem a) (npts a) (s2page a) (core_data a) (vminfos a) (spts a) b (hlock a).
Notation "a {smmu_vmid : b }" := (update_smmu_vmid a b) (at level 1).

Definition update_hlock (a: Shared) b :=
  mkShared (flatmem a) (npts a) (s2page a) (core_data a) (vminfos a) (spts a) (smmu_vmid a) b.
Notation "a {hlock : b }" := (update_hlock a b) (at level 1).

Definition update_halt (a: RData) b :=
  mkRData b (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {halt : b }" := (update_halt a b) (at level 1).

Definition update_icore (a: RData) b :=
  mkRData (halt a) b (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {icore : b }" := (update_icore a b) (at level 1).

Definition update_ihost (a: RData) b :=
  mkRData (halt a) (icore a) b (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {ihost : b }" := (update_ihost a b) (at level 1).

Definition update_tstate (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) b (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {tstate : b }" := (update_tstate a b) (at level 1).

Definition update_curid (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) b (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {curid : b }" := (update_curid a b) (at level 1).

Definition update_cur_vmid (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) b (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {cur_vmid : b }" := (update_cur_vmid a b) (at level 1).

Definition update_cur_vcpuid (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) b (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {cur_vcpuid : b }" := (update_cur_vcpuid a b) (at level 1).

Definition update_regs (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) b
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {regs : b }" := (update_regs a b) (at level 1).

Definition update_lock (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          b (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {lock : b }" := (update_lock a b) (at level 1).

Definition update_bars (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) b (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {bars : b }" := (update_bars a b) (at level 1).

Definition update_region_cnt (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) b (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {region_cnt : b }" := (update_region_cnt a b) (at level 1).

Definition update_regions (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) b (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {regions : b }" := (update_regions a b) (at level 1).

Definition update_shadow_ctxts (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) b (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {shadow_ctxts : b }" := (update_shadow_ctxts a b) (at level 1).

Definition update_smmu_conf (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) b (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {smmu_conf : b }" := (update_smmu_conf a b) (at level 1).

Definition update_log (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) b (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {log : b }" := (update_log a b) (at level 1).

Definition update_oracle (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) b (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {oracle : b }" := (update_oracle a b) (at level 1).

Definition update_slog (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) b
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {slog : b }" := (update_slog a b) (at level 1).

Definition update_soracle (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          b (doracle a) (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {soracle : b }" := (update_soracle a b) (at level 1).

Definition update_doracle (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) b (core_doracle a) (data_log a) (core_data_log a) (shared a).
Notation "a {doracle : b }" := (update_doracle a b) (at level 1).

Definition update_core_doracle (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) b (data_log a) (core_data_log a) (shared a).
Notation "a {core_doracle : b }" := (update_core_doracle a b) (at level 1).

Definition update_data_log (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) b (core_data_log a) (shared a).
Notation "a {data_log : b }" := (update_data_log a b) (at level 1).

Definition update_core_data_log (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) b (shared a).
Notation "a {core_data_log : b }" := (update_core_data_log a b) (at level 1).

Definition update_shared (a: RData) b :=
  mkRData (halt a) (icore a) (ihost a) (tstate a) (curid a) (cur_vmid a) (cur_vcpuid a) (regs a)
          (lock a) (bars a) (region_cnt a) (regions a) (shadow_ctxts a) (smmu_conf a) (log a) (oracle a) (slog a)
          (soracle a) (doracle a) (core_doracle a) (data_log a) (core_data_log a) b.
Notation "a {shared : b }" := (update_shared a b) (at level 1).

Definition update_ctxt_regs (a: Ctxt) b :=
  mkCtxt b (trap_regs a) (ctxt_states a).
Notation "a {ctxt_regs : b }" := (update_ctxt_regs a b) (at level 1).

Definition update_trap_regs (a: Ctxt) b :=
  mkCtxt (ctxt_regs a) b (ctxt_states a).
Notation "a {trap_regs : b }" := (update_trap_regs a b) (at level 1).

Definition update_ctxt_states (a: Ctxt) b :=
  mkCtxt (ctxt_regs a) (trap_regs a) b.
Notation "a {ctxt_states : b }" := (update_ctxt_states a b) (at level 1).

Definition update_pc (a: CtxtStates) b :=
  mkCtxtStates b (pstate a) (dirty a) (flags a) (esr_el1 a) (spsr_0 a).
Notation "a {pc : b }" := (update_pc a b) (at level 1).

Definition update_pstate (a: CtxtStates) b :=
  mkCtxtStates (pc a) b (dirty a) (flags a) (esr_el1 a) (spsr_0 a).
Notation "a {pstate : b }" := (update_pstate a b) (at level 1).

Definition update_dirty (a: CtxtStates) b :=
  mkCtxtStates (pc a) (pstate a) b (flags a) (esr_el1 a) (spsr_0 a).
Notation "a {dirty : b }" := (update_dirty a b) (at level 1).

Definition update_flags (a: CtxtStates) b :=
  mkCtxtStates (pc a) (pstate a) (dirty a) b (esr_el1 a) (spsr_0 a).
Notation "a {flags : b }" := (update_flags a b) (at level 1).

Definition update_esr_el1 (a: CtxtStates) b :=
  mkCtxtStates (pc a) (pstate a) (dirty a) (flags a) b (spsr_0 a).
Notation "a {esr_el1 : b }" := (update_esr_el1 a b) (at level 1).

Definition update_spsr_0 (a: CtxtStates) b :=
  mkCtxtStates (pc a) (pstate a) (dirty a) (flags a) (esr_el1 a) b.
Notation "a {spsr_0 : b }" := (update_spsr_0 a b) (at level 1).

Definition update_pmuselr_el0 (a: TrapRegs) b :=
  mkTrapRegs b (pmuserenr_el0 a) (mdcr_el2 a) (cptr_el2 a) (cnthctl_el2 a).
Notation "a {pmuselr_el0 : b }" := (update_pmuselr_el0 a b) (at level 1).

Definition update_pmuserenr_el0 (a: TrapRegs) b :=
  mkTrapRegs (pmuselr_el0 a) b (mdcr_el2 a) (cptr_el2 a) (cnthctl_el2 a).
Notation "a {pmuserenr_el0 : b }" := (update_pmuserenr_el0 a b) (at level 1).

Definition update_mdcr_el2 (a: TrapRegs) b :=
  mkTrapRegs (pmuselr_el0 a) (pmuserenr_el0 a) b (cptr_el2 a) (cnthctl_el2 a).
Notation "a {mdcr_el2 : b }" := (update_mdcr_el2 a b) (at level 1).

Definition update_cptr_el2 (a: TrapRegs) b :=
  mkTrapRegs (pmuselr_el0 a) (pmuserenr_el0 a) (mdcr_el2 a) b (cnthctl_el2 a).
Notation "a {cptr_el2 : b }" := (update_cptr_el2 a b) (at level 1).

Definition update_cnthctl_el2 (a: TrapRegs) b :=
  mkTrapRegs (pmuselr_el0 a) (pmuserenr_el0 a) (mdcr_el2 a) (cptr_el2 a) b.
Notation "a {cnthctl_el2 : b }" := (update_cnthctl_el2 a b) (at level 1).

Definition update_x0 (a: CtxtRegs) b :=
  mkCtxtRegs b (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x0 : b }" := (update_x0 a b) (at level 1).

Definition update_x1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) b (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x1 : b }" := (update_x1 a b) (at level 1).

Definition update_x2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) b (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x2 : b }" := (update_x2 a b) (at level 1).

Definition update_x3 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) b (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x3 : b }" := (update_x3 a b) (at level 1).

Definition update_x4 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) b (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x4 : b }" := (update_x4 a b) (at level 1).

Definition update_x5 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) b (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x5 : b }" := (update_x5 a b) (at level 1).

Definition update_x6 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) b (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x6 : b }" := (update_x6 a b) (at level 1).

Definition update_x7 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) b
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x7 : b }" := (update_x7 a b) (at level 1).

Definition update_x8 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          b (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x8 : b }" := (update_x8 a b) (at level 1).

Definition update_x9 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) b (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x9 : b }" := (update_x9 a b) (at level 1).

Definition update_x10 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) b (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x10 : b }" := (update_x10 a b) (at level 1).

Definition update_x11 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) b (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x11 : b }" := (update_x11 a b) (at level 1).

Definition update_x12 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) b (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x12 : b }" := (update_x12 a b) (at level 1).

Definition update_x13 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) b (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x13 : b }" := (update_x13 a b) (at level 1).

Definition update_x14 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) b (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x14 : b }" := (update_x14 a b) (at level 1).

Definition update_x15 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) b
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x15 : b }" := (update_x15 a b) (at level 1).

Definition update_x16 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          b (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x16 : b }" := (update_x16 a b) (at level 1).

Definition update_x17 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) b (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x17 : b }" := (update_x17 a b) (at level 1).

Definition update_x18 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) b (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x18 : b }" := (update_x18 a b) (at level 1).

Definition update_x19 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) b (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x19 : b }" := (update_x19 a b) (at level 1).

Definition update_x20 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) b (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x20 : b }" := (update_x20 a b) (at level 1).

Definition update_x21 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) b (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x21 : b }" := (update_x21 a b) (at level 1).

Definition update_x22 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) b (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x22 : b }" := (update_x22 a b) (at level 1).

Definition update_x23 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) b
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x23 : b }" := (update_x23 a b) (at level 1).

Definition update_x24 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          b (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x24 : b }" := (update_x24 a b) (at level 1).

Definition update_x25 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) b (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x25 : b }" := (update_x25 a b) (at level 1).

Definition update_x26 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) b (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x26 : b }" := (update_x26 a b) (at level 1).

Definition update_x27 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) b (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x27 : b }" := (update_x27 a b) (at level 1).

Definition update_x28 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) b (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x28 : b }" := (update_x28 a b) (at level 1).

Definition update_x29 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) b (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x29 : b }" := (update_x29 a b) (at level 1).

Definition update_x30 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) b (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {x30 : b }" := (update_x30 a b) (at level 1).

Definition update_fp_q0 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) b
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q0 : b }" := (update_fp_q0 a b) (at level 1).

Definition update_fp_q1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          b (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q1 : b }" := (update_fp_q1 a b) (at level 1).

Definition update_fp_q2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) b (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q2 : b }" := (update_fp_q2 a b) (at level 1).

Definition update_fp_q3 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) b (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q3 : b }" := (update_fp_q3 a b) (at level 1).

Definition update_fp_q4 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) b (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q4 : b }" := (update_fp_q4 a b) (at level 1).

Definition update_fp_q5 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) b (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q5 : b }" := (update_fp_q5 a b) (at level 1).

Definition update_fp_q6 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) b (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q6 : b }" := (update_fp_q6 a b) (at level 1).

Definition update_fp_q7 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) b (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q7 : b }" := (update_fp_q7 a b) (at level 1).

Definition update_fp_q8 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) b
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q8 : b }" := (update_fp_q8 a b) (at level 1).

Definition update_fp_q9 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          b (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q9 : b }" := (update_fp_q9 a b) (at level 1).

Definition update_fp_q10 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) b (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q10 : b }" := (update_fp_q10 a b) (at level 1).

Definition update_fp_q11 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) b (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q11 : b }" := (update_fp_q11 a b) (at level 1).

Definition update_fp_q12 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) b (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q12 : b }" := (update_fp_q12 a b) (at level 1).

Definition update_fp_q13 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) b (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q13 : b }" := (update_fp_q13 a b) (at level 1).

Definition update_fp_q14 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) b (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q14 : b }" := (update_fp_q14 a b) (at level 1).

Definition update_fp_q15 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) b (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q15 : b }" := (update_fp_q15 a b) (at level 1).

Definition update_fp_q16 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) b
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q16 : b }" := (update_fp_q16 a b) (at level 1).

Definition update_fp_q17 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          b (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q17 : b }" := (update_fp_q17 a b) (at level 1).

Definition update_fp_q18 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) b (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q18 : b }" := (update_fp_q18 a b) (at level 1).

Definition update_fp_q19 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) b (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q19 : b }" := (update_fp_q19 a b) (at level 1).

Definition update_fp_q20 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) b (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q20 : b }" := (update_fp_q20 a b) (at level 1).

Definition update_fp_q21 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) b (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q21 : b }" := (update_fp_q21 a b) (at level 1).

Definition update_fp_q22 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) b (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q22 : b }" := (update_fp_q22 a b) (at level 1).

Definition update_fp_q23 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) b (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q23 : b }" := (update_fp_q23 a b) (at level 1).

Definition update_fp_q24 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) b
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q24 : b }" := (update_fp_q24 a b) (at level 1).

Definition update_fp_q25 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          b (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q25 : b }" := (update_fp_q25 a b) (at level 1).

Definition update_fp_q26 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) b (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q26 : b }" := (update_fp_q26 a b) (at level 1).

Definition update_fp_q27 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) b (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q27 : b }" := (update_fp_q27 a b) (at level 1).

Definition update_fp_q28 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) b (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q28 : b }" := (update_fp_q28 a b) (at level 1).

Definition update_fp_q29 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) b (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q29 : b }" := (update_fp_q29 a b) (at level 1).

Definition update_fp_q30 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) b (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q30 : b }" := (update_fp_q30 a b) (at level 1).

Definition update_fp_q31 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) b (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_q31 : b }" := (update_fp_q31 a b) (at level 1).

Definition update_fp_fpsr (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) b
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_fpsr : b }" := (update_fp_fpsr a b) (at level 1).

Definition update_fp_fpcr (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          b (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {fp_fpcr : b }" := (update_fp_fpcr a b) (at level 1).

Definition update_csselr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) b (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {csselr_el1 : b }" := (update_csselr_el1 a b) (at level 1).

Definition update_sctlr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) b (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {sctlr_el1 : b }" := (update_sctlr_el1 a b) (at level 1).

Definition update_cpacr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) b (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {cpacr_el1 : b }" := (update_cpacr_el1 a b) (at level 1).

Definition update_ttbr0_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) b (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {ttbr0_el1 : b }" := (update_ttbr0_el1 a b) (at level 1).

Definition update_ttbr1_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) b (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {ttbr1_el1 : b }" := (update_ttbr1_el1 a b) (at level 1).

Definition update_tcr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) b (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {tcr_el1 : b }" := (update_tcr_el1 a b) (at level 1).

Definition update_afsr0_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) b
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {afsr0_el1 : b }" := (update_afsr0_el1 a b) (at level 1).

Definition update_afsr1_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          b (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {afsr1_el1 : b }" := (update_afsr1_el1 a b) (at level 1).

Definition update_far_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) b (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {far_el1 : b }" := (update_far_el1 a b) (at level 1).

Definition update_mair_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) b (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {mair_el1 : b }" := (update_mair_el1 a b) (at level 1).

Definition update_vbar_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) b (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {vbar_el1 : b }" := (update_vbar_el1 a b) (at level 1).

Definition update_contextidr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) b (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {contextidr_el1 : b }" := (update_contextidr_el1 a b) (at level 1).

Definition update_amair_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) b (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {amair_el1 : b }" := (update_amair_el1 a b) (at level 1).

Definition update_cntkctl_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) b (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {cntkctl_el1 : b }" := (update_cntkctl_el1 a b) (at level 1).

Definition update_par_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) b
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {par_el1 : b }" := (update_par_el1 a b) (at level 1).

Definition update_tpidr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          b (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {tpidr_el1 : b }" := (update_tpidr_el1 a b) (at level 1).

Definition update_spsr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) b (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {spsr_el1 : b }" := (update_spsr_el1 a b) (at level 1).

Definition update_mdscr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) b (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {mdscr_el1 : b }" := (update_mdscr_el1 a b) (at level 1).

Definition update_sp_el0 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) b (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {sp_el0 : b }" := (update_sp_el0 a b) (at level 1).

Definition update_tpidr_el0 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) b (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {tpidr_el0 : b }" := (update_tpidr_el0 a b) (at level 1).

Definition update_tpidrro_el0 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) b (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {tpidrro_el0 : b }" := (update_tpidrro_el0 a b) (at level 1).

Definition update_spsr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) b (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {spsr_el2 : b }" := (update_spsr_el2 a b) (at level 1).

Definition update_vmpidr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) b
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {vmpidr_el2 : b }" := (update_vmpidr_el2 a b) (at level 1).

Definition update_mpidr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          b (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {mpidr_el1 : b }" := (update_mpidr_el1 a b) (at level 1).

Definition update_actlr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) b (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {actlr_el1 : b }" := (update_actlr_el1 a b) (at level 1).

Definition update_sp_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) b (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {sp_el1 : b }" := (update_sp_el1 a b) (at level 1).

Definition update_elr_el1 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) b (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {elr_el1 : b }" := (update_elr_el1 a b) (at level 1).

Definition update_elr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) b (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {elr_el2 : b }" := (update_elr_el2 a b) (at level 1).

Definition update_vttbr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) b (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {vttbr_el2 : b }" := (update_vttbr_el2 a b) (at level 1).

Definition update_hcr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) b (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {hcr_el2 : b }" := (update_hcr_el2 a b) (at level 1).

Definition update_tpidr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) b
          (esr_el2 a) (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {tpidr_el2 : b }" := (update_tpidr_el2 a b) (at level 1).

Definition update_esr_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          b (ec a) (far_el2 a) (hpfar_el2 a).
Notation "a {esr_el2 : b }" := (update_esr_el2 a b) (at level 1).

Definition update_ec (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) b (far_el2 a) (hpfar_el2 a).
Notation "a {ec : b }" := (update_ec a b) (at level 1).

Definition update_far_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) b (hpfar_el2 a).
Notation "a {far_el2 : b }" := (update_far_el2 a b) (at level 1).

Definition update_hpfar_el2 (a: CtxtRegs) b :=
  mkCtxtRegs (x0 a) (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a) (x7 a)
          (x8 a) (x9 a) (x10 a) (x11 a) (x12 a) (x13 a) (x14 a) (x15 a)
          (x16 a) (x17 a) (x18 a) (x19 a) (x20 a) (x21 a) (x22 a) (x23 a)
          (x24 a) (x25 a) (x26 a) (x27 a) (x28 a) (x29 a) (x30 a) (fp_q0 a)
          (fp_q1 a) (fp_q2 a) (fp_q3 a) (fp_q4 a) (fp_q5 a) (fp_q6 a) (fp_q7 a) (fp_q8 a)
          (fp_q9 a) (fp_q10 a) (fp_q11 a) (fp_q12 a) (fp_q13 a) (fp_q14 a) (fp_q15 a) (fp_q16 a)
          (fp_q17 a) (fp_q18 a) (fp_q19 a) (fp_q20 a) (fp_q21 a) (fp_q22 a) (fp_q23 a) (fp_q24 a)
          (fp_q25 a) (fp_q26 a) (fp_q27 a) (fp_q28 a) (fp_q29 a) (fp_q30 a) (fp_q31 a) (fp_fpsr a)
          (fp_fpcr a) (csselr_el1 a) (sctlr_el1 a) (cpacr_el1 a) (ttbr0_el1 a) (ttbr1_el1 a) (tcr_el1 a) (afsr0_el1 a)
          (afsr1_el1 a) (far_el1 a) (mair_el1 a) (vbar_el1 a) (contextidr_el1 a) (amair_el1 a) (cntkctl_el1 a) (par_el1 a)
          (tpidr_el1 a) (spsr_el1 a) (mdscr_el1 a) (sp_el0 a) (tpidr_el0 a) (tpidrro_el0 a) (spsr_el2 a) (vmpidr_el2 a)
          (mpidr_el1 a) (actlr_el1 a) (sp_el1 a) (elr_el1 a) (elr_el2 a) (vttbr_el2 a) (hcr_el2 a) (tpidr_el2 a)
          (esr_el2 a) (ec a) (far_el2 a) b.
Notation "a {hpfar_el2 : b }" := (update_hpfar_el2 a b) (at level 1).

(* Log Replay *)

Fixpoint CalFlatmem o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalFlatmem o l' in
    match e with
    | TSHARED (OFLATMEM m) => m
    | _ => l0
    end
  end.

Fixpoint CalCoreData o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalCoreData o l' in
    match e with
    | TSHARED (OCORE_DATA m) => m
    | _ => l0
    end
  end.

Fixpoint CalS2Page o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalS2Page o l' in
    match e with
    | TSHARED (OS2_PAGE m) => m
    | _ => l0
    end
  end.

Fixpoint CalSPT o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalSPT o l' in
    match e with
    | TSHARED (OSPT m) => m
    | _ => l0
    end
  end.

Fixpoint CalSMMU o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalSMMU o l' in
    match e with
    | TSHARED (OSMMU m) => m
    | _ => l0
    end
  end.

Fixpoint CalNPT o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalNPT o l' in
    match e with
    | TSHARED (ONPT m) => m
    | _ => l0
    end
  end.

Fixpoint CalVMInfo o (log: MultiLog) :=
  match log with
  | nil => o
  | (TEVENT _ e) :: l' =>
    let l0 := CalVMInfo o l' in
    match e with
    | TSHARED (OVMINFO m) => m
    | _ => l0
    end
  end.

Definition FLATMEM_ID := 0.
Definition CORE_ID := 1.
Definition S2PAGE_ID := 2.
Definition SPT_ID := 3.
Definition SMMU_ID := 4.
Definition NPT_ID := 5.
Definition INFO_ID := 22.
Definition ID_END := 39.

Definition lock_idx_core    := 0.
Definition lock_idx_s2page  := 1.
Definition lock_idx_spt     := 2.
Definition lock_idx_smmu    := 3.
Definition lock_idx_pt_base := 4.
Definition lock_idx_pt vmid := lock_idx_pt_base + vmid.
Definition lock_idx_vm_base := 21.
Definition lock_idx_vm vmid := lock_idx_vm_base + vmid.
Definition lock_range       := 39.

Fixpoint CalState (id: Z) (log: MultiLog) (sdt: Shared) :=
  if id =? FLATMEM_ID then
    sdt {flatmem: CalFlatmem (flatmem sdt) log}
  else if id =? CORE_ID then
    sdt {core_data: CalCoreData (core_data sdt) log}
  else if id =? S2PAGE_ID then
    sdt {s2page: CalS2Page (s2page sdt) log}
  else if id =? SPT_ID then
    sdt {spts: CalSPT (spts sdt) log}
  else if id =? SMMU_ID then
    sdt {smmu_vmid: CalSMMU (smmu_vmid sdt) log}
  else if (NPT_ID <=? id) && (id <? INFO_ID) then
    let vmid := id - NPT_ID in
    sdt {npts: (npts sdt) # vmid == (CalNPT (vmid @ (npts sdt)) log)}
  else if (INFO_ID <=? id) && (id <? ID_END) then
    let vmid := id - INFO_ID in
    sdt {vminfos: (vminfos sdt) # vmid == (CalVMInfo (vmid @ (vminfos sdt)) log)}
  else sdt.

Hint Unfold
     FLATMEM_ID
     CORE_ID
     S2PAGE_ID
     SPT_ID
     SMMU_ID
     NPT_ID
     INFO_ID
     ID_END.
Section CLASS_RELATIONS.

  Context `{data : CompatData RData}.
  Context `{data0 : CompatData RData}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  Notation LDATAOps := (cdata (cdata_ops := data_ops0) RData).

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.

  Context `{rel_prf: CompatRel _ (memory_model_ops:= memory_model_ops) _ 
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Section CLASS_CPU_ID.

    Class relate_impl_CPU_ID :=
      {
        relate_impl_CPU_ID_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          d1.(curid) = d2.(curid);

        relate_impl_CPU_ID_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {curid: b} d2 {curid: b}
      }.

    Class match_impl_CPU_ID :=
      {
        match_impl_CPU_ID_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {curid: b} m f
      }.

  End CLASS_CPU_ID.

  Section CLASS_multi_log.

    Class relate_impl_multi_log :=
      {
        relate_impl_multi_log_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          d1.(log) = d2.(log);

        relate_impl_multi_log_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {log: b} d2 {log: b}
      }.

    Class match_impl_multi_log :=
      {
        match_impl_multi_log_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {log: b} m f
      }.

    Class match_impl_multi_log_one R :=
      {
        match_impl_multi_log_one_update ι d m f z l l':
          match_AbData ι d m f ->
          ZMap.get z d.(log) = l ->
          R l l' ->
          match_AbData ι d {log: ZMap.set z (l') d.(log)} m f
      }.

    Global Instance match_impl_multi_log_one_match_impl_multi_log R:
      match_impl_multi_log ->
      match_impl_multi_log_one R.
    Proof. destruct 1; constructor; eauto. Qed.

  End CLASS_multi_log.

  Section CLASS_multi_oracle.

    Class relate_impl_multi_oracle :=
      {
        relate_impl_multi_oracle_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          d1.(oracle) = d2.(oracle);

        relate_impl_multi_oracle_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {oracle: b} d2 {oracle: b}
      }.

    Class match_impl_multi_oracle :=
      {
        match_impl_multi_oracle_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {oracle: b} m f
      }.

  End CLASS_multi_oracle.

End CLASS_RELATIONS.

Ltac relate_match_instance_tac:=
  split; inversion 1; eauto 2; try econstructor; eauto 2.

Hint Extern 1 relate_impl_CPU_ID =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 match_impl_CPU_ID =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 relate_impl_multi_oracle =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 match_impl_multi_oracle =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 relate_impl_multi_log =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 match_impl_multi_log =>
(relate_match_instance_tac): typeclass_instances.
```
