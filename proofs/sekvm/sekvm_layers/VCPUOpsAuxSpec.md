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
Require Import MemoryOps.Spec.
Require Import MmioOps.Layer.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section VCPUOpsAuxSpec.

  Definition reset_gp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let logn := vmid @ (data_log adt) in
    let pc0 := (doracle adt) vmid logn in
    rely is_int64 pc0;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        let num := vm_next_load_info (VB info) in
        rely (0 <=? num) && (num <=? MAX_LOAD_INFO_NUM);
        match search_load_info_loop (Z.to_nat num) 0 pc0 0 (VB info) with
        | Some (idx', load_info) =>
          rely is_addr load_info;
          let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) ::
                            TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                            (orac cpu l0) ++ l0 in
          if load_info =? 0 then
            Some adt {halt: true} {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse} {data_log: (data_log adt) # vmid == (logn + 1)}
          else
            let ctxt' := ctxt {ctxt_regs: clear_shadow_gp_regs_specx (ctxt_regs ctxt)} in
            let pstate0 := (doracle adt) vmid (logn + 1) in
            rely is_int64 pstate0;
            let ctxt'' := ctxt' {ctxt_regs: reset_fp_regs_specx (ctxt_regs ctxt')} {ctxt_states: (ctxt_states ctxt') {pc: pc0} {pstate: pstate0}} in
            Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                      {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse} {data_log: (data_log adt) # vmid == (logn + 2)}
                      {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt''}
        | _ => None
        end
      | _ => None
      end
    | _, _, _ => None
    end.

  Fixpoint reset_sys_regs_loop n i vcpuid cregs cstates (dorc: Z -> Z) logn :=
    match n with
    | O => Some (cregs, cstates, logn, i)
    | S n' =>
      match reset_sys_regs_loop n' i vcpuid cregs cstates dorc logn with
      | Some (cregs', cstates', logn', i') =>
        if i' =? MPIDR_EL1 then
          let mpidr :=  (Z.land vcpuid 15) + (Z.land (vcpuid / 16) 255) * 256 +
                        (Z.land (vcpuid / 4096) 255) * 65536 in
          match set_shadow_ctxt_specx i' (mpidr + 2147483648) cregs' cstates' with
          | (cregs'', cstates'') => Some (cregs'', cstates'', logn', i' + 1)
          end
        else
          if i' =? ACTLR_EL1 then
            let val := dorc logn' in
            rely is_int64 val;
            match set_shadow_ctxt_specx i' val cregs' cstates' with
            | (cregs'', cstates'') => Some (cregs'', cstates'', logn' + 1, i' + 1)
            end
          else
            let val := reg_desc i' in
            rely is_int64 val;
            match set_shadow_ctxt_specx i' val cregs' cstates' with
            | (cregs'', cstates'') => Some (cregs'', cstates'', logn', i' + 1)
            end
      | _ => None
      end
    end.

  Definition reset_sys_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    match reset_sys_regs_loop (Z.to_nat SHADOW_SYS_REGS_SIZE) 1 vcpuid (ctxt_regs ctxt)
                              (ctxt_states ctxt) (doracle adt vmid) (vmid @ (data_log adt)) with
    | Some (cregs', cstates', logn', i') =>
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'})}
           {data_log: (data_log adt) # vmid == logn'}
    | _ => None
    end.

  Fixpoint sync_dirty_to_shadow_loop (n: nat) (i: Z) dirty cregs cstates dorc logn :=
    match n with
    | O => Some (i, cregs, cstates, logn)
    | S n' =>
      match sync_dirty_to_shadow_loop n' i dirty cregs cstates dorc logn with
      | Some (i', cregs', cstates', logn') =>
        rely ((i' >=? 0) && (i' <=? 31));
        if (Z.land dirty (Z.shiftl 1 i')) =? 0 then
           Some (i' + 1, cregs', cstates', logn')
        else
          let reg := dorc logn in
          rely is_int64 reg;
          match set_shadow_ctxt_specx i' reg cregs' cstates' with
          | (cregs'', cstates'') => Some (i' + 1, cregs'', cstates'', logn' + 1)
          end
      | _ => None
      end
    end.

  Definition sync_dirty_to_shadow_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let dirty0 := dirty (ctxt_states ctxt) in
    rely is_int64 dirty0;
    match sync_dirty_to_shadow_loop 31%nat 0 dirty0 (ctxt_regs ctxt) (ctxt_states ctxt) ((doracle adt) vmid) (vmid @ (data_log adt)) with
    | Some (i', cregs', cstates', logn') =>
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'})}
           {data_log: (data_log adt) # vmid == logn'}
    | _ => None
    end.

  Definition prep_wfx_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: DIRTY_PC_FLAG}} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition prep_hvc_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let psci_fn0 := (x0 (ctxt_regs ctxt)) in
    rely is_int64 psci_fn0;
    let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: 1}} in
    let psci_fn := Z.land psci_fn0 INVALID in
    if psci_fn =? PSCI_0_2_FN64_CPU_ON then
      let reg1 := (x1 (ctxt_regs ctxt)) in
      let reg2 := (x2 (ctxt_regs ctxt)) in
      let reg3 := (x3 (ctxt_regs ctxt)) in
      rely is_int64 reg1; rely is_int64 reg2; rely is_int64 reg3;
      Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
    else
      if (psci_fn =? PSCI_0_2_FN_AFFINITY_INFO) || (psci_fn =? PSCI_0_2_FN64_AFFINITY_INFO) then
        let reg1 := (x1 (ctxt_regs ctxt)) in
        let reg2 := (x2 (ctxt_regs ctxt)) in
        rely is_int64 reg1; rely is_int64 reg2;
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
      else
        if psci_fn =? PSCI_0_2_FN_SYSTEM_OFF then
          let id := INFO_ID + vmid in
          let cpu := curid adt in
          match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
          | LockFalse, orac, l0 =>
            match H_CalLock ((orac cpu l0) ++ l0) with
            | Some (_, LEMPTY, None) =>
              let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
              let info' := info {vm_state: POWEROFF} in
              let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                                TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                                (orac cpu l0) ++ l0 in
              Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
                  {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse} {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
            | _ => None
            end
          | _, _, _ => None
          end
        else Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition prep_abort_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let logn := vmid @ (data_log adt) in
    let esr := (doracle adt) vmid logn in
    rely is_int64 esr;
    let Rd := Z.land (esr / 65536) 31 in
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let hpfar_el2' := (hpfar_el2 (ctxt_regs ctxt)) in
    rely is_gfn (hpfar_el2' / 16);
    let fault_ipa := (hpfar_el2' / 16) * 4096 in
    if fault_ipa <? MAX_MMIO_ADDR then
      if ((Z.land esr ESR_ELx_WNR) =? 0) && ((Z.land esr ESR_ELx_S1PTW) =? 0) then
        let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: (Z.shiftl 1 Rd)}} in
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
      else
        let ctxt' := ctxt {ctxt_states: (ctxt_states ctxt) {dirty: DIRTY_PC_FLAG}} in
        let reg := get_shadow_ctxt_specx Rd (ctxt_regs ctxt') (ctxt_states ctxt') in
        rely is_int64 reg;
        Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
    else Some adt.

  Definition update_exception_gp_regs_spec (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let pstate' := (pstate (ctxt_states ctxt)) in
    let pc' := (pc (ctxt_states ctxt)) in
    let new_pc := exception_vector (VZ64 pstate') in
    rely is_int64 pstate'; rely is_int64 pc'; rely is_int64 new_pc;
    let ctxt' := ctxt {ctxt_regs: (ctxt_regs ctxt) {elr_el1: pc'}}
                      {ctxt_states: (ctxt_states ctxt) {pc: new_pc} {pstate: PSTATE_FAULT_BITS_64} {spsr_0: pstate'} {esr_el1: ESR_ELx_EC_UNKNOWN}} in
    Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}.

  Definition post_handle_shadow_s2pt_fault_spec (vmid: Z) (vcpuid: Z) (addr: Z64) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    if halt adt then Some adt else
    let logn := vmid @ (core_data_log adt) in
    let pte := core_doracle adt vmid logn in
    let level := core_doracle adt vmid (logn + 1) in
    rely is_int64 pte; rely is_int64 level;
    if level =? 2 then
      prot_and_map_vm_s2pt_spec vmid addr (VZ64 pte) 2 (adt {core_data_log: (core_data_log adt) # vmid == (logn + 2)})
    else
      prot_and_map_vm_s2pt_spec vmid addr (VZ64 pte) 3 (adt {core_data_log: (core_data_log adt) # vmid == (logn + 2)}).

End VCPUOpsAuxSpec.

Section VCPUOpsAuxSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioOps_ops) LDATA).

  Definition reset_gp_regs_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' pc, adt' == get_int_pc_spec vmid vcpuid adt;
    rely is_int64 pc;
    when' load_info, adt1 == search_load_info_spec vmid (VZ64 pc) adt';
    rely is_int64 load_info;
    if load_info =? 0 then panic_spec adt1
    else
      when adt2 == clear_shadow_gp_regs_spec vmid vcpuid adt1;
      when' pstate, adt3 == get_int_pstate_spec vmid vcpuid adt2;
      rely is_int64 pstate;
      when adt4 == set_shadow_ctxt_spec vmid vcpuid PSTATE (VZ64 pstate) adt3;
      when adt5 == set_shadow_ctxt_spec vmid vcpuid PC (VZ64 pc) adt4;
      reset_fp_regs_spec vmid vcpuid adt5.

  Fixpoint reset_sys_regs_loop0 (n: nat) (i: Z) (vmid: Z) (vcpuid: Z) (adt: RData) :=
    match n with
    | O => Some (adt, i)
    | S n' =>
      match reset_sys_regs_loop0 n' i vmid vcpuid adt with
      | Some (adt', i') =>
        rely is_reg i';
        if i' =? MPIDR_EL1 then
          let mpidr :=  (Z.land vcpuid 15) + (Z.land (vcpuid / 16) 255) * 256 +
                        (Z.land (vcpuid / 4096) 255) * 65536 in
          when adt'' == set_shadow_ctxt_spec vmid vcpuid i' (VZ64 (mpidr + 2147483648)) adt';
          Some (adt'', i' + 1)
        else
          if i' =? ACTLR_EL1 then
            when' val, adt2 == read_actlr_el1_spec adt';
            rely is_int64 val;
            when adt'' == set_shadow_ctxt_spec vmid vcpuid i' (VZ64 val) adt2;
            Some (adt'', i' + 1)
          else
            when' val == get_sys_reg_desc_val_spec i' adt';
            rely is_int64 val;
            when adt'' == set_shadow_ctxt_spec vmid vcpuid i' (VZ64 val) adt';
            Some (adt'', i' + 1)
      | _ => None
      end
    end.

  Definition reset_sys_regs_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    match reset_sys_regs_loop0 (Z.to_nat SHADOW_SYS_REGS_SIZE) 1 vmid vcpuid adt with
    | Some (adt', idx') => rely is_int idx'; Some adt'
    | _ => None
    end.

  Fixpoint sync_dirty_to_shadow_loop0 (n: nat) (i: Z) (vmid vcpuid dirty: Z) (adt: RData) :=
    match n with
    | O => Some (i, adt)
    | S n' =>
      match sync_dirty_to_shadow_loop0 n' i vmid vcpuid dirty adt with
      | Some (i', adt') =>
        rely ((i' >=? 0) && (i' <=? 31));
        if (Z.land dirty (Z.shiftl 1 i')) =? 0 then
          Some (i' + 1, adt')
        else
          when' reg, adt' == get_int_gpr_spec vmid vcpuid i' adt;
          rely is_int64 reg;
          when adt'' == set_shadow_ctxt_spec vmid vcpuid i' (VZ64 reg) adt';
          Some (i' + 1, adt'')
      | _ => None
      end
    end.

  Definition sync_dirty_to_shadow_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' dirty == get_shadow_dirty_bit_spec vmid vcpuid adt;
    match sync_dirty_to_shadow_loop0 31%nat 0 vmid vcpuid dirty adt with
    | Some (i', adt') => rely is_int i'; Some adt'
    | _ => None
    end.

  Definition prep_wfx_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    set_shadow_dirty_bit_spec vmid vcpuid (VZ64 DIRTY_PC_FLAG) adt.

  Definition prep_hvc_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' psci_fn0 == get_shadow_ctxt_spec vmid vcpuid 0 adt;
    rely is_int64 psci_fn0;
    when adt' == set_shadow_dirty_bit_spec vmid vcpuid (VZ64 1) adt;
    when adt'' == set_int_gpr_spec vmid vcpuid 0 (VZ64 psci_fn0) adt';
    let psci_fn := Z.land psci_fn0 INVALID in
    if psci_fn =? PSCI_0_2_FN64_CPU_ON then
        when' reg1 == get_shadow_ctxt_spec vmid vcpuid 1 adt'';
        rely is_int64 reg1;
        when adt1 == set_int_gpr_spec vmid vcpuid 1 (VZ64 reg1) adt'';
        when' reg2 == get_shadow_ctxt_spec vmid vcpuid 2 adt1;
        rely is_int64 reg2;
        when adt2 == set_int_gpr_spec vmid vcpuid 2 (VZ64 reg2) adt1;
        when' reg3 == get_shadow_ctxt_spec vmid vcpuid 3 adt2;
        rely is_int64 reg3;
        set_int_gpr_spec vmid vcpuid 3 (VZ64 reg3) adt2
    else
      if (psci_fn =? PSCI_0_2_FN_AFFINITY_INFO) || (psci_fn =? PSCI_0_2_FN64_AFFINITY_INFO) then
        when' reg1 == get_shadow_ctxt_spec vmid vcpuid 1 adt'';
        rely is_int64 reg1;
        when adt1 == set_int_gpr_spec vmid vcpuid 1 (VZ64 reg1) adt'';
        when' reg2 == get_shadow_ctxt_spec vmid vcpuid 2 adt1;
        rely is_int64 reg2;
        set_int_gpr_spec vmid vcpuid 2 (VZ64 reg2) adt1
      else
        if psci_fn =? PSCI_0_2_FN_SYSTEM_OFF then
          set_vm_poweroff_spec vmid adt''
        else
          Some adt''.

  Definition prep_abort_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' esr, adt' == get_int_esr_spec vmid vcpuid adt;
    rely is_int64 esr;
    let Rd := Z.land (esr / 65536) 31 in
    when' hpfar_el2 == get_shadow_ctxt_spec vmid vcpuid HPFAR_EL2 adt';
    rely is_int64 hpfar_el2; rely is_gfn (hpfar_el2 / 16);
    let fault_ipa := (hpfar_el2 / 16) * 4096 in
    if fault_ipa <? MAX_MMIO_ADDR then
      when adt'' == set_shadow_dirty_bit_spec vmid vcpuid (VZ64 DIRTY_PC_FLAG) adt';
      if ((Z.land esr ESR_ELx_WNR) =? 0) && ((Z.land esr ESR_ELx_S1PTW) =? 0) then
        set_shadow_dirty_bit_spec vmid vcpuid (VZ64 (Z.shiftl 1 Rd)) adt''
      else
        when' reg == get_shadow_ctxt_spec vmid vcpuid Rd adt'';
        rely is_int64 reg;
        set_int_gpr_spec vmid vcpuid Rd (VZ64 reg) adt''
    else Some adt.

  Definition update_exception_gp_regs_spec0 (vmid: Z) (vcpuid: Z) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' pstate == get_shadow_ctxt_spec vmid vcpuid PSTATE adt;
    rely is_int64 pstate;
    when' pc == get_shadow_ctxt_spec vmid vcpuid PC adt;
    rely is_int64 pc;
    when' new_pc == get_exception_vector_spec (VZ64 pstate) adt;
    rely is_int64 new_pc;
    when adt' == set_shadow_ctxt_spec vmid vcpuid ELR_EL1 (VZ64 pc) adt;
    when adt1 == set_shadow_ctxt_spec vmid vcpuid PC (VZ64 new_pc) adt';
    when adt2 == set_shadow_ctxt_spec vmid vcpuid PSTATE (VZ64 PSTATE_FAULT_BITS_64) adt1;
    when adt3 == set_shadow_ctxt_spec vmid vcpuid SPSR_0 (VZ64 pstate) adt2;
    set_shadow_ctxt_spec vmid vcpuid ESR_EL1 (VZ64 ESR_ELx_EC_UNKNOWN) adt3.

  Definition post_handle_shadow_s2pt_fault_spec0 (vmid: Z) (vcpuid: Z) (addr: Z64) (adt: RData) : option RData :=
    rely is_vm vmid; rely is_vcpu vcpuid;
    when' pte, adt1 == get_int_new_pte_spec vmid vcpuid adt;
    rely is_int64 pte;
    when' level, adt2 == get_int_new_level_spec vmid vcpuid adt1;
    rely is_int64 level;
    if level =? 2 then
      prot_and_map_vm_s2pt_spec vmid addr (VZ64 pte) 2 adt2
    else
      prot_and_map_vm_s2pt_spec vmid addr (VZ64 pte) 3 adt2.

  Inductive reset_gp_regs_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | reset_gp_regs_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: reset_gp_regs_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      reset_gp_regs_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive reset_sys_regs_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | reset_sys_regs_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: reset_sys_regs_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      reset_sys_regs_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive sync_dirty_to_shadow_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | sync_dirty_to_shadow_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: sync_dirty_to_shadow_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      sync_dirty_to_shadow_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive prep_wfx_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | prep_wfx_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: prep_wfx_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      prep_wfx_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive prep_hvc_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | prep_hvc_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: prep_hvc_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      prep_hvc_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive prep_abort_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | prep_abort_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: prep_abort_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      prep_abort_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive update_exception_gp_regs_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | update_exception_gp_regs_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid
      (Hinv: high_level_invariant labd)
      (Hspec: update_exception_gp_regs_spec (Int.unsigned vmid) (Int.unsigned vcpuid) labd = Some labd'):
      update_exception_gp_regs_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive post_handle_shadow_s2pt_fault_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | post_handle_shadow_s2pt_fault_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid vcpuid addr
      (Hinv: high_level_invariant labd)
      (Hspec: post_handle_shadow_s2pt_fault_spec (Int.unsigned vmid) (Int.unsigned vcpuid) (VZ64 (Int64.unsigned addr)) labd = Some labd'):
      post_handle_shadow_s2pt_fault_spec_low_step s WB ((Vint vmid)::(Vint vcpuid)::(Vlong addr)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition reset_gp_regs_spec_low: compatsem LDATAOps :=
      csem reset_gp_regs_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition reset_sys_regs_spec_low: compatsem LDATAOps :=
      csem reset_sys_regs_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition sync_dirty_to_shadow_spec_low: compatsem LDATAOps :=
      csem sync_dirty_to_shadow_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition prep_wfx_spec_low: compatsem LDATAOps :=
      csem prep_wfx_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition prep_hvc_spec_low: compatsem LDATAOps :=
      csem prep_hvc_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition prep_abort_spec_low: compatsem LDATAOps :=
      csem prep_abort_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition update_exception_gp_regs_spec_low: compatsem LDATAOps :=
      csem update_exception_gp_regs_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition post_handle_shadow_s2pt_fault_spec_low: compatsem LDATAOps :=
      csem post_handle_shadow_s2pt_fault_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::nil)) Tvoid.

  End WITHMEM.

End VCPUOpsAuxSpecLow.

```
