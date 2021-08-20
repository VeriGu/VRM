# VCPUOpsSpec

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

Require Import AbstractMachine.Spec.
Require Import VCPUOpsAux.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import VCPUOpsAux.Layer.
Require Import MemoryOps.Spec.
Require Import BootOps.Spec.

Local Open Scope Z_scope.

Section VCPUOpsSpec.

  Definition save_shadow_kvm_regs_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let ec0 := ec (ctxt_regs ctxt) in
    rely is_int64 ec0;
    if ec0 =? ARM_EXCEPTION_TRAP then
      let hsr := esr_el2 (ctxt_regs ctxt) in
      rely is_int64 hsr;
      let hsr_ec := Z.shiftr (Z.land hsr ESR_ELx_EC_MASK) ESR_ELx_EC_SHIFT in
      if hsr_ec =? ESR_ELx_EC_WFx then
        let ctxt' := ctxt {ctxt_states : (ctxt_states ctxt) {dirty : DIRTY_PC_FLAG}} in
        Some adt {shadow_ctxts : (shadow_ctxts adt) # ctxtid == ctxt'}
      else
      if (hsr_ec =? ESR_ELx_EC_HVC32) || (hsr_ec =? ESR_ELx_EC_HVC64) then
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
            else Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == ctxt'}
      else
      if (hsr_ec =? ESR_ELx_EC_IABT_LOW) || (hsr_ec =? ESR_ELx_EC_DABT_LOW) then
        let logn := vmid @ (data_log adt) in
        let esr := (doracle adt) vmid logn in
        rely is_int64 esr;
        let Rd := Z.land (esr / 65536) 31 in
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
        else Some adt
      else
        Some adt {halt: true}
    else
      Some adt.

  Definition restore_shadow_kvm_regs_spec  (adt: RData) : option RData :=
    if halt adt then Some adt else
    let vmid := cur_vmid adt in
    let vcpuid := cur_vcpuid adt in
    rely is_vmid vmid; rely is_vcpu vcpuid;
    let ctxtid := ctxt_id vmid vcpuid in
    let ctxt := ctxtid @ (shadow_ctxts adt) in
    let dirty0 := dirty (ctxt_states ctxt) in
    rely is_int64 dirty0;
    if dirty0 =? INVALID64 then
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
              match reset_sys_regs_loop (Z.to_nat SHADOW_SYS_REGS_SIZE) 1 vcpuid (ctxt_regs ctxt'')
                              (ctxt_states ctxt'') (doracle adt vmid) (logn + 2) with
              | Some (cregs', cstates', logn', i') =>
                Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                     {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse} {data_log: (data_log adt) # vmid == logn'}
                     {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt'' {ctxt_regs: cregs'} {ctxt_states: cstates' {dirty: 0}})}
              | _ => None
              end
          | _ => None
          end
        | _ => None
        end
      | _, _, _ => None
      end
    else
      let ec0 := ec (ctxt_regs ctxt) in
      rely is_int64 ec0;
      let logn := vmid @ (data_log adt) in
      match (
          if ec0 =? ARM_EXCEPTION_TRAP then
            match sync_dirty_to_shadow_loop 31 0 dirty0 (ctxt_regs ctxt) (ctxt_states ctxt) (doracle adt vmid) logn with
            | Some (_, cregs', cstates', logn') => Some (cregs', cstates', logn')
            | _ => None
            end
          else Some (ctxt_regs ctxt, ctxt_states ctxt, logn)
        )
      with
      | Some (cregs', cstates', logn') =>
        let pstate' := pstate cstates' in
        let pc' := pc cstates' in
        let new_pc := exception_vector (VZ64 pstate') in
        rely is_int64 pstate'; rely is_int64 pc'; rely is_int64 new_pc;
        let (cregs'', cstates'') := (if (Z.land dirty0 PENDING_EXCEPT_INJECT_FLAG) =? 0 then (cregs', cstates')
                                     else (cregs' {elr_el1 : pc'}, cstates' {pc : new_pc} {pstate : PSTATE_FAULT_BITS_64}
                                                                            {spsr_0 : pstate'} {esr_el1 : ESR_ELx_EC_UNKNOWN})) in
        let cstates''' := (if (Z.land dirty0 DIRTY_PC_FLAG) =? 0 then cstates'' {dirty: 0}
                           else cstates' {pc : (pc cstates'') + 4} {dirty: 0}) in
        let cregs''' := cregs'' {far_el2: 0} in
        let clogn := vmid @ (core_data_log adt) in
        let addr := core_doracle adt vmid clogn in
        rely is_int64 addr;
        if (0 <? addr) && (addr <? KVM_ADDR_SPACE) then
          let pte := core_doracle adt vmid (clogn + 1) in
          let level := core_doracle adt vmid (clogn + 2) in
          rely is_int64 pte; rely is_int64 level;
          prot_and_map_vm_s2pt_spec vmid (VZ64 addr) (VZ64 pte) (if level =? 2 then 2 else 3)
                                    (adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'''} {ctxt_states: cstates'''})}
                                         {data_log: (data_log adt) # vmid == logn'} {core_data_log: (core_data_log adt) # vmid == (clogn + 3)})
        else
          Some adt {shadow_ctxts: (shadow_ctxts adt) # ctxtid == (ctxt {ctxt_regs: cregs'''} {ctxt_states: cstates'''})}
               {data_log: (data_log adt) # vmid == logn'} {core_data_log: (core_data_log adt) # vmid == (clogn + 1)}
      | _ => None
      end.

End VCPUOpsSpec.

Section VCPUOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := VCPUOpsAux_ops) LDATA).

  Definition save_shadow_kvm_regs_spec0  (adt: RData) : option RData :=
    when vmid == get_cur_vmid_spec adt;
    rely is_vmid vmid;
    when vcpuid == get_cur_vcpuid_spec adt;
    rely is_vcpu vcpuid;
    when' ec == get_shadow_ctxt_spec vmid vcpuid EC adt;
    rely is_int64 ec;
    if ec =? ARM_EXCEPTION_TRAP then
      when' hsr == get_shadow_ctxt_spec vmid vcpuid ESR_EL2 adt;
      rely is_int64 hsr;
      let hsr_ec := Z.shiftr (Z.land hsr ESR_ELx_EC_MASK) ESR_ELx_EC_SHIFT in
      if hsr_ec =? ESR_ELx_EC_WFx then
        prep_wfx_spec vmid vcpuid adt
      else
      if hsr_ec =? ESR_ELx_EC_HVC32 then
        prep_hvc_spec vmid vcpuid adt
      else
      if hsr_ec =? ESR_ELx_EC_HVC64 then
        prep_hvc_spec vmid vcpuid adt
      else
      if hsr_ec =? ESR_ELx_EC_IABT_LOW then
        prep_abort_spec vmid vcpuid adt
      else
      if hsr_ec =? ESR_ELx_EC_DABT_LOW then
        prep_abort_spec vmid vcpuid adt
      else
        panic_spec adt
    else
      Some adt.

  Definition restore_shadow_kvm_regs_spec0  (adt: RData) : option RData :=
    when vmid == get_cur_vmid_spec adt;
    rely is_vmid vmid;
    when vcpuid == get_cur_vcpuid_spec adt;
    rely is_vcpu vcpuid;
    when' dirty == get_shadow_ctxt_spec vmid vcpuid DIRTY adt;
    rely is_int64 dirty;
    if dirty =? INVALID64 then
      when adt' == reset_gp_regs_spec vmid vcpuid adt;
      when adt'' == reset_sys_regs_spec vmid vcpuid adt';
      set_shadow_dirty_bit_spec vmid vcpuid (VZ64 0) adt''
    else
      when' ec == get_shadow_ctxt_spec vmid vcpuid EC adt;
      rely is_int64 ec;
      when adt' == (if ec =? ARM_EXCEPTION_TRAP then
                      sync_dirty_to_shadow_spec vmid vcpuid adt
                    else Some adt);
      when adt'' == (if (Z.land dirty PENDING_EXCEPT_INJECT_FLAG) =? 0 then
                       Some adt'
                     else update_exception_gp_regs_spec vmid vcpuid adt');
      when adt3 == (if (Z.land dirty DIRTY_PC_FLAG) =? 0 then
                      Some adt''
                    else when' pc == get_shadow_ctxt_spec vmid vcpuid PC adt'';
                        rely is_addr pc;
                        set_shadow_ctxt_spec vmid vcpuid PC (VZ64 (pc + 4)) adt'');
      when adt4 == set_shadow_dirty_bit_spec vmid vcpuid (VZ64 0) adt3;
      when adt5 == set_shadow_ctxt_spec vmid vcpuid FAR_EL2 (VZ64 0) adt4;
      when' addr, adt6 == get_vm_fault_addr_spec vmid vcpuid adt5;
      rely is_int64 addr;
      if (0 <? addr) && (addr <? KVM_ADDR_SPACE) then
        post_handle_shadow_s2pt_fault_spec vmid vcpuid (VZ64 addr) adt6
      else
        Some adt6.

  Inductive save_shadow_kvm_regs_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | save_shadow_kvm_regs_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: save_shadow_kvm_regs_spec0  labd = Some labd'):
      save_shadow_kvm_regs_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive restore_shadow_kvm_regs_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | restore_shadow_kvm_regs_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'
      (Hinv: high_level_invariant labd)
      (Hspec: restore_shadow_kvm_regs_spec0  labd = Some labd'):
      restore_shadow_kvm_regs_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition save_shadow_kvm_regs_spec_low: compatsem LDATAOps :=
      csem save_shadow_kvm_regs_spec_low_step (type_of_list_type nil) Tvoid.

    Definition restore_shadow_kvm_regs_spec_low: compatsem LDATAOps :=
      csem restore_shadow_kvm_regs_spec_low_step (type_of_list_type nil) Tvoid.

  End WITHMEM.

End VCPUOpsSpecLow.

```
