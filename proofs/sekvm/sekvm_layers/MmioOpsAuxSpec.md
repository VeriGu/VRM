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

Require Import AbstractMachine.Spec.
Require Import MmioCore.Layer.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioCore.Spec.

Local Open Scope Z_scope.

Section MmioOpsAuxSpec.

  Fixpoint is_smmu_range_loop (n: nat) (addr: Z) (i: Z) (res: Z) (conf: SMMUConf) :=
    match n with
    | O => Some (i, res)
    | S n' =>
      match is_smmu_range_loop n' addr i res conf with
      | Some (i', res') =>
        match i' @ (smmu_phys_base conf), i' @ (smmu_size conf) with
        | base, size =>
          rely is_addr base; rely is_int64 size; rely is_addr (base + size);
          if (base <=? addr) && (addr <? base + size) then
            Some (i'+1, i')
          else
            Some (i'+1, res')
        end
      | _ => None
      end
    end.

  Definition is_smmu_range_spec (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      rely is_addr addr;
      if halt adt then Some INVALID else
      let conf := smmu_conf adt in
      let total_smmu := smmu_num conf in
      rely is_smmu total_smmu;
      match is_smmu_range_loop (Z.to_nat total_smmu) addr 0 INVALID conf with
      | Some (i', res') => Some res'
      | _ => None
      end
    end.

  Definition handle_host_mmio_specx index fault_ipa len is_write rt cregs cstates rcregs dorc logn smmu :=
    if is_write =? 0 then
      let data := dorc HOSTVISOR logn in
      rely is_int64 data;
      if len =? 8 then
        match set_shadow_ctxt_specx rt data cregs cstates with
        | (cregs', cstates') =>
          Some (false, logn + 1, cregs', cstates', rcregs {esr_el2: (elr_el2 rcregs) + 4})
        end
      else if len =? 4 then
             match set_shadow_ctxt_specx rt (Z.land data INVALID) cregs cstates with
             | (cregs', cstates') =>
               Some (false, logn + 1, cregs', cstates', rcregs {esr_el2: (elr_el2 rcregs) + 4})
             end
           else Some (true, logn, cregs, cstates, rcregs)
    else
      let data := get_shadow_ctxt_specx rt cregs cstates in
      rely is_int64 data;
      let ret_state := (if len =? 8 then Some (false, logn, cregs, cstates, rcregs {esr_el2: (elr_el2 rcregs) + 4})
                        else if len =? 4 then Some (false, logn, cregs, cstates, rcregs {esr_el2: (elr_el2 rcregs) + 4})
                             else Some (true, logn, cregs, cstates, rcregs)) in
      let offset := Z.land fault_ipa SMMU_OFFSET_MASK in
      if offset <? Spec.SMMU_GLOBAL_BASE
      then
        when ret ==
          (if (offset >=? 0) && (offset <=? ARM_SMMU_GR1_BASE)
            then
              if offset =? ARM_SMMU_GR0_sCR0
              then let smmu_enable := Z.land (Z.shiftr data sCR0_SMCFCFG_SHIFT) 1 in if smmu_enable =? 0 then Some 0 else Some 1
              else if offset =? ARM_SMMU_GR0_sCR2 then if Z.land data 255 =? 0 then Some 1 else Some 0 else Some 1
            else
              if (offset >=? ARM_SMMU_GR1_BASE) && (offset <? ARM_SMMU_GR1_END)
              then
                let n := (offset - ARM_SMMU_GR1_BASE) / 4 in
                rely is_smmu_cfg n;
                let vmid := (smmu_id index n) @ smmu in
                rely is_vmid vmid;
                let type := Z.shiftr data CBAR_TYPE_SHIFT in
                let t_vmid := Z.land data CBAR_VMID_MASK in
                if vmid =? 0 then Some 1 else if (type =? CBAR_TYPE_S2_TRANS) && (vmid =? t_vmid) then Some 1 else Some 0
              else Some 1);
        if ret =? 0 then Some (true, logn, cregs, cstates, rcregs)
        else  ret_state
      else
        let off' := offset - Spec.SMMU_GLOBAL_BASE in
        let cb_offset := Z.land off' ARM_SMMU_PGSHIFT_MASK in
        if cb_offset =? ARM_SMMU_CB_TTBR0
        then
          let cbndx := Z.shiftr (offset - Spec.SMMU_GLOBAL_BASE) Spec.ARM_SMMU_PGSHIFT in
          rely is_smmu_cfg cbndx;
          ret_state
        else
          if cb_offset =? ARM_SMMU_CB_CONTEXTIDR
          then Some (true, logn, cregs, cstates, rcregs)
          else ret_state.

  Definition handle_host_mmio_spec (addr: Z64) (index: Z) (hsr: Z) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely is_addr addr; rely is_smmu index; rely is_int hsr;
      let fault_ipa := Z.lor addr (Z.land (far_el2 (ctxt_regs (regs adt))) 4095) in
      let len := host_dabt_get_as' hsr in
      let is_write := host_dabt_is_write' hsr in
      let rt := host_dabt_get_rd' hsr in
      rely is_addr fault_ipa; rely is_int len; rely is_int is_write; rely is_int rt;
      if halt adt then Some adt else
      match SMMU_ID @ (lock adt) with
      | LockOwn true =>
        let logn := HOSTVISOR @ (data_log adt) in
        let smmu := smmu_vmid (shared adt) in
        let vcpuid := cur_vcpuid adt in
        rely is_vcpu vcpuid;
        let ctxt := (ctxt_id HOSTVISOR vcpuid) @ (shadow_ctxts adt) in
        match handle_host_mmio_specx index fault_ipa len is_write rt (ctxt_regs ctxt) (ctxt_states ctxt) (ctxt_regs (regs adt))(doracle adt) logn smmu with
        | Some (halt', logn', cregs', cstates', rcregs') =>
          Some adt {halt: halt'} {regs: (regs adt) {ctxt_regs: rcregs'}} {data_log: if logn =? logn' then (data_log adt) else (data_log adt) # HOSTVISOR == logn'}
               {shadow_ctxts: if halt' || (negb (is_write =? 0)) then (shadow_ctxts adt)
                              else (shadow_ctxts adt) # (ctxt_id HOSTVISOR vcpuid) == (ctxt {ctxt_regs: cregs'} {ctxt_states: cstates'})}
        | _ => None
        end
      | _ => None
      end
    end.

End MmioOpsAuxSpec.

Section MmioOpsAuxSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioCore_ops) LDATA).

  Fixpoint is_smmu_range_loop0 (n: nat) (addr: Z) (i: Z) (res: Z) (adt: RData) :=
    match n with
    | O => Some (i, res)
    | S n' =>
      match is_smmu_range_loop0 n' addr i res adt with
      | Some (i', res') =>
        rely is_smmu i'; rely is_int res';
        when' base == get_smmu_base_spec i' adt;
        rely is_addr base;
        when' size == get_smmu_size_spec i' adt;
        rely is_int64 size; rely is_addr (base + size);
        if (base <=? addr) && (addr <? base + size) then
          Some (i'+1, i')
        else
          Some (i'+1, res')
      | _ => None
      end
    end.

  Definition is_smmu_range_spec0 (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      when total_smmu == get_smmu_num_spec adt;
      rely is_smmu total_smmu; rely is_addr addr;
      match is_smmu_range_loop0 (Z.to_nat total_smmu) addr 0 INVALID adt with
      | Some (i', res') =>
        rely is_smmu i'; rely is_int res'; Some res'
      | _ => None
      end
    end.

  Definition handle_host_mmio_spec0 (addr: Z64) (index: Z) (hsr: Z) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      when' fault_ipa == host_get_fault_ipa_spec (VZ64 addr) adt;
      when len == host_dabt_get_as_spec hsr adt;
      when is_write == host_dabt_is_write_spec hsr adt;
      rely is_int64 fault_ipa; rely is_int len; rely is_int is_write;
      if is_write =? 0 then
        when adt' == handle_smmu_read_spec hsr (VZ64 fault_ipa) len adt;
        host_skip_instr_spec adt'
      else
        when adt' == handle_smmu_write_spec hsr (VZ64 fault_ipa) len index adt;
        host_skip_instr_spec adt'
    end.

  Inductive is_smmu_range_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | is_smmu_range_spec_low_intro s (WB: _ -> Prop) m'0 labd addr res
      (Hinv: high_level_invariant labd)
      (Hspec: is_smmu_range_spec0 (VZ64 (Int64.unsigned addr)) labd = Some (Int.unsigned res)):
      is_smmu_range_spec_low_step s WB ((Vlong addr)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive handle_host_mmio_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_host_mmio_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' addr index hsr
      (Hinv: high_level_invariant labd)
      (Hspec: handle_host_mmio_spec0 (VZ64 (Int64.unsigned addr)) (Int.unsigned index) (Int.unsigned hsr) labd = Some labd'):
      handle_host_mmio_spec_low_step s WB ((Vlong addr)::(Vint index)::(Vint hsr)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition is_smmu_range_spec_low: compatsem LDATAOps :=
      csem is_smmu_range_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

    Definition handle_host_mmio_spec_low: compatsem LDATAOps :=
      csem handle_host_mmio_spec_low_step (type_of_list_type (Tint64::Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End MmioOpsAuxSpecLow.

```
