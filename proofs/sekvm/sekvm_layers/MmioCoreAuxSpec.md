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

Require Import MmioRaw.Layer.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MmioCoreAuxSpec.

  Definition handle_smmu_global_access_spec (hsr: Z) (offset: Z64) (smmu_index: Z) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      rely is_int hsr;
      if halt adt then Some 0 else
      match SMMU_ID @ (lock adt) with
      | LockOwn true =>
        let vcpuid := cur_vcpuid adt in
        rely is_vcpu vcpuid;
        let rt := host_dabt_get_rd' hsr in
        rely is_int rt;
        when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
        rely is_int64 data;
        if (offset >=? 0) && (offset <=? ARM_SMMU_GR1_BASE) then
          if offset =? ARM_SMMU_GR0_sCR0 then
            let smmu_enable := Z.land (Z.shiftr data sCR0_SMCFCFG_SHIFT) 1 in
            if smmu_enable =? 0 then Some 0 else Some 1
          else if offset =? ARM_SMMU_GR0_sCR2 then
                  if (Z.land data 255) =? 0 then Some 1 else Some 0
              else Some 1
        else if (offset >=? ARM_SMMU_GR1_BASE) && (offset <? ARM_SMMU_GR1_END) then
                let n := (offset - ARM_SMMU_GR1_BASE) / 4 in
                rely is_smmu smmu_index; rely is_smmu_cfg n;
                let vmid := (smmu_id smmu_index n) @ (smmu_vmid (shared adt)) in
                rely is_vmid vmid;
                let type := Z.shiftr data CBAR_TYPE_SHIFT in
                let t_vmid := Z.land data CBAR_VMID_MASK in
                if vmid =? 0 then Some 1
                else
                  if (type =? CBAR_TYPE_S2_TRANS) && (vmid =? t_vmid) then Some 1 else Some 0
             else Some 1
      | _ => None
      end
    end.

  Definition handle_smmu_cb_access_spec (offset: Z64) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      rely (offset >=? SMMU_GLOBAL_BASE);
      if halt adt then Some 0 else
      let off' := offset - SMMU_GLOBAL_BASE in
      let cb_offset := Z.land off' ARM_SMMU_PGSHIFT_MASK in
      if cb_offset =? ARM_SMMU_CB_TTBR0 then Some 2
      else if cb_offset =? ARM_SMMU_CB_CONTEXTIDR then Some 0 else Some 1
    end.

  Definition __handle_smmu_write_spec (hsr: Z) (fault_ipa: Z64) (len: Z) (val: Z64) (write_val: Z) (adt: RData) : option RData :=
    match fault_ipa, val with
    | VZ64 fault_ipa, VZ64 val =>
      rely is_int hsr;
      if halt adt then Some adt else
      if len =? 8 then
        if write_val =? 0 then
          let vcpuid := cur_vcpuid adt in
          rely is_vcpu vcpuid;
          let rt := host_dabt_get_rd' hsr in
          rely is_int rt;
          when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
          rely is_int64 data;
          Some adt
        else
          Some adt
      else
        if len =? 4 then
          Some adt
        else
          Some adt {halt: true}
    end.

  Definition __handle_smmu_read_spec (hsr: Z) (fault_ipa: Z64) (len: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      rely is_int hsr;
      if halt adt then Some adt else
      let vcpuid := cur_vcpuid adt in
      rely is_vcpu vcpuid;
      let rt := host_dabt_get_rd' hsr in
      rely is_int rt;
      let n := HOSTVISOR @ (data_log adt) in
      let data := (doracle adt) HOSTVISOR n in
      rely is_int64 data;
      let dlog' := (data_log adt) # HOSTVISOR == (n + 1) in
      if len =? 8 then
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 data) (adt {data_log: dlog'})
      else if len =? 4 then
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 (Z.land data INVALID)) (adt {data_log: dlog'})
      else
        Some adt {halt: true}
    end.

End MmioCoreAuxSpec.

Section MmioCoreAuxSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioRaw_ops) LDATA).

  Definition handle_smmu_global_access_spec0 (hsr: Z) (offset: Z64) (smmu_index: Z) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      when' data == host_get_mmio_data_spec hsr adt;
      rely is_int64 data;
      if (offset >=? 0) && (offset <=? ARM_SMMU_GR1_BASE) then
        if offset =? ARM_SMMU_GR0_sCR0 then
          let smmu_enable := Z.land (Z.shiftr data sCR0_SMCFCFG_SHIFT) 1 in
          if smmu_enable =? 0 then
            check_spec 0 adt
          else
            check_spec 1 adt
        else if offset =? ARM_SMMU_GR0_sCR2 then
                if (Z.land data 255) =? 0 then
                  check_spec 1 adt
                else
                  check_spec 0 adt
        else
          check_spec 1 adt
      else if (offset >=? ARM_SMMU_GR1_BASE) && (offset <? ARM_SMMU_GR1_END) then
              let n := (offset - ARM_SMMU_GR1_BASE) / 4 in
              when vmid == get_smmu_cfg_vmid_spec n smmu_index adt;
              rely is_vmid vmid;
              let type := Z.shiftr data CBAR_TYPE_SHIFT in
              let t_vmid := Z.land data CBAR_VMID_MASK in
              if vmid =? 0 then
                check_spec 1 adt
              else
                if (type =? CBAR_TYPE_S2_TRANS) && (vmid =? t_vmid) then
                  check_spec 1 adt
                else
                  check_spec 0 adt
            else
              check_spec 1 adt
    end.

  Definition handle_smmu_cb_access_spec0 (offset: Z64) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      rely (offset >=? SMMU_GLOBAL_BASE);
      let off' := offset - SMMU_GLOBAL_BASE in
      let cb_offset := Z.land off' ARM_SMMU_PGSHIFT_MASK in
      if cb_offset =? ARM_SMMU_CB_TTBR0 then
        check_spec 2 adt
      else if cb_offset =? ARM_SMMU_CB_CONTEXTIDR then
              check_spec 0 adt
      else
              check_spec 1 adt
    end.

  Definition __handle_smmu_write_spec0 (hsr: Z) (fault_ipa: Z64) (len: Z) (val: Z64) (write_val: Z) (adt: RData) : option RData :=
    match fault_ipa, val with
    | VZ64 fault_ipa, VZ64 val =>
      if len =? 8 then
        if write_val =? 0 then
          when' data == host_get_mmio_data_spec hsr adt;
          rely is_int64 data;
          writeq_relaxed_spec (VZ64 data) (VZ64 fault_ipa) adt
        else
          writeq_relaxed_spec (VZ64 val) (VZ64 fault_ipa) adt
      else
        if len =? 4 then
          writel_relaxed_spec (VZ64 val) (VZ64 fault_ipa) adt
        else
          panic_spec adt
    end.

  Definition __handle_smmu_read_spec0 (hsr: Z) (fault_ipa: Z64) (len: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      when rt == host_dabt_get_rd_spec hsr adt;
      rely is_int rt;
      when vcpuid == get_cur_vcpuid_spec adt;
      rely is_vcpu vcpuid;
      if len =? 8 then
        when' data, adt' == readq_relaxed_spec (VZ64 fault_ipa) adt;
        rely is_int64 data;
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 data) adt'
      else if len =? 4 then
        when' data, adt' == readl_relaxed_spec (VZ64 fault_ipa) adt;
        rely is_int64 data;
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 data) adt'
      else
        panic_spec adt
    end.

  Inductive handle_smmu_global_access_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_smmu_global_access_spec_low_intro s (WB: _ -> Prop) m'0 labd hsr offset smmu_index res
      (Hinv: high_level_invariant labd)
      (Hspec: handle_smmu_global_access_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned offset)) (Int.unsigned smmu_index) labd = Some (Int.unsigned res)):
      handle_smmu_global_access_spec_low_step s WB ((Vint hsr)::(Vlong offset)::(Vint smmu_index)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive handle_smmu_cb_access_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_smmu_cb_access_spec_low_intro s (WB: _ -> Prop) m'0 labd offset res
      (Hinv: high_level_invariant labd)
      (Hspec: handle_smmu_cb_access_spec0 (VZ64 (Int64.unsigned offset)) labd = Some (Int.unsigned res)):
      handle_smmu_cb_access_spec_low_step s WB ((Vlong offset)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive __handle_smmu_write_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | __handle_smmu_write_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' hsr fault_ipa len val write_val
      (Hinv: high_level_invariant labd)
      (Hspec: __handle_smmu_write_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) (VZ64 (Int64.unsigned val)) (Int.unsigned write_val) labd = Some labd'):
      __handle_smmu_write_spec_low_step s WB ((Vint hsr)::(Vlong fault_ipa)::(Vint len)::(Vlong val)::(Vint write_val)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive __handle_smmu_read_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | __handle_smmu_read_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' hsr fault_ipa len
      (Hinv: high_level_invariant labd)
      (Hspec: __handle_smmu_read_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) labd = Some labd'):
      __handle_smmu_read_spec_low_step s WB ((Vint hsr)::(Vlong fault_ipa)::(Vint len)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition handle_smmu_global_access_spec_low: compatsem LDATAOps :=
      csem handle_smmu_global_access_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::nil)) Tint32.

    Definition handle_smmu_cb_access_spec_low: compatsem LDATAOps :=
      csem handle_smmu_cb_access_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

    Definition __handle_smmu_write_spec_low: compatsem LDATAOps :=
      csem __handle_smmu_write_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::Tint64::Tint32::nil)) Tvoid.

    Definition __handle_smmu_read_spec_low: compatsem LDATAOps :=
      csem __handle_smmu_read_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::nil)) Tvoid.

  End WITHMEM.

End MmioCoreAuxSpecLow.

```
