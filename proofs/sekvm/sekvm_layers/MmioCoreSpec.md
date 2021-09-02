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

Require Import MmioCoreAux.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioCoreAux.Layer.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MmioCoreSpec.

  Definition handle_smmu_write_spec (hsr: Z) (fault_ipa: Z64) (len: Z) (index: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      rely is_int hsr; rely is_addr fault_ipa; rely is_smmu index;
      if halt adt then Some adt else
      match SMMU_ID @ (lock adt) with
      | LockOwn true =>
        let vcpuid := cur_vcpuid adt in
        let rt := host_dabt_get_rd' hsr in
        rely is_vcpu vcpuid; rely is_int rt;
        let offset := Z.land fault_ipa SMMU_OFFSET_MASK in
        if offset <? SMMU_GLOBAL_BASE then
          when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
          rely is_int64 data;
          when ret ==
            (if (offset >=? 0) && (offset <=? ARM_SMMU_GR1_BASE) then
              if offset =? ARM_SMMU_GR0_sCR0 then
                let smmu_enable := Z.land (Z.shiftr data sCR0_SMCFCFG_SHIFT) 1 in
                if smmu_enable =? 0 then Some 0 else Some 1
              else if offset =? ARM_SMMU_GR0_sCR2 then
                      if (Z.land data 255) =? 0 then Some 1 else Some 0
                  else Some 1
            else if (offset >=? ARM_SMMU_GR1_BASE) && (offset <? ARM_SMMU_GR1_END) then
                    let n := (offset - ARM_SMMU_GR1_BASE) / 4 in
                    rely is_smmu_cfg n;
                    let vmid := (smmu_id index n) @ (smmu_vmid (shared adt)) in
                    rely is_vmid vmid;
                    let type := Z.shiftr data CBAR_TYPE_SHIFT in
                    let t_vmid := Z.land data CBAR_VMID_MASK in
                    if vmid =? 0 then Some 1
                    else
                      if (type =? CBAR_TYPE_S2_TRANS) && (vmid =? t_vmid) then Some 1 else Some 0
                else Some 1);
          if ret =? 0 then Some adt {halt: true}
          else if len =? 8 then Some adt
               else if len =? 4 then Some adt
                    else Some adt {halt: true}
        else
          let off' := offset - SMMU_GLOBAL_BASE in
          let cb_offset := Z.land off' ARM_SMMU_PGSHIFT_MASK in
          if cb_offset =? ARM_SMMU_CB_TTBR0 then
            let cbndx := Z.shiftr (offset - SMMU_GLOBAL_BASE) ARM_SMMU_PGSHIFT in
            rely is_smmu_cfg cbndx;
            let val := SMMU_TTBR index cbndx in
            if len =? 8 then Some adt
            else if len =? 4 then Some adt
                 else Some adt {halt: true}
          else if cb_offset =? ARM_SMMU_CB_CONTEXTIDR then Some adt {halt: true}
               else
                 if len =? 8 then
                   when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
                   rely is_int64 data;
                   Some adt
                 else if len =? 4 then Some adt
                      else Some adt {halt: true}
      | _ => None
      end
    end.

  Definition handle_smmu_read_spec (hsr: Z) (fault_ipa: Z64) (len: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      rely is_int hsr;
      if halt adt then Some adt else
      let vcpuid := cur_vcpuid adt in
      let rt := host_dabt_get_rd' hsr in
      let n := HOSTVISOR @ (data_log adt) in
      let data := (doracle adt) HOSTVISOR n in
      rely is_vcpu vcpuid; rely is_int rt; rely is_int64 data;
      let dlog' := (data_log adt) # HOSTVISOR == (n + 1) in
      if len =? 8 then
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 data) (adt {data_log: dlog'})
      else if len =? 4 then
        set_shadow_ctxt_spec HOSTVISOR vcpuid rt (VZ64 (Z.land data INVALID)) (adt {data_log: dlog'})
      else
        Some adt {halt: true}
    end.

End MmioCoreSpec.

Section MmioCoreSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioCoreAux_ops) LDATA).

  Definition handle_smmu_write_spec0 (hsr: Z) (fault_ipa: Z64) (len: Z) (index: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      let offset := Z.land fault_ipa SMMU_OFFSET_MASK in
      if offset <? SMMU_GLOBAL_BASE then
        when ret == handle_smmu_global_access_spec hsr (VZ64 offset) index adt;
        rely is_int ret;
        if ret =? 0 then
          panic_spec adt
        else
          __handle_smmu_write_spec hsr (VZ64 fault_ipa) len (VZ64 0) 0 adt
      else
        when ret == handle_smmu_cb_access_spec (VZ64 offset) adt;
        rely is_int ret;
        if ret =? 0 then
          panic_spec adt
        else
          if ret =? 2 then
            when cbndx == smmu_get_cbndx_spec (VZ64 offset) adt;
            rely is_int cbndx;
            when' val == get_smmu_cfg_hw_ttbr_spec cbndx index adt;
            rely is_int64 val;
            __handle_smmu_write_spec hsr (VZ64 fault_ipa) len (VZ64 val) 1 adt
          else
            __handle_smmu_write_spec hsr (VZ64 fault_ipa) len (VZ64 0) 0 adt
    end.

  Definition handle_smmu_read_spec0 (hsr: Z) (fault_ipa: Z64) (len: Z) (adt: RData) : option RData :=
    match fault_ipa with
    | VZ64 fault_ipa =>
      let offset := Z.land fault_ipa SMMU_OFFSET_MASK in
      if offset <? SMMU_GLOBAL_BASE then
        __handle_smmu_read_spec hsr (VZ64 fault_ipa) len adt
      else
        __handle_smmu_read_spec hsr (VZ64 fault_ipa) len adt
    end.

  Inductive handle_smmu_write_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_smmu_write_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' hsr fault_ipa len index
      (Hinv: high_level_invariant labd)
      (Hspec: handle_smmu_write_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) (Int.unsigned index) labd = Some labd'):
      handle_smmu_write_spec_low_step s WB ((Vint hsr)::(Vlong fault_ipa)::(Vint len)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive handle_smmu_read_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | handle_smmu_read_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' hsr fault_ipa len
      (Hinv: high_level_invariant labd)
      (Hspec: handle_smmu_read_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) labd = Some labd'):
      handle_smmu_read_spec_low_step s WB ((Vint hsr)::(Vlong fault_ipa)::(Vint len)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition handle_smmu_write_spec_low: compatsem LDATAOps :=
      csem handle_smmu_write_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::Tint32::nil)) Tvoid.

    Definition handle_smmu_read_spec_low: compatsem LDATAOps :=
      csem handle_smmu_read_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::nil)) Tvoid.

  End WITHMEM.

End MmioCoreSpecLow.

```
