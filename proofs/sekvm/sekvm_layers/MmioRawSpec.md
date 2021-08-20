# MmioRawSpec

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
Require Import RData.
Require Import BootOps.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Definition ARM_SMMU_PGSHIFT := 12.
Definition SMMU_GLOBAL_BASE := 32768.
Hint Unfold ARM_SMMU_PGSHIFT SMMU_GLOBAL_BASE.

Section MmioRawSpec.

  Definition host_get_mmio_data_spec (hsr: Z) (adt: RData) : option Z64 :=
    rely is_int hsr;
    if halt adt then Some (VZ64 0) else
    let vcpuid := cur_vcpuid adt in
    rely is_vcpu vcpuid;
    let rt := host_dabt_get_rd' hsr in
    rely is_int rt;
    when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
    rely is_int64 data;
    Some (VZ64 data).

  Definition smmu_init_pte_spec (prot: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match prot, addr with
    | VZ64 prot, VZ64 addr =>
      rely is_addr addr; rely (prot <? 9223372036854775807);
      let pte := Z.lor addr (Z.lor prot PTE_AF_OR_SH_IS) in
      Some (VZ64 pte)
    end.

  Definition smmu_get_cbndx_spec (offset: Z64) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      rely (offset >=? SMMU_GLOBAL_BASE);
      let cbndx := Z.shiftr (offset - SMMU_GLOBAL_BASE) ARM_SMMU_PGSHIFT in
      rely is_smmu_cfg cbndx;
      Some cbndx
    end.

End MmioRawSpec.

Section MmioRawSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := BootOps_ops) LDATA).

  Definition host_get_mmio_data_spec0 (hsr: Z) (adt: RData) : option Z64 :=
    when vcpuid == get_cur_vcpuid_spec adt;
    rely is_vcpu vcpuid;
    when rt == host_dabt_get_rd_spec hsr adt;
    rely is_int rt;
    when' data == get_shadow_ctxt_spec HOSTVISOR vcpuid rt adt;
    rely is_int64 data;
    Some (VZ64 data).

  Definition smmu_init_pte_spec0 (prot: Z64) (addr: Z64) (adt: RData) : option Z64 :=
    match prot, addr with
    | VZ64 prot, VZ64 addr =>
      rely is_addr addr; rely (prot <? 9223372036854775807);
      let pte := Z.lor addr (Z.lor prot PTE_AF_OR_SH_IS) in
      Some (VZ64 pte)
    end.

  Definition smmu_get_cbndx_spec0 (offset: Z64) (adt: RData) : option Z :=
    match offset with
    | VZ64 offset =>
      rely (offset >=? SMMU_GLOBAL_BASE);
      let cbndx := Z.shiftr (offset - SMMU_GLOBAL_BASE) ARM_SMMU_PGSHIFT in
      rely is_smmu_cfg cbndx;
      Some cbndx
    end.

  Inductive host_get_mmio_data_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | host_get_mmio_data_spec_low_intro s (WB: _ -> Prop) m'0 labd hsr res
      (Hinv: high_level_invariant labd)
      (Hspec: host_get_mmio_data_spec0 (Int.unsigned hsr) labd = Some (VZ64 (Int64.unsigned res))):
      host_get_mmio_data_spec_low_step s WB ((Vint hsr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive smmu_init_pte_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | smmu_init_pte_spec_low_intro s (WB: _ -> Prop) m'0 labd prot addr res
      (Hinv: high_level_invariant labd)
      (Hspec: smmu_init_pte_spec0 (VZ64 (Int64.unsigned prot)) (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      smmu_init_pte_spec_low_step s WB ((Vlong prot)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive smmu_get_cbndx_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | smmu_get_cbndx_spec_low_intro s (WB: _ -> Prop) m'0 labd offset res
      (Hinv: high_level_invariant labd)
      (Hspec: smmu_get_cbndx_spec0 (VZ64 (Int64.unsigned offset)) labd = Some (Int.unsigned res)):
      smmu_get_cbndx_spec_low_step s WB ((Vlong offset)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition host_get_mmio_data_spec_low: compatsem LDATAOps :=
      csem host_get_mmio_data_spec_low_step (type_of_list_type (Tint32::nil)) Tint64.

    Definition smmu_init_pte_spec_low: compatsem LDATAOps :=
      csem smmu_init_pte_spec_low_step (type_of_list_type (Tint64::Tint64::nil)) Tint64.

    Definition smmu_get_cbndx_spec_low: compatsem LDATAOps :=
      csem smmu_get_cbndx_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

  End WITHMEM.

End MmioRawSpecLow.
```
