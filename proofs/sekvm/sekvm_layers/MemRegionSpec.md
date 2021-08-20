# MemRegionSpec

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
Require Import MmioSPTOps.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MemRegionSpec.

  Fixpoint mem_region_search_loop (n: nat) (addr: Z) (i: Z) (res: Z) (adt: RData) :=
    match n with
    | O => Some (i, res)
    | S n' =>
      match mem_region_search_loop n' addr i res adt with
      | Some (i', res') =>
        rely is_memblock i'; rely is_int res';
        when' base == get_mem_region_base_spec i' adt;
        rely is_addr base;
        when' size == get_mem_region_size_spec i' adt;
        rely is_int64 size; rely is_addr (base + size);
        if (base <=? addr) && (addr <? base + size) then
          Some (i'+1, i')
        else
          Some (i'+1, res')
      | _ => None
      end
    end.

  Definition mem_region_search_spec (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      when total_regions == get_mem_region_cnt_spec adt;
      rely is_memblock total_regions; rely is_addr addr;
      match mem_region_search_loop (Z.to_nat total_regions) addr 0 INVALID adt with
      | Some (i', res') =>
        rely is_memblock i'; rely is_int res'; Some res'
      | _ => None
      end
    end.

End MemRegionSpec.

Section MemRegionSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioSPTOps_ops) LDATA).

  Inductive mem_region_search_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | mem_region_search_spec_low_intro s (WB: _ -> Prop) m'0 labd addr res
      (Hinv: high_level_invariant labd)
      (Hspec: mem_region_search_spec (VZ64 (Int64.unsigned addr)) labd = Some (Int.unsigned res)):
      mem_region_search_spec_low_step s WB ((Vlong addr)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition mem_region_search_spec_low: compatsem LDATAOps :=
      csem mem_region_search_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

  End WITHMEM.

End MemRegionSpecLow.

```
