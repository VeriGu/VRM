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
Require Import MemRegion.Spec.
Require Import MemRegion.Layer.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section PageIndexSpec.

  Fixpoint region_search_loop (n: nat) (addr: Z) (i: Z) (res: Z) (regs: ZMap.t Memblock) :=
    match n with
    | O => Some (i, res)
    | S n' =>
      match region_search_loop n' addr i res regs with
      | Some (i', res') =>
        rely is_memblock i'; rely is_int res';
        let region := i' @ regs in
        let base := mb_base region in
        let size := mb_size region in
        rely is_addr base; rely is_int64 size; rely is_addr (base + size);
        if (base <=? addr) && (addr <? base + size) then
          Some (i'+1, i')
        else
          Some (i'+1, res')
      | _ => None
      end
    end.

  Definition get_s2_page_index_spec (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      rely is_addr addr; rely is_memblock (region_cnt adt);
      match region_search_loop (Z.to_nat (region_cnt adt)) addr 0 INVALID (regions adt) with
      | Some (i', region_index) =>
        rely is_memblock i'; rely is_int region_index;
        if region_index =? INVALID then
          Some (VZ64 INVALID64)
        else
          rely is_memblock region_index;
          let region := region_index @ (regions adt) in
          let base := mb_base region in
          let page_index := mb_index region in
          rely is_addr base; rely is_int64 page_index;
          if page_index =? INVALID64 then Some (VZ64 INVALID64)
          else rely is_addr page_index;
                       rely (addr >=? base);
                           Some (VZ64 (page_index + (addr - base) / PAGE_SIZE))
      | _ => None
      end
    end.

End PageIndexSpec.

Section PageIndexSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MemRegion_ops) LDATA).

  Definition get_s2_page_index_spec0 (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      rely is_addr addr;
      when region_index == mem_region_search_spec (VZ64 addr) adt;
      rely is_int region_index;
      if (region_index =? INVALID) then Some (VZ64 INVALID64) else
                rely is_memblock region_index;
      when' page_index == get_mem_region_index_spec region_index adt;
      rely is_int64 page_index;
      if page_index =? INVALID64 then
        Some (VZ64 INVALID64)
      else
        rely is_addr page_index;
        when' base == get_mem_region_base_spec region_index adt;
        rely is_addr base; rely (addr >=? base);
        Some (VZ64 (page_index + (addr - base) / PAGE_SIZE))
    end.

  Inductive get_s2_page_index_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_s2_page_index_spec_low_intro s (WB: _ -> Prop) m'0 labd addr res
      (Hinv: high_level_invariant labd)
      (Hspec: get_s2_page_index_spec0 (VZ64 (Int64.unsigned addr)) labd = Some (VZ64 (Int64.unsigned res))):
      get_s2_page_index_spec_low_step s WB ((Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_s2_page_index_spec_low: compatsem LDATAOps :=
      csem get_s2_page_index_spec_low_step (type_of_list_type (Tint64::nil)) Tint64.

  End WITHMEM.

End PageIndexSpecLow.

```
