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

Require Import NPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import MemoryOps.Spec.
Require Import BootCore.Layer.
Require Import MemManager.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section BootAuxSpec.

  Fixpoint unmap_and_load_loop (n: nat) (vmid: Z) (start: Z) (target: Z) (remap: Z) (adt: RData) :=
    match n with
    | O => Some (start, target, remap, adt)
    | S n' =>
      match unmap_and_load_loop n' vmid start target remap adt with
      | Some (start', target', remap', adt') =>
        rely is_addr start'; rely is_addr target'; rely is_addr remap';
        rely (start' + PMD_SIZE >=? target');
        when' pte, adt1 == walk_s2pt_spec COREVISOR (VZ64 remap') adt';
        rely is_int64 pte;
        let pfn := phys_page pte / PMD_SIZE * PTRS_PER_PMD in
        let gfn := start' / PAGE_SIZE in
        if pfn =? 0 then
          when adt2 == panic_spec adt1;
          Some (start' + PMD_SIZE, start' + PMD_SIZE, remap' + (start' + PMD_SIZE - target'), adt2)
        else
          when adt2 == prot_and_map_vm_s2pt_spec vmid (VZ64 (gfn * PAGE_SIZE)) (VZ64 (pfn * PAGE_SIZE)) 2 adt1;
          Some (start' + PMD_SIZE, start' + PMD_SIZE, remap' + (start' + PMD_SIZE - target'), adt2)
      | _ => None
      end
    end.

  Definition unmap_and_load_vm_image_spec (vmid: Z) (target_addr: Z64) (remap_addr: Z64) (num: Z64) (adt: RData) : option RData :=
    match target_addr, remap_addr, num with
    | VZ64 target_addr, VZ64 remap_addr, VZ64 num =>
      rely is_addr target_addr; rely is_addr remap_addr; rely is_gfn num; rely is_vm vmid;
      let start := target_addr / PMD_SIZE * PMD_SIZE in
      let end' := target_addr + num * PAGE_SIZE in
      rely (end' >=? start);
      let num := (end' - start + 2097151) / PMD_SIZE in
      rely is_int64 num;
      match unmap_and_load_loop (Z.to_nat num) vmid start target_addr remap_addr adt with
      | Some (start', target', remap', adt') =>
        rely is_int64 start'; rely is_int64 target'; rely is_int64 remap';
        Some adt'
      | _ => None
      end
    end.

End BootAuxSpec.

Section BootAuxSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := BootCore_ops) LDATA).

  Inductive unmap_and_load_vm_image_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | unmap_and_load_vm_image_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid target_addr remap_addr num
      (Hinv: high_level_invariant labd)
      (Hspec: unmap_and_load_vm_image_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned target_addr)) (VZ64 (Int64.unsigned remap_addr)) (VZ64 (Int64.unsigned num)) labd = Some labd'):
      unmap_and_load_vm_image_spec_low_step s WB ((Vint vmid)::(Vlong target_addr)::(Vlong remap_addr)::(Vlong num)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition unmap_and_load_vm_image_spec_low: compatsem LDATAOps :=
      csem unmap_and_load_vm_image_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End BootAuxSpecLow.

```
