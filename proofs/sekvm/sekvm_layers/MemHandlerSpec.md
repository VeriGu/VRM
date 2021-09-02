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
Require Import CtxtSwitch.Layer.
Require Import MemoryOps.Spec.
Require Import MmioOps.Spec.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MemHandlerSpec.

  Definition clear_vm_stage2_range_spec (vmid: Z) (start: Z64) (size: Z64) (adt: RData) : option RData :=
    match start, size with
    | VZ64 start, VZ64 size =>
      rely is_addr start; rely is_addr size;
      when power, adt' == get_vm_poweron_spec vmid adt;
      rely is_int power;
      if power =? 0 then
        clear_vm_range_spec vmid (VZ64 (start / PAGE_SIZE)) (VZ64 (size / PAGE_SIZE)) adt'
      else
        Some adt'
    end.

  Definition el2_arm_lpae_map_spec (iova: Z64) (paddr: Z64) (prot: Z64) (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    match iova, paddr, prot  with
    | VZ64 iova, VZ64 paddr, VZ64 prot =>
      rely is_smmu_addr iova; rely is_paddr paddr; rely (prot <? 9223372036854775807); rely (phys_page prot =? 0);
      let pfn := paddr / PAGE_SIZE in
      let gfn := iova / PAGE_SIZE in
      when' pte == smmu_init_pte_spec (VZ64 prot) (VZ64 paddr) adt;
      rely is_int64 pte;
      when adt' == smmu_assign_page_spec cbndx index (VZ64 pfn) (VZ64 gfn) adt;
      smmu_map_page_spec cbndx index (VZ64 iova) (VZ64 pte) adt'
    end.

  Fixpoint kvm_phys_addr_ioremap_loop (n: nat) vmid gpa pa adt :=
    match n with
    | O => Some (gpa, pa, adt)
    | S n' =>
      match kvm_phys_addr_ioremap_loop n' vmid gpa pa adt with
      | Some (gpa', pa', adt') =>
        rely is_addr gpa'; rely is_paddr pa';
        when adt'' == map_io_spec vmid (VZ64 gpa') (VZ64 pa') adt';
        Some (gpa' + PAGE_SIZE, pa' + PAGE_SIZE, adt'')
      | _ => None
      end
    end.

  Definition kvm_phys_addr_ioremap_spec (vmid: Z) (gpa: Z64) (pa: Z64) (size: Z64) (adt: RData) : option RData :=
    match gpa, pa, size with
    | VZ64 gpa, VZ64 pa, VZ64 size =>
      let num := (size + 4095) / PAGE_SIZE in
      rely is_addr gpa; rely is_paddr pa; rely is_addr size; rely is_addr (gpa + num); rely is_addr (pa + num);
      match kvm_phys_addr_ioremap_loop (Z.to_nat num) vmid gpa pa adt with
      | Some (gpa', pa', adt') =>
        rely is_int64 gpa'; rely is_int64 pa';
        Some adt'
      | _ => None
      end
    end.

End MemHandlerSpec.

Section MemHandlerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := CtxtSwitch_ops) LDATA).

  Inductive clear_vm_stage2_range_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_vm_stage2_range_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid start size
      (Hinv: high_level_invariant labd)
      (Hspec: clear_vm_stage2_range_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned start)) (VZ64 (Int64.unsigned size)) labd = Some labd'):
      clear_vm_stage2_range_spec_low_step s WB ((Vint vmid)::(Vlong start)::(Vlong size)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive el2_arm_lpae_map_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | el2_arm_lpae_map_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' iova paddr prot cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: el2_arm_lpae_map_spec (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned paddr)) (VZ64 (Int64.unsigned prot)) (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      el2_arm_lpae_map_spec_low_step s WB ((Vlong iova)::(Vlong paddr)::(Vlong prot)::(Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive kvm_phys_addr_ioremap_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | kvm_phys_addr_ioremap_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid gpa pa size
      (Hinv: high_level_invariant labd)
      (Hspec: kvm_phys_addr_ioremap_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned gpa)) (VZ64 (Int64.unsigned pa)) (VZ64 (Int64.unsigned size)) labd = Some labd'):
      kvm_phys_addr_ioremap_spec_low_step s WB ((Vint vmid)::(Vlong gpa)::(Vlong pa)::(Vlong size)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition clear_vm_stage2_range_spec_low: compatsem LDATAOps :=
      csem clear_vm_stage2_range_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition el2_arm_lpae_map_spec_low: compatsem LDATAOps :=
      csem el2_arm_lpae_map_spec_low_step (type_of_list_type (Tint64::Tint64::Tint64::Tint32::Tint32::nil)) Tvoid.

    Definition kvm_phys_addr_ioremap_spec_low: compatsem LDATAOps :=
      csem kvm_phys_addr_ioremap_spec_low_step (type_of_list_type (Tint32::Tint64::Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End MemHandlerSpecLow.

```
