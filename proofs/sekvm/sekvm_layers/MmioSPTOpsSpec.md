# MmioSPTOpsSpec

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
Require Import MmioSPTWalk.Layer.
Require Import MmioSPTWalk.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section MmioSPTOpsSpec.

  Definition init_spt_spec (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    rely is_smmu index; rely is_smmu_cfg cbndx;
    if halt adt then Some adt else
    let id := SPT_ID in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let spt0 := spts (shared adt) in
      let spt := CalSPT spt0 (orac cpu l) in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((orac cpu l) ++ l) in
      let ttbr := SMMU_TTBR index cbndx in
      let spt' := spt {spt_pt: (spt_pt spt) # ttbr == (ZMap.init (0, 0))}
                      {spt_pgd_t: (spt_pgd_t spt) # ttbr == (ZMap.init false)}
                      {spt_pmd_t: (spt_pmd_t spt) # ttbr == (ZMap.init (ZMap.init false))} in

      let l'' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt'))) :: l' in
      let adt' := adt {tstate: 1} {shared: (shared adt) {spts: spt'}} {log: (log adt) # id == l''} {lock: (lock adt) # id == LockFalse} in
      match H_CalLock l'' with
      | Some _ => Some adt'
      | _ => None
      end
    | _ => None
    end.

  Definition walk_spt_spec (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr addr;
      if halt adt then Some (adt, (VZ64 0)) else
      let id := SPT_ID in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let spt0 := spts (shared adt) in
        let spt := CalSPT spt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((orac cpu l) ++ l) in
        let ttbr := SMMU_TTBR index cbndx in
        let pt := ttbr @ (spt_pt spt) in
        let gfn := addr / PAGE_SIZE in
        match ZMap.get gfn pt with
        | (pfn, pte) =>
          rely is_int64 pte;
          let l'' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt))) :: l' in
          let adt' := adt {tstate: 1} {shared: (shared adt) {spts: spt}} {log: (log adt) # id == l''} {lock: (lock adt) # id == LockFalse} in
          match H_CalLock l'' with
          | Some _ => Some (adt', (VZ64 pte))
          | _ => None
          end
        end
      | _ => None
      end
    end.

  Definition map_spt_spec (cbndx: Z) (index: Z) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      let id := SPT_ID in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let spt0 := spts (shared adt) in
        let spt := CalSPT spt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((orac cpu l) ++ l) in
        match local_spt_map cbndx index addr pte spt with
        | Some (halt', spt') =>
          let l'' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt'))) :: l' in
          let adt' := adt {halt: halt'} {tstate: if halt' then 0 else 1}
                          {shared: (shared adt) {spts: spt'}}
                          {log: (log adt) # id == (if halt' then l' else l'')}
                          {lock: (lock adt) # id == (if halt' then LockOwn true else LockFalse)} in
          match H_CalLock l'' with
          | Some _ => Some adt'
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    end.

  Definition unmap_spt_spec (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_smmu index; rely is_smmu_cfg cbndx; rely is_smmu_addr addr;
      if halt adt then Some (adt, (VZ64 0)) else
      let id := SPT_ID in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let spt0 := spts (shared adt) in
        let spt := CalSPT spt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: ((orac cpu l) ++ l) in
        let ttbr := SMMU_TTBR index cbndx in
        let pt := ttbr @ (spt_pt spt) in
        let gfn := addr / PAGE_SIZE in
        match ZMap.get gfn pt with
        | (pfn, pte) =>
          rely is_int64 pte;
          match (if pte =? 0 then Some (false, spt) else local_spt_map cbndx index addr 0 spt) with
          | Some (halt', spt') =>
            let l'' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt'))) :: l' in
            let adt' := adt {halt: halt'} {tstate: if halt' then 0 else 1}
                            {shared: (shared adt) {spts: spt'}}
                            {log: (log adt) # id == (if halt' then l' else l'')}
                            {lock: (lock adt) # id == (if halt' then LockOwn true else LockFalse)} in
            match H_CalLock l'' with
            | Some _ => Some (adt', (VZ64 (if halt' then 0 else pte)))
            | _ => None
            end
          | _ => None
          end
        end
      | _ => None
      end
    end.

End MmioSPTOpsSpec.

Section MmioSPTOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MmioSPTWalk_ops) LDATA).

  Definition init_spt_spec0 (cbndx: Z) (index: Z) (adt: RData) : option RData :=
    when adt1 == acquire_lock_spt_spec adt;
    when adt2 == clear_smmu_pt_spec cbndx index adt1;
    release_lock_spt_spec adt2.

  Definition walk_spt_spec0 (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    when adt1 == acquire_lock_spt_spec adt;
    when' ret == walk_smmu_pt_spec cbndx index addr adt1;
    rely is_int64 ret;
    when adt2 == release_lock_spt_spec adt1;
    when' res == check64_spec (VZ64 ret) adt2;
    Some (adt2, VZ64 res).

  Definition map_spt_spec0 (cbndx: Z) (index: Z) (addr: Z64) (pte: Z64) (adt: RData) : option RData :=
    when adt1 == acquire_lock_spt_spec adt;
    when adt2 == set_smmu_pt_spec cbndx index addr pte adt1;
    release_lock_spt_spec adt2.

  Definition unmap_spt_spec0 (cbndx: Z) (index: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    when adt1 == acquire_lock_spt_spec adt;
    when' res == walk_smmu_pt_spec cbndx index addr adt1;
    rely is_int64 res;
    if res =? 0 then
      when adt2 == release_lock_spt_spec adt1;
      when' ret == check64_spec (VZ64 res) adt2;
      Some (adt2, VZ64 ret)
    else
      when adt2 == set_smmu_pt_spec cbndx index addr (VZ64 0) adt1;
      when adt3 == release_lock_spt_spec adt2;
      when' ret == check64_spec (VZ64 res) adt3;
      Some (adt3, VZ64 ret).

  Inductive init_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | init_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index
      (Hinv: high_level_invariant labd)
      (Hspec: init_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) labd = Some labd'):
      init_spt_spec_low_step s WB ((Vint cbndx)::(Vint index)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive walk_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_spt_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive map_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index addr pte
      (Hinv: high_level_invariant labd)
      (Hspec: map_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      map_spt_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong addr)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive unmap_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | unmap_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' cbndx index addr res
      (Hinv: high_level_invariant labd)
      (Hspec: unmap_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      unmap_spt_spec_low_step s WB ((Vint cbndx)::(Vint index)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition init_spt_spec_low: compatsem LDATAOps :=
      csem init_spt_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition walk_spt_spec_low: compatsem LDATAOps :=
      csem walk_spt_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::nil)) Tint64.

    Definition map_spt_spec_low: compatsem LDATAOps :=
      csem map_spt_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::Tint64::nil)) Tvoid.

    Definition unmap_spt_spec_low: compatsem LDATAOps :=
      csem unmap_spt_spec_low_step (type_of_list_type (Tint32::Tint32::Tint64::nil)) Tint64.

  End WITHMEM.

End MmioSPTOpsSpecLow.

```
