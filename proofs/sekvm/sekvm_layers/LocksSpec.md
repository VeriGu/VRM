# LocksSpec

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

Require Import RData.
Require Import CalLock.
Require Import Constants.
Require Import HypsecCommLib.
Require Import LockOpsH.Spec.
Require Import LockOpsH.Layer.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.

Section LocksSpec.

  Definition acquire_lock_pt_spec (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let npt := vmid @ (npts (shared adt)) in
      let npt' := CalNPT npt (orac cpu l) in
      let shared' := (shared adt) {npts: (npts (shared adt)) # vmid == npt'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition acquire_lock_spt_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := SPT_ID in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let spt := spts (shared adt) in
      let spt' := CalSPT spt (orac cpu l) in
      let shared' := (shared adt) {spts: spt'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition acquire_lock_s2page_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := S2PAGE_ID in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let s2p := s2page (shared adt) in
      let s2p' := CalS2Page s2p (orac cpu l) in
      let shared' := (shared adt) {s2page: s2p'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition acquire_lock_core_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := CORE_ID in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let core := core_data (shared adt) in
      let core' := CalCoreData core (orac cpu l) in
      let shared' := (shared adt) {core_data: core'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition acquire_lock_vm_spec (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let info := vmid @ (vminfos (shared adt)) in
      let info' := CalVMInfo info (orac cpu l) in
      let shared' := (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition acquire_lock_smmu_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := SMMU_ID in
    let cpu := curid adt in
    match id @ (lock adt) with
    | LockFalse =>
      let l := id @ (log adt) in
      let orac := id @ (oracle adt) in
      let l0 := orac cpu l in
      let smmu := smmu_vmid (shared adt) in
      let smmu' := CalSMMU smmu (orac cpu l) in
      let shared' := (shared adt) {smmu_vmid: smmu'} in
      let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK 10%nat)) :: ((orac cpu l) ++ l) in
      match H_CalLock l' with
      | Some _ =>
        Some adt {tstate: 0} {shared: shared'} {log: (log adt) # id == l'} {lock: (lock adt) # id == (LockOwn true)}
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_pt_spec (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := NPT_ID + vmid in
    let cpu := curid adt in
    let npt := vmid @ (npts (shared adt)) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (ONPT npt))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_spt_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := SPT_ID in
    let cpu := curid adt in
    let spt := spts (shared adt) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSPT spt))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_s2page_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := S2PAGE_ID in
    let cpu := curid adt in
    let s2p := s2page (shared adt) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OS2_PAGE s2p))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_core_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := CORE_ID in
    let cpu := curid adt in
    let core := core_data (shared adt) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OCORE_DATA core))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_vm_spec (vmid: Z) (adt: RData) : option RData :=
    if halt adt then Some adt else
    rely is_vmid vmid;
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    let info := vmid @ (vminfos (shared adt)) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OVMINFO info))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

  Definition release_lock_smmu_spec (adt: RData): option RData :=
    if halt adt then Some adt else
    let id := SMMU_ID in
    let cpu := curid adt in
    let smmu := smmu_vmid (shared adt) in
    match ZMap.get id (lock adt) with
    | LockOwn true =>
      let l := id @ (log adt) in
      let l' := (TEVENT cpu (TTICKET REL_LOCK)) :: (TEVENT cpu (TSHARED (OSMMU smmu))) :: l in
      match H_CalLock l' with
      | Some _ => Some (adt {tstate: 1} {log: (log adt) # id == l'} {lock: ZMap.set id LockFalse (lock adt)})
      | _ => None
      end
    | _ => None
    end.

End LocksSpec.

Section LocksSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := LockOpsH_ops) LDATA).

  Definition acquire_lock_spec0 (lk: Z) (adt: RData): option RData :=
    match wait_hlock_spec lk adt with
    | Some adt' => acquire_shared_spec lk adt'
    | _ => None
    end.

  Definition release_lock_spec0 (e: SharedMemEvent) (lk: Z) (adt: RData): option RData :=
    match release_shared_spec e lk adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition acquire_lock_pt_spec0 (vmid: Z) (adt: RData) : option RData :=
    acquire_lock_spec0 (lock_idx_pt vmid) adt.

  Definition acquire_lock_spt_spec0  (adt: RData) : option RData :=
    acquire_lock_spec0 lock_idx_spt adt.

  Definition acquire_lock_s2page_spec0  (adt: RData) : option RData :=
    acquire_lock_spec0 lock_idx_s2page adt.

  Definition acquire_lock_core_spec0  (adt: RData) : option RData :=
    acquire_lock_spec0 lock_idx_core adt.

  Definition acquire_lock_vm_spec0 (vmid: Z) (adt: RData) : option RData :=
    acquire_lock_spec0 (lock_idx_vm vmid) adt.

  Definition acquire_lock_smmu_spec0  (adt: RData) : option RData :=
    acquire_lock_spec0 lock_idx_smmu adt.

  Definition release_lock_pt_spec0 (vmid: Z) (adt: RData) : option RData :=
    let lk := lock_idx_pt vmid in
    match release_shared_pt_spec vmid adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition release_lock_spt_spec0 (adt: RData) : option RData :=
    let lk := lock_idx_spt in
    match release_shared_spt_spec adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition release_lock_s2page_spec0 (adt: RData) : option RData :=
    let lk := lock_idx_s2page in
    match release_shared_s2page_spec adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition release_lock_core_spec0 (adt: RData) : option RData :=
    let lk := lock_idx_core in
    match release_shared_core_spec adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition release_lock_vm_spec0 (vmid: Z) (adt: RData) : option RData :=
    let lk := lock_idx_vm vmid in
    match release_shared_vm_spec vmid adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Definition release_lock_smmu_spec0 (adt: RData) : option RData :=
    let lk := lock_idx_smmu in
    match release_shared_smmu_spec adt with
    | Some adt' => pass_hlock_spec lk adt'
    | _ => None
    end.

  Inductive acquire_lock_pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_pt_spec0 (Int.unsigned vmid) labd = Some labd'):
      acquire_lock_pt_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive acquire_lock_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_spt_spec0  labd = Some labd'):
      acquire_lock_spt_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive acquire_lock_s2page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_s2page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_s2page_spec0  labd = Some labd'):
      acquire_lock_s2page_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive acquire_lock_core_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_core_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_core_spec0  labd = Some labd'):
      acquire_lock_core_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive acquire_lock_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_vm_spec0 (Int.unsigned vmid) labd = Some labd'):
      acquire_lock_vm_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive acquire_lock_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | acquire_lock_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: acquire_lock_smmu_spec0  labd = Some labd'):
      acquire_lock_smmu_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_pt_spec0 (Int.unsigned vmid) labd = Some labd'):
      release_lock_pt_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_spt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_spt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_spt_spec0  labd = Some labd'):
      release_lock_spt_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_s2page_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_s2page_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_s2page_spec0  labd = Some labd'):
      release_lock_s2page_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_core_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_core_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_core_spec0  labd = Some labd'):
      release_lock_core_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_vm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_vm_spec0 (Int.unsigned vmid) labd = Some labd'):
      release_lock_vm_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive release_lock_smmu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | release_lock_smmu_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' 
      (Hinv: high_level_invariant labd)
      (Hspec: release_lock_smmu_spec0  labd = Some labd'):
      release_lock_smmu_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition acquire_lock_pt_spec_low: compatsem LDATAOps :=
      csem acquire_lock_pt_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition acquire_lock_spt_spec_low: compatsem LDATAOps :=
      csem acquire_lock_spt_spec_low_step (type_of_list_type nil) Tvoid.

    Definition acquire_lock_s2page_spec_low: compatsem LDATAOps :=
      csem acquire_lock_s2page_spec_low_step (type_of_list_type nil) Tvoid.

    Definition acquire_lock_core_spec_low: compatsem LDATAOps :=
      csem acquire_lock_core_spec_low_step (type_of_list_type nil) Tvoid.

    Definition acquire_lock_vm_spec_low: compatsem LDATAOps :=
      csem acquire_lock_vm_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition acquire_lock_smmu_spec_low: compatsem LDATAOps :=
      csem acquire_lock_smmu_spec_low_step (type_of_list_type nil) Tvoid.

    Definition release_lock_pt_spec_low: compatsem LDATAOps :=
      csem release_lock_pt_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition release_lock_spt_spec_low: compatsem LDATAOps :=
      csem release_lock_spt_spec_low_step (type_of_list_type nil) Tvoid.

    Definition release_lock_s2page_spec_low: compatsem LDATAOps :=
      csem release_lock_s2page_spec_low_step (type_of_list_type nil) Tvoid.

    Definition release_lock_core_spec_low: compatsem LDATAOps :=
      csem release_lock_core_spec_low_step (type_of_list_type nil) Tvoid.

    Definition release_lock_vm_spec_low: compatsem LDATAOps :=
      csem release_lock_vm_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition release_lock_smmu_spec_low: compatsem LDATAOps :=
      csem release_lock_smmu_spec_low_step (type_of_list_type nil) Tvoid.

  End WITHMEM.

End LocksSpecLow.
```
