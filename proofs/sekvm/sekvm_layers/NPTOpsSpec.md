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

Require Import NPTWalk.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import NPTWalk.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import RData.

Local Open Scope Z_scope.

Section NPTOpsSpec.

  Definition get_level_s2pt_spec (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z) :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some (adt, 0) else
      let id := NPT_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let npt0 := vmid @ (npts (shared adt)) in
        let npt := CalNPT npt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: orac cpu l ++ l in
        let gfn := addr / PAGE_SIZE in
        match gfn @ (pt npt) with
        | (_, level, pte) =>
          rely is_int level;
          let res := (if phys_page pte =? 0 then 0 else level) in
          let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt)) :: l' in
          let adt' := adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt}}
                          {log: (log adt) # id == l''} {lock: (lock adt) # id == LockFalse}
          in
          match H_CalLock l'' with
          | Some _ => Some (adt', res)
          | _ => None
          end
        end
      | _ => None
      end
    end.

  Definition walk_s2pt_spec (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_vmid vmid; rely is_addr addr;
      if halt adt then Some (adt, (VZ64 0)) else
      let id := NPT_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let npt0 := vmid @ (npts (shared adt)) in
        let npt := CalNPT npt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: orac cpu l ++ l in
        let gfn := addr / PAGE_SIZE in
        match gfn @ (pt npt) with
        | (_, level, pte) =>
          rely is_int64 pte;
          let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt)) :: l' in
          let adt' := adt {tstate: 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt}}
                          {log: (log adt) # id == l''} {lock: (lock adt) # id == LockFalse}
          in
          match H_CalLock l'' with
          | Some _ => Some (adt', VZ64 pte)
          | _ => None
          end
        end
      | _ => None
      end
    end.

  Definition map_s2pt_spec (vmid: Z) (addr: Z64) (level: Z) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      let id := NPT_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let npt0 := vmid @ (npts (shared adt)) in
        let npt := CalNPT npt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: orac cpu l ++ l in
        if (level =? 2) || (level =? 3) then
          if pte =? 0 then None
          else
            match local_mmap vmid addr level pte npt with
            | Some (halt', npt') =>
              let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: l' in
              let adt' := adt {halt: halt'} {tstate: if halt' then 0 else 1} {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
                              {log: (log adt) # id == if halt' then l' else l''}
                              {lock: (lock adt) # id == if halt' then LockOwn true else LockFalse}
              in
              match H_CalLock l'' with
              | Some _ => Some adt'
              | _ => None
              end
            | _ => None
            end
        else None
      | _ => None
      end
    end.

  Definition clear_pfn_host_spec (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_pfn pfn;
      if halt adt then Some adt else
      let id := NPT_ID + HOSTVISOR in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let npt0 := HOSTVISOR @ (npts (shared adt)) in
        let npt := CalNPT npt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: orac cpu l ++ l in
        match pfn @ (pt npt) with
        | (_, level, pte) =>
          rely is_int level;
          match (
              if (if phys_page pte =? 0 then 0 else level) =? 0
              then Some (false, npt)
              else local_mmap HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
          | Some (halt', npt') =>
            let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: l' in
            let adt' := adt {halt: halt'} {tstate: if halt' then 0 else 1} {shared: (shared adt) {npts: (npts (shared adt)) # HOSTVISOR == npt'}}
                            {log: (log adt) # id == if halt' then l' else l''}
                            {lock: (lock adt) # id == if halt' then LockOwn true else LockFalse}
            in
            match H_CalLock l'' with
            | Some _ => Some adt'
            | _ => None
            end
          | _ => None
          end
        end
      | _ => None
      end
    end.

End NPTOpsSpec.

Section NPTOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := NPTWalk_ops) LDATA).

  Definition get_level_s2pt_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z) :=
    when adt1 == acquire_lock_pt_spec vmid adt;
    when ret == get_npt_level_spec vmid addr adt1;
    rely is_int ret;
    when adt2 == release_lock_pt_spec vmid adt1;
    when res == check_spec ret adt2;
    Some (adt2, res).

  Definition walk_s2pt_spec0 (vmid: Z) (addr: Z64) (adt: RData) : option (RData * Z64) :=
    when adt1 == acquire_lock_pt_spec vmid adt;
    when' ret == walk_npt_spec vmid addr adt1;
    rely is_int64 ret;
    when adt2 == release_lock_pt_spec vmid adt1;
    when' res == check64_spec (VZ64 ret) adt2;
    Some (adt2, VZ64 res).

  Definition map_s2pt_spec0 (vmid: Z) (addr: Z64) (level: Z) (pte: Z64) (adt: RData) : option RData :=
    when adt1 == acquire_lock_pt_spec vmid adt;
    when adt2 == set_npt_spec vmid addr level pte adt1;
    when adt3 == release_lock_pt_spec vmid adt2;
    Some adt3.

  Definition clear_pfn_host_spec0 (pfn: Z64) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_pfn pfn;
      when adt1 == acquire_lock_pt_spec HOSTVISOR adt;
      when level == get_npt_level_spec HOSTVISOR (VZ64 (pfn * PAGE_SIZE)) adt1;
      rely is_int level;
      if level =? 0 then
        release_lock_pt_spec HOSTVISOR adt1
      else
        when adt2 == set_npt_spec HOSTVISOR (VZ64 (pfn * PAGE_SIZE)) 3 (VZ64 PAGE_GUEST) adt1;
        release_lock_pt_spec HOSTVISOR adt2
    end.

  Inductive get_level_s2pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_level_s2pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr res
      (Hinv: high_level_invariant labd)
      (Hspec: get_level_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) labd = Some (labd', (Int.unsigned res))):
      get_level_s2pt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Inductive walk_s2pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | walk_s2pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr res
      (Hinv: high_level_invariant labd)
      (Hspec: walk_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      walk_s2pt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Inductive map_s2pt_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | map_s2pt_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid addr level pte
      (Hinv: high_level_invariant labd)
      (Hspec: map_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (Int.unsigned level) (VZ64 (Int64.unsigned pte)) labd = Some labd'):
      map_s2pt_spec_low_step s WB ((Vint vmid)::(Vlong addr)::(Vint level)::(Vlong pte)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive clear_pfn_host_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | clear_pfn_host_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pfn
      (Hinv: high_level_invariant labd)
      (Hspec: clear_pfn_host_spec0 (VZ64 (Int64.unsigned pfn)) labd = Some labd'):
      clear_pfn_host_spec_low_step s WB ((Vlong pfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_level_s2pt_spec_low: compatsem LDATAOps :=
      csem get_level_s2pt_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tint32.

    Definition walk_s2pt_spec_low: compatsem LDATAOps :=
      csem walk_s2pt_spec_low_step (type_of_list_type (Tint32::Tint64::nil)) Tint64.

    Definition map_s2pt_spec_low: compatsem LDATAOps :=
      csem map_s2pt_spec_low_step (type_of_list_type (Tint32::Tint64::Tint32::Tint64::nil)) Tvoid.

    Definition clear_pfn_host_spec_low: compatsem LDATAOps :=
      csem clear_pfn_host_spec_low_step (type_of_list_type (Tint64::nil)) Tvoid.

  End WITHMEM.

End NPTOpsSpecLow.

```
