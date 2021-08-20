# VMPowerSpec

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
Require Import MemoryOps.Layer.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section VMPowerSpec.

  Definition set_vm_poweroff_spec (vmid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid;
    if halt adt then Some adt else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        let info' := info {vm_state: POWEROFF} in
        let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info')) ::
                          TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                          (orac cpu l0) ++ l0 in
        Some adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info'}}
             {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse}
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition get_vm_poweron_spec (vmid: Z) (adt: RData) : option (RData * Z) :=
    rely is_vmid vmid;
    if halt adt then Some (adt, 0) else
    let id := INFO_ID + vmid in
    let cpu := curid adt in
    match id @ (lock adt), id @ (oracle adt), id @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let info := CalVMInfo (vmid @ (vminfos (shared adt))) (orac cpu l0) in
        rely is_int (vm_state (VS info));
        let ret := (if vm_state (VS info) =? POWEROFF then 0 else 1) in
        let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OVMINFO info)) ::
                          TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                          (orac cpu l0) ++ l0 in
        Some (adt {tstate: 1} {shared: (shared adt) {vminfos: (vminfos (shared adt)) # vmid == info}}
                  {log: (log adt) # id == l'} {lock: (lock adt) # id == LockFalse},
              ret)
      | _ => None
      end
    | _, _, _ => None
    end.

End VMPowerSpec.

Section VMPowerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := MemoryOps_ops) LDATA).

  Definition set_vm_poweroff_spec0 (vmid: Z) (adt: RData) : option RData :=
    rely is_vmid vmid;
    when adt1 == acquire_lock_vm_spec vmid adt;
    when adt2 == set_vm_state_spec vmid POWEROFF adt1;
    release_lock_vm_spec vmid adt2.

  Definition get_vm_poweron_spec0 (vmid: Z) (adt: RData) : option (RData * Z) :=
    rely is_vmid vmid;
    when adt1 == acquire_lock_vm_spec vmid adt;
    when state == get_vm_state_spec vmid adt1;
    rely is_int state;
    if state =? POWEROFF then
      let ret := 0 in
      when adt2 == release_lock_vm_spec vmid adt1;
      when res == check_spec ret adt2;
      Some (adt2, res)
    else
      let ret := 1 in
      when adt2 == release_lock_vm_spec vmid adt1;
      when res == check_spec ret adt2;
      Some (adt2, res).

  Inductive set_vm_poweroff_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_vm_poweroff_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid
      (Hinv: high_level_invariant labd)
      (Hspec: set_vm_poweroff_spec0 (Int.unsigned vmid) labd = Some labd'):
      set_vm_poweroff_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive get_vm_poweron_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_vm_poweron_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' vmid res
      (Hinv: high_level_invariant labd)
      (Hspec: get_vm_poweron_spec0 (Int.unsigned vmid) labd = Some (labd', (Int.unsigned res))):
      get_vm_poweron_spec_low_step s WB ((Vint vmid)::nil) (m'0, labd) (Vint res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition set_vm_poweroff_spec_low: compatsem LDATAOps :=
      csem set_vm_poweroff_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition get_vm_poweron_spec_low: compatsem LDATAOps :=
      csem get_vm_poweron_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

  End WITHMEM.

End VMPowerSpecLow.

```
