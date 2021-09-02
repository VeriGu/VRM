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
Require Import Locks.Spec.
Require Import VMPower.Layer.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section BootCoreSpec.

  Definition gen_vmid_spec (adt: RData) : option (RData * Z) :=
    if halt adt then Some (adt, 0) else
    let cpu := curid adt in
    match CORE_ID @ (lock adt), CORE_ID @ (oracle adt), CORE_ID @ (log adt) with
    | LockFalse, orac, l0 =>
      match H_CalLock ((orac cpu l0) ++ l0) with
      | Some (_, LEMPTY, None) =>
        let core := CalCoreData (core_data (shared adt)) (orac cpu l0) in
        let vmid := next_vmid core in
        rely is_vmid vmid;
        if vmid <? COREVISOR then
          let core' := core {next_vmid: vmid + 1} in
          let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OCORE_DATA core')) ::
                            TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                            (orac cpu l0) ++ l0 in
          Some (adt {tstate: 1} {shared: (shared adt) {core_data: core'}}
                    {log: (log adt) # CORE_ID == l'} {lock: (lock adt) # CORE_ID == LockFalse},
                vmid)
        else
          let l' := TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l0) ++ l0 in
          Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {core_data: core}}
                    {log: (log adt) # CORE_ID == l'} {lock: (lock adt) # CORE_ID == (LockOwn true)},
                0)
      | _ => None
      end
    | _, _, _ => None
    end.

  Definition alloc_remap_addr_spec (pgnum: Z64) (adt: RData) : option (RData * Z64) :=
    match pgnum with
    | VZ64 pgnum =>
      rely is_gfn pgnum;
      if halt adt then Some (adt, (VZ64 0)) else
      let cpu := curid adt in
      match CORE_ID @ (lock adt), CORE_ID @ (oracle adt), CORE_ID @ (log adt) with
      | LockFalse, orac, l0 =>
        match H_CalLock ((orac cpu l0) ++ l0) with
        | Some (_, LEMPTY, None) =>
          let core := CalCoreData (core_data (shared adt)) (orac cpu l0) in
          let remap := next_remap_ptr core in
          rely is_addr remap;
          if remap + pgnum * PAGE_SIZE <? REMAP_END then
            let core' := core {next_remap_ptr: remap + pgnum * PAGE_SIZE} in
            let l' :=  TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OCORE_DATA core')) ::
                              TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) ::
                              (orac cpu l0) ++ l0 in
            Some (adt {tstate: 1} {shared: (shared adt) {core_data: core'}}
                      {log: (log adt) # CORE_ID == l'} {lock: (lock adt) # CORE_ID == LockFalse},
                  (VZ64 remap))
          else
            let l' := TEVENT cpu (TSHARED (OPULL CORE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l0) ++ l0 in
            Some (adt {halt: true} {tstate: 0} {shared: (shared adt) {core_data: core}}
                      {log: (log adt) # CORE_ID == l'} {lock: (lock adt) # CORE_ID == (LockOwn true)},
                  (VZ64 0))
        | _ => None
        end
      | _, _, _ => None
      end
    end.

End BootCoreSpec.

Section BootCoreSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := VMPower_ops) LDATA).

  Definition gen_vmid_spec0  (adt: RData) : option (RData * Z) :=
    when adt' == acquire_lock_core_spec adt;
    when vmid == get_next_vmid_spec adt';
    rely is_vmid vmid;
    if vmid <? COREVISOR then
      when adt2 == set_next_vmid_spec (vmid + 1) adt';
      when adt3 == release_lock_core_spec adt2;
      when res == check_spec vmid adt3;
      Some (adt3, res)
    else
      when adt2 == panic_spec adt';
      when adt3 == release_lock_core_spec adt2;
      when res == check_spec vmid adt3;
      Some (adt3, res).

  Definition alloc_remap_addr_spec0 (pgnum: Z64) (adt: RData) : option (RData * Z64) :=
    match pgnum with
    | VZ64 pgnum =>
      when adt' == acquire_lock_core_spec adt;
      when' remap == get_next_remap_ptr_spec adt';
      rely is_addr remap; rely is_gfn pgnum;
      if remap + pgnum * PAGE_SIZE <? REMAP_END then
        when adt2 == set_next_remap_ptr_spec (VZ64 (remap + pgnum * PAGE_SIZE)) adt';
        when adt3 == release_lock_core_spec adt2;
        when' res == check64_spec (VZ64 remap) adt3;
        Some (adt3, VZ64 res)
      else
        when adt2 == panic_spec adt';
        when adt3 == release_lock_core_spec adt2;
        when' res == check64_spec (VZ64 remap) adt3;
        Some (adt3, VZ64 res)
    end.

  Inductive gen_vmid_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | gen_vmid_spec_low_intro s (WB: _ -> Prop) m'0 labd labd'  res
      (Hinv: high_level_invariant labd)
      (Hspec: gen_vmid_spec0 labd = Some (labd', (Int.unsigned res))):
      gen_vmid_spec_low_step s WB nil (m'0, labd) (Vint res) (m'0, labd').

  Inductive alloc_remap_addr_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | alloc_remap_addr_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pgnum res
      (Hinv: high_level_invariant labd)
      (Hspec: alloc_remap_addr_spec0 (VZ64 (Int64.unsigned pgnum)) labd = Some (labd', (VZ64 (Int64.unsigned res)))):
      alloc_remap_addr_spec_low_step s WB ((Vlong pgnum)::nil) (m'0, labd) (Vlong res) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition gen_vmid_spec_low: compatsem LDATAOps :=
      csem gen_vmid_spec_low_step (type_of_list_type nil) Tint32.

    Definition alloc_remap_addr_spec_low: compatsem LDATAOps :=
      csem alloc_remap_addr_spec_low_step (type_of_list_type (Tint64::nil)) Tint64.

  End WITHMEM.

End BootCoreSpecLow.

```
