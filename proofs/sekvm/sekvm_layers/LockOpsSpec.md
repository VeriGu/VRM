# LockOpsSpec

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
Require Import AbstractMachine.Spec.
Require Import HypsecCommLib.
Require Import AbstractMachine.Layer.

Local Open Scope Z_scope.

Section LockOpsSpec.

  (* Ported from mcertikos/objects/ObjMultiprocessor.v *)
  Definition wait_lock_spec (lk: Z) (adt: RData): option RData :=
    (* if adt.(shared).(halt) then Some adt else *)
    match ZMap.get lk adt.(log) with
    | l =>
      let it := INC_TICKET (Z.to_nat lock_bound) in
      let to := ZMap.get lk adt.(oracle) in
      let l' := TEVENT adt.(curid) (TTICKET it) ::
                to adt.(curid) l ++ l in
      match CalTicketLock l' with
      | None            => None
      | Some (t, n, tq) =>
          if zle (n + TOTAL_CPU + 1) t then None else
          let wt := CalWaitTime tq in
          let tw := t - 1 in
          match CalTicketWait wt adt.(curid) tw l' to with
          | None     => None
          | Some l'' =>
              let hl := TEVENT adt.(curid) (TTICKET HOLD_LOCK) in
              Some adt {log: ZMap.set lk ((hl::l'')) adt.(log)}
          end
      end
    end.

  (* Ported from mcertikos/objects/ObjMultiprocessor.v *)
  Definition pass_lock_spec (lk: Z) (adt: RData): option RData :=
    (* if adt.(shared).(halt) then Some adt else *)
    match ZMap.get lk adt.(log) with
    | l => let l' := TEVENT adt.(curid) (TTICKET INC_NOW) :: l in
          Some adt {log: ZMap.set lk (l') adt.(log)}
    end.

End LockOpsSpec.

Section LockOpsSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := AbstractMachine_ops) LDATA).

  Definition wait_lock_spec_wraparound (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), bars adt with
    | l, BarrierValid =>
      let it := INC_TICKET (Z.to_nat lock_bound) in
      let to := ZMap.get lk adt.(oracle) in
      let l' := TEVENT adt.(curid) (TTICKET it) ::
                to adt.(curid) l ++ l in
      match CalTicketLockWraparound l' with
      | None            => None
      | Some (t, n, tq) =>
          let wt := CalWaitTime tq in
          let tw := Int.unsigned (Int.repr (t - 1)) in
          match CalTicketWaitWraparound wt adt.(curid) tw l' to with
          | None     => None
          | Some l'' =>
              let hl := TEVENT adt.(curid) (TTICKET HOLD_LOCK) in
              Some adt {log: ZMap.set lk ((hl::l'')) adt.(log)}
          end
      end
    | _, _ => None
    end.

  Definition pass_lock_spec0 (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), bars adt with
    | l, BarrierValid => let l' := TEVENT adt.(curid) (TTICKET INC_NOW) :: l in
          Some adt {log: ZMap.set lk (l') adt.(log)}
    | _, _ => None
    end.

  Inductive wait_lock_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | wait_lock_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' lk
      (Hinv: high_level_invariant labd)
      (Hspec: wait_lock_spec_wraparound (Int.unsigned lk) labd = Some labd'):
      wait_lock_spec_low_step s WB ((Vint lk)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive pass_lock_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | pass_lock_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' lk
      (Hinv: high_level_invariant labd)
      (Hspec: pass_lock_spec0 (Int.unsigned lk) labd = Some labd'):
      pass_lock_spec_low_step s WB ((Vint lk)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition wait_lock_spec_low: compatsem LDATAOps :=
      csem wait_lock_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition pass_lock_spec_low: compatsem LDATAOps :=
      csem pass_lock_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

  End WITHMEM.

End LockOpsSpecLow.
```
