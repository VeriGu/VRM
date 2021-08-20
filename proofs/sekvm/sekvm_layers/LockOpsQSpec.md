# LockOpsQSpec

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
Require Import LockOps.Spec.
Require Import LockOps.Layer.

Local Open Scope Z_scope.

Section LockOpsQSpec.

  Definition wait_qlock_spec (lk: Z) (adt: RData) : option RData :=
    match ZMap.get lk adt.(log), ZMap.get lk adt.(lock) with
    | l, LockFalse =>
      let it := INC_TICKET (Z.to_nat lock_bound) in
      let to := ZMap.get lk adt.(oracle) in
      let l' := TEVENT adt.(curid) (TTICKET it) ::
                to adt.(curid) l ++ l in
      match Q_CalLock l' with
      | Some (self_c, other_c, b, q, tq) =>
        match Q_CalWait (CalWaitTime tq) adt.(curid) l' to with
        | Some ql =>
          let ql' := (TEVENT adt.(curid) (TTICKET HOLD_LOCK)) :: ql in
          match Q_CalLock ql' with
          | Some _ => Some adt {log: ZMap.set lk (ql') adt.(log)}
                               {lock: ZMap.set lk (LockOwn false) adt.(lock)}
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _, _ => None
    end
  .

  Definition pass_qlock_spec (lk: Z) (adt: RData) : option RData :=
    match ZMap.get lk adt.(log), ZMap.get lk adt.(lock) with
    | l, LockOwn false =>
      let l' := TEVENT adt.(curid) (TTICKET INC_NOW) :: l in
      match Q_CalLock l' with
      | Some _ => Some adt {log: ZMap.set lk (l') adt.(log)}
                           {lock: ZMap.set lk LockFalse adt.(lock)}
      | _ => None
      end
    | _,_ => None
    end
  .

End LockOpsQSpec.

Section LockOpsQSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := LockOps_ops) LDATA).

  Definition wait_qlock_spec0 (lk: Z) (adt: RData) : option RData :=
    wait_lock_spec lk adt.

  Definition pass_qlock_spec0 (lk: Z) (adt: RData) : option RData :=
    pass_lock_spec lk adt.

  Inductive wait_qlock_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | wait_qlock_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' lk
      (Hinv: high_level_invariant labd)
      (Hspec: wait_qlock_spec0 (Int.unsigned lk) labd = Some labd'):
      wait_qlock_spec_low_step s WB ((Vint lk)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive pass_qlock_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | pass_qlock_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' lk
      (Hinv: high_level_invariant labd)
      (Hspec: pass_qlock_spec0 (Int.unsigned lk) labd = Some labd'):
      pass_qlock_spec_low_step s WB ((Vint lk)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition wait_qlock_spec_low: compatsem LDATAOps :=
      csem wait_qlock_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition pass_qlock_spec_low: compatsem LDATAOps :=
      csem pass_qlock_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

  End WITHMEM.

End LockOpsQSpecLow.
```
