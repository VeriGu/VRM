# DRF_Isolated

```coq
Require Import List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Base_Isolated Promising_Isolated.

(* DRF-kernel constraint *)
(* 
    DRF-kernel constraint is defined by a global ownership for the promise lists
    If the global ownership exists, then the execution satisfies DRF
*)

Definition OwnershipMap := Address -> option TID.

(* Check global ownership given promise list *)
Inductive rel_global_ownership : View -> OwnershipMap -> (View -> option Promise) -> OwnershipMap -> Prop :=
| GO_EMPTY : forall om lp, rel_global_ownership 0 om lp om
| GO_PULL : forall n om lp omr tid addr 
                (Hlp : rel_global_ownership n om lp omr)
                (Hown : om addr = None)
                (Hlp : lp (S n) = Some (PULL tid addr)),
                rel_global_ownership (S n) (update om addr (Some tid)) lp omr
| GO_PUSH : forall n om lp omr tid addr 
                (Hlp : rel_global_ownership n om lp omr)
                (Hown : om addr = Some tid)
                (Hlp : lp (S n) = Some (PUSH tid addr)),
                rel_global_ownership (S n) (update om addr None) lp omr
| GO_WRITE : forall n om lp omr tid val addr
                (Hlp : rel_global_ownership n om lp omr)
                (Hown : om addr = Some tid)
                (Hlp : lp (S n) = Some (WRITE tid val addr)),
                rel_global_ownership (S n) om lp omr
| GO_NONE : forall n om lp omr
                (Hlp : rel_global_ownership n om lp omr)
                (Hlp : lp (S n) = None),
                rel_global_ownership (S n) om lp omr.

(* No-barrier-misuse constraint *)
(* 
    No-barrier-misuse constraint is defined by a local ownership.
    It checks whether barriers are correctly placed according to the 
    PUSH/PULL promise in the promise list
*)
Record LocalOwnership := mkLocalOwnership{
    ownership_local : Address -> bool;
    lastbarrier_local : Address -> View
}.
Instance etaLocalOwnership : Settable _ := settable! mkLocalOwnership <ownership_local; lastbarrier_local>.

Definition initownership := 
    {|
        ownership_local := fun addr => false;
        lastbarrier_local := fun addr => 0
    |}.

(* Check local ownership given the promise list, the local execution list of a CPU *)
Inductive rel_local_ownership : (View -> option Promise) -> list Event -> LocalOwnership -> Prop :=
| LO_EMPTY : forall promises, rel_local_ownership promises [] initownership
| LO_LOAD : forall promises le lo addr view reg 
                (Hlo : rel_local_ownership promises le lo)
                (Hown : ownership_local lo addr = true),
                rel_local_ownership promises ((LOAD addr view reg) :: le) lo
| LO_STORE : forall promises le lo addr view reg
                (Hlo : rel_local_ownership promises le lo)
                (Hown : ownership_local lo addr = true),
                rel_local_ownership promises ((STORE addr view reg) :: le) lo
| LO_ACQ : forall promises le lo addr view
                (Hlo : rel_local_ownership promises le lo)
                (Hown : ownership_local lo addr = false)
                (Hview : lastbarrier_local lo addr <= view),
                rel_local_ownership promises ((ACQ view addr) :: le)
                (lo 
                    <| ownership_local := update (ownership_local lo) addr true |>
                    <| lastbarrier_local := update (lastbarrier_local lo) addr view |>
                )
| LO_REL : forall promises le lo addr view 
                (Hlo : rel_local_ownership promises le lo)
                (Hown : ownership_local lo addr = true)
                (Hview : lastbarrier_local lo addr <= view),
                rel_local_ownership promises ((REL view addr) :: le)
                (lo
                    <| ownership_local := update (ownership_local lo) addr false |>
                    <| lastbarrier_local := update (lastbarrier_local lo) addr view |>
                )
| LO_INTERNAL : forall promises le lo i
                (Hlo : rel_local_ownership promises le lo),
                rel_local_ownership promises ((INTERNAL i) :: le) lo.

(* DRF kernel and No-barrier-misuse constraints *)
Inductive DRF : Trace -> Prop :=
| DRF_TRACE : forall (t : Trace)  (n : View)
                (Hglobal : exists om : OwnershipMap, rel_global_ownership n om (promiselist t) (fun _ => None))
                (Hlocal : forall tid : TID, exists lo, rel_local_ownership (promiselist t) (executions t tid) lo),
                DRF t.```
