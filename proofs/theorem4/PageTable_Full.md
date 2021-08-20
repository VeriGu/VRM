# PageTable_Full

```coq
Require Import List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import PeanoNat.

Require Import Psatz.

Require Import Base_Full Promising_Full DRF_Full SC_Full.


Parameter is_page_table_addr : Address -> Prop.

(* A page table log contains all possible values a read to a page table entry can be *)
Definition PageTableLog := list Value.

(* Compute the page table log (which contains the values in the last critical section of this address) given the promise list *)
Inductive rel_page_table_log : View -> (View -> option Promise) -> Address -> PageTableLog -> bool -> Prop :=
| PTL_EMPTY : forall lp addr, rel_page_table_log 0 lp addr [default] true
| PTL_WRITE_NEW : forall lp addr n val tid ptl
                        (Hptl : rel_page_table_log n lp addr ptl true)
                        (Hlp : lp (S n) = Some (WRITE tid val addr)),
                        rel_page_table_log (S n) lp addr [val] false
| PTL_WRITE_OLD : forall lp addr n val tid ptl
                        (Hptl : rel_page_table_log n lp addr ptl false)
                        (Hlp : lp (S n) = Some (WRITE tid val addr)),
                        rel_page_table_log (S n) lp addr (val :: ptl) false
| PTL_PULL : forall lp addr n tid ptl b
                        (Hptl : rel_page_table_log n lp addr ptl b)
                        (Hlp : lp (S n) = Some (PULL tid addr)),
                        rel_page_table_log (S n) lp addr ptl true
| PTL_PUSH : forall lp addr n tid ptl b
                        (Hptl : rel_page_table_log n lp addr ptl b)
                        (Hlp : lp (S n) = Some (PUSH tid addr)),
                        rel_page_table_log (S n) lp addr ptl b
| PTL_NONE : forall lp addr n ptl b
                        (Hptl : rel_page_table_log n lp addr ptl b)
                        (Hlp : lp (S n) = None),
                        rel_page_table_log (S n) lp addr ptl b.

(* transactional-page-table constraint *)
Definition transactional_page_table (lp : View -> option Promise) := 
    forall n addr ptl b
        (Haddr : is_page_table_addr addr)
        (Hptl : rel_page_table_log n lp addr ptl b), 
        exists val, ptl = [val].

(* The theorem about page table 
    If the page table satisfies the transactional-page-table constraints,
    the value it can read can only be the result at the end of the execution
*)
Theorem page_table_same_result :
    forall lp
        (Htrans : transactional_page_table lp)
        n addr ms ptl b
        (Haddr : is_page_table_addr addr)
        (* ms is the memory result at the end of the execution *)
        (Hms : rel_replay_mem n lp ms)
        (Hptl : rel_page_table_log n lp addr ptl b),
        ptl = [ms addr].
Proof.
    induction n; intros.
    -   inversion Hms. inversion Hptl. reflexivity.
    -   inversion Hms; inversion Hptl; try (try rewrite Hlp0 in Hwrite; try rewrite Hlp0 in Hnotwrite; discriminate).
        +   rewrite Hwrite in Hlp0. inversion Hlp0.
            rewrite update_same. reflexivity.
        +   rewrite Hwrite in Hlp0. inversion Hlp0.
            rewrite update_same.
            unfold transactional_page_table in *.
            edestruct Htrans. apply Haddr. apply Hptl.
            rewrite <- H6 in H. inversion H. reflexivity.
        +   eapply IHn. easy. easy. apply Hptl0.
        +   eapply IHn. easy. easy. apply Hptl0.
        +   eapply IHn. easy. easy. apply Hptl0.
Qed.


```
