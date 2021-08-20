# Promising_Full

```coq
Require Import List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Base_Full.

(* An execution trace in the promising model:
    a promise list and local execution logs for all threads
*)
Record Trace := mkTrace{
    promiselen : View;
    promiselist : View -> option Promise;
    executions : TID -> list Event
} 
.
Instance etaTrace : Settable _ :=  settable! mkTrace <promiselen; promiselist; executions>.

(* compute memory state from the promise list *)
Inductive rel_replay_mem : View -> (View -> option Promise) -> MemState -> Prop :=
| REPLAY_MEM_EMPTY : forall lp, rel_replay_mem 0 lp (fun addr => 0)
| REPLAY_MEM_WRITE : forall n lp tid val addr s
                        (Hlp : rel_replay_mem n lp s)
                        (Hwrite : lp (S n) = Some (WRITE tid val addr)),
                        rel_replay_mem (S n) lp (update s addr val)
| REPLAY_MEM_OTHER : forall n lp s (Hlp : rel_replay_mem n lp s)
                        (Hnotwrite: match lp (S n) with
                                    | Some (WRITE _ _ _) => false
                                    | _ => true
                        end = true
                        ),
                        rel_replay_mem (S n) lp s.


Definition get_value (view : View) (promises : View -> option Promise) : option Value :=
    match promises view with
    | Some (WRITE _ val _) => Some val
    | _ => None
    end.
(* compute register state of a specific thread from the promise list 
    and the thread's local execution *)
Inductive rel_replay_reg : (View -> option Promise) -> list Event -> RegState -> Prop :=
| REPLAY_REG_EMPTY : forall lp, rel_replay_reg lp [] (fun reg => 0)
| REPLAY_REG_INTERNAL : forall lp le s i s'
                            (Hs : rel_replay_reg lp le s)
                            (Hinternal : execute_internal i s = Some s'),
                            rel_replay_reg lp ((INTERNAL i) :: le) s'
(* register state update rule for data oracle calls*)
| REPLAY_REG_ORACLE : forall lp le s reg val
                            (Hs : rel_replay_reg lp le s),
                            rel_replay_reg lp ((ORACLE reg val) :: le) (update s reg val)
| REPLAY_REG_LOAD : forall lp le s addr view reg val
                            (Hs : rel_replay_reg lp le s)
                            (Hval : get_value view lp = Some val),
                            rel_replay_reg lp ((LOAD addr view reg) :: le) (update s reg val)
| REPLAY_REG_STORE : forall lp le s addr view reg
                            (Hs : rel_replay_reg lp le s)
                            (Hval : get_value view lp = Some (s reg)),
                            rel_replay_reg lp ((STORE addr view reg) :: le) s
| REPLAY_REG_ACQ : forall lp le s addr view
                            (Hs : rel_replay_reg lp le s),
                            rel_replay_reg lp (ACQ view addr :: le) s
| REPLAY_REG_REL : forall lp le s addr view
                            (Hs : rel_replay_reg lp le s),
                            rel_replay_reg lp (REL view addr :: le) s.

(* Promising Constraints *)

(* All promises are fulfilled exactly once *)
Definition fulfilled (trace : Trace) : Prop :=
    let promises := promiselist trace in
    forall (v : View)
        (Hmask : exists p, promises v = Some p),
        (exists (tid : TID) (e : Event) (n : View), 
            nth_error (executions trace tid) n = Some e /\ 
            match promises v with
            | None => False
            | Some (WRITE tid' val addr) => tid = tid' /\ (exists reg, e = STORE addr v reg)
            | Some (PULL tid' addr) => tid = tid' /\ e = REL v addr
            | Some (PUSH tid' addr) => tid = tid' /\ e = ACQ v addr
            end /\ 
            (forall tid' n' e'
                (He' : nth_error (executions trace tid') n' = Some e')
                (Hmatch :
                    match e' with
                    | STORE _ v' _ => v = v'
                    | REL v' _ => v = v'
                    | ACQ v' _ => v = v'
                    | _ => False
                    end
                ), tid = tid' /\ n = n'
            )
        ).

(* For each thread, the execution satisfies promising constraint *)

(* Register view and coherence view values in the promising model *)
Definition RegView := RegID -> View.
Definition CohView := Address -> View.

(* Thread-local promising state *)
Record LocalState := mkLocalState{
    regstate : RegState;
    regview : RegView;
    cohview : CohView;
    lastbarrier : View;
    lastview : View
} 
. 
Instance etaLocalState : Settable _ := settable! mkLocalState <regstate; regview; cohview; lastbarrier; lastview>.

Definition initstate :=
    {|
        regstate := (fun reg => 0);
        regview := (fun v => 0);
        cohview := (fun addr => 0);
        lastbarrier := 0;
        lastview := 0
    |}.

Definition execute_internal_ls (i : InternalEvent) (ls : LocalState) : option LocalState. Admitted.

Lemma execute_internal_ls_regstate :
    forall i ls ls' (Hls : execute_internal_ls i ls = Some ls'),
         execute_internal i (regstate ls) = Some (regstate ls').
Admitted.

(* Finding the last promise to addr before view v *)
Definition previous_promise (promises : View -> option Promise) (v : View) (addr : Address) : View. Admitted.

(* We only need the property that the inserting a new promise into the promise list will only increase the value of previous_promise *)
Lemma previous_promise_incr : 
    forall pl view p lb addr
        (Hmask : pl view = None),
        previous_promise (update pl view (Some p)) lb addr >= previous_promise pl lb addr.
Admitted.

(* Check the promising view constraints given a promising list and a local execution *)
Inductive rel_promising : TID -> (View -> option Promise) -> list Event -> LocalState -> Prop :=
| PA_EMPTY : forall tid lp, rel_promising tid lp [] initstate
| PA_INTERNAL : forall tid lp le ls i ls'
                    (Hls : rel_promising tid lp le ls)
                    (Hexec : execute_internal_ls i ls = Some ls'),
                    rel_promising tid lp ((INTERNAL i) :: le) ls'
(* data oracle calls do not affect view constraints *)
| PA_ORACLE : forall tid lp le ls reg val
                    (Hls : rel_promising tid lp le ls),
                    rel_promising tid lp ((ORACLE reg val) :: le)
                        (ls
                            <| regstate := update (regstate ls) reg val |>
                        )
| PA_LOAD : forall tid lp le ls addr val view reg 
                    (Hls : rel_promising tid lp le ls)
                    (Hbarrier : view >= previous_promise lp (lastbarrier ls) addr)
                    (Hcoh : view >= cohview ls addr)
                    (Hpromise : lp view = Some (WRITE tid val addr)),
                    rel_promising tid lp ((LOAD addr view reg) :: le)
                        (ls
                            <| regstate := update (regstate ls) reg val |>
                            <| lastview := max (lastview ls) view |>
                            <| cohview := update (cohview ls) addr view |>
                        )
| PA_ACQ : forall tid lp le ls view addr 
                    (Hls : rel_promising tid lp le ls)
                    (Hpromise : lp view = Some (PULL tid addr)),
                    rel_promising tid lp ((ACQ view addr) :: le) (ls <| lastbarrier := max view (lastbarrier ls) |>)
| PA_STORE : forall tid lp le ls addr view reg
                    (Hls : rel_promising tid lp le ls)
                    (Hbarrier : view >= lastbarrier ls)
                    (Hcoh : view > cohview ls addr)
                    (Hpromise : lp view = Some (WRITE tid (regstate ls reg) addr)),
                    rel_promising tid lp ((STORE addr view reg) :: le)
                        (ls <| lastview := max (lastview ls) view |>
                            <| cohview := update (cohview ls) addr view |>
                        )
| PA_REL : forall tid lp le ls view addr 
                    (Hls : rel_promising tid lp le ls)
                    (Hpromise : lp view = Some (PUSH tid addr))
                    (Hbarrier : view >= lastview ls),
                    rel_promising tid lp ((REL view addr) :: le) ls.



(* In valid promising trace, all promises must be fulfilled exactly once and it must satisfy the promising constraints *)
Inductive valid_trace : Trace -> Prop :=
| VALID_TRACE : forall t (Hfulfilled : fulfilled t) 
     (Hconsistent : forall tid, exists ls, rel_promising tid (promiselist t) (executions t tid) ls),
     valid_trace t.


(* the result of rel_replay_reg agrees with the regstates in rel_promising *)
Lemma rel_promising_localstate : 
    forall tid lp le ls 
        (Hls : rel_promising tid lp le ls)
        rs
        (Hrs : rel_replay_reg lp le rs),
        regstate ls = rs.
Proof.
    intros tid lp le ls Hls. induction Hls; intros; inversion Hrs; simpl in *.
    -   reflexivity.
    -   apply IHHls in Hs. rewrite <- Hs in Hinternal.
        erewrite execute_internal_ls_regstate in Hinternal. inversion Hinternal.
        reflexivity. easy.
    -   apply IHHls in Hs. subst s. easy.
    -   unfold get_value in Hval. rewrite Hpromise in Hval.
        inversion Hval. erewrite IHHls. reflexivity. easy.
    -   apply IHHls. apply Hs.
    -   apply IHHls. apply Hs.
    -   apply IHHls. apply Hs.
Qed.```
