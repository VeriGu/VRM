# SC_Full

```coq
Require Import List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Base_Full.

(* Am SC evemt os am evemt issued by a certain thread*)
Inductive GlobalEvent :=
| GE (tid : TID) (e : Event) : GlobalEvent.

(* An SC state contains the memory state and register states *)
Record GlobalState := mkGlobalState{
    memstate : MemState;
    regstates : TID -> RegState
} 
.
Instance etaGlobalState : Settable _ :=  settable! mkGlobalState <memstate; regstates>.

(* replay SC execution *)
Inductive rel_replay_sc : list GlobalEvent -> GlobalState -> Prop :=
| SC_EMPTY : rel_replay_sc [] (mkGlobalState (fun _ => 0) (fun _ _ => 0))
| SC_INTERNAL : forall le gs tid i rs
                    (Hgs : rel_replay_sc le gs)
                    (Hinternal : execute_internal i (regstates gs tid) = Some rs),
                    rel_replay_sc (GE tid (INTERNAL i) :: le) 
                        (gs <| regstates := update (regstates gs) tid rs |>)
| SC_ORACLE : forall le gs tid reg val
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (ORACLE reg val) :: le)
                        (gs <| regstates := update (regstates gs) tid (update (regstates gs tid) reg val) |>)
| SC_LOAD : forall le gs tid addr view reg
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (LOAD addr view reg) :: le)
                        (gs <| regstates := update (regstates gs) tid (update (regstates gs tid) reg (memstate gs addr)) |>)
| SC_STORE : forall le gs tid addr view reg
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (STORE addr view reg) :: le)
                        (gs <| memstate := update (memstate gs) addr (regstates gs tid reg) |>)
| SC_ACQ : forall le gs tid view addr
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (ACQ view addr) :: le) gs
| SC_REL : forall le gs tid view addr
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (REL view addr) :: le) gs.

```
