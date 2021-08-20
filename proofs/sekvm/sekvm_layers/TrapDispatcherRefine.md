# TrapDispatcherRefine

```coq
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import ZSet.
Require Import ListLemma2.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import RealParams.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import LayerCalculusLemma.
Require Import TacticsForTesting.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import TrapDispatcher.Spec.
Require Import RData.
Require Import Constants.
Require Import FaultHandler.Layer.
Require Import TrapDispatcher.Layer.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TrapDispatcherProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := TrapDispatcher_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := FaultHandler_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_rel: hadt = ladt
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    Section FreshPrim.

      Lemma host_hvc_dispatcher_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_hvc_dispatcher_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_hvc_dispatcher_spec  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof host_hvc_dispatcher0; repeat hstep; try htrivial.
        Qed.

      Lemma host_hvc_dispatcher_spec_ref:
        compatsim (crel RData RData) (gensem host_hvc_dispatcher_spec) host_hvc_dispatcher_spec_low.
      Proof.
        Opaque host_hvc_dispatcher_spec.
        compatsim_simpl (@match_RData).
        exploit host_hvc_dispatcher_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma vm_exit_dispatcher_spec_exists:
        forall habd habd' labd vmid vcpuid res f
               (Hspec: vm_exit_dispatcher_spec vmid vcpuid habd = Some (habd', res))
               (Hrel: relate_RData f habd labd),
          exists labd', vm_exit_dispatcher_spec vmid vcpuid labd = Some (labd', res) /\ relate_RData f habd' labd'.
        Proof.
          intros until f.
          solve_refine_proof vm_exit_dispatcher0; repeat hstep; try htrivial.
        Qed.

      Lemma vm_exit_dispatcher_spec_ref:
        compatsim (crel RData RData) (gensem vm_exit_dispatcher_spec) vm_exit_dispatcher_spec_low.
      Proof.
        Opaque vm_exit_dispatcher_spec.
        compatsim_simpl (@match_RData).
        exploit vm_exit_dispatcher_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) TrapDispatcher_passthrough FaultHandler.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End TrapDispatcherProofHigh.

```
