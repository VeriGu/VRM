# ProofHigh

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

Require Import TrapHandler.Layer.
Require Import RData.
Require Import TrapHandler.Spec.
Require Import TrapHandlerRaw.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import AbstractMachine.Spec.
Require Import TrapHandlerRaw.Spec.
Require Import TrapDispatcher.Spec.
Require Import FaultHandler.Spec.
Require Import MemHandler.Spec.
Require Import MmioOps.Spec.
Require Import BootOps.Spec.
Require Import MemoryOps.Spec.
Require Import MemManager.Spec.
Require Import NPTWalk.Spec.
Require Import NPTOps.Spec.
Require Import MmioSPTWalk.Spec.
Require Import MmioSPTOps.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TrapHandlerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := TrapHandler_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := TrapHandlerRaw_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_adt: hadt = ladt
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

      Lemma host_hvc_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_hvc_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_hvc_handler_spec  labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma host_npt_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_npt_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_npt_handler_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma host_vcpu_run_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: host_vcpu_run_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', host_vcpu_run_handler_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma vm_exit_handler_spec_exists:
        forall habd habd' labd  f
               (Hspec: vm_exit_handler_spec  habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', vm_exit_handler_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma mem_load_spec_exists:
        forall habd habd' labd gfn reg f
               (Hspec: mem_load_spec gfn reg habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', mem_load_spec gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma mem_store_spec_exists:
        forall habd habd' labd gfn reg f
               (Hspec: mem_store_spec gfn reg habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', mem_store_spec gfn reg labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma dev_load_spec_exists:
        forall habd habd' labd gfn reg cbndx index f
               (Hspec: dev_load_spec gfn reg cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', dev_load_spec gfn reg cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma dev_store_spec_exists:
        forall habd habd' labd gfn reg cbndx index f
               (Hspec: dev_store_spec gfn reg cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', dev_store_spec gfn reg cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

    End FreshPrim.

  End WITHMEM.

End TrapHandlerProofHigh.

```
