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

Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioOps.Layer.
Require Import VCPUOpsAux.Layer.
Require Import VCPUOpsAux.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section VCPUOpsAuxProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := VCPUOpsAux_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioOps_ops) HDATA).

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

      Lemma reset_gp_regs_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: reset_gp_regs_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', reset_gp_regs_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma reset_sys_regs_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: reset_sys_regs_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', reset_sys_regs_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma sync_dirty_to_shadow_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: sync_dirty_to_shadow_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', sync_dirty_to_shadow_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma prep_wfx_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: prep_wfx_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', prep_wfx_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma prep_hvc_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: prep_hvc_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', prep_hvc_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma prep_abort_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: prep_abort_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', prep_abort_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma update_exception_gp_regs_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: update_exception_gp_regs_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', update_exception_gp_regs_spec vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

      Lemma post_handle_shadow_s2pt_fault_spec_exists:
        forall habd habd' labd vmid vcpuid addr f
          (Hspec: post_handle_shadow_s2pt_fault_spec vmid vcpuid addr habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', post_handle_shadow_s2pt_fault_spec vmid vcpuid addr labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros. inv Hrel.
        eexists; split. eassumption.
        constructor; reflexivity.
      Qed.

    End FreshPrim.

  End WITHMEM.

End VCPUOpsAuxProofHigh.

```
