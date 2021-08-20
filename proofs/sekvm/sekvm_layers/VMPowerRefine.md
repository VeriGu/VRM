# VMPowerRefine

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

Require Import VMPower.Spec.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import Constants.
Require Import MemoryOps.Layer.
Require Import VMPower.Layer.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Transparent H_CalLock.

Section VMPowerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := VMPower_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MemoryOps_ops) HDATA).

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

      Hint Unfold
           acquire_lock_vm_spec
           check_spec
           get_vm_poweron_spec
           get_vm_poweron_spec0
           get_vm_state_spec
           release_lock_vm_spec
           set_vm_poweroff_spec
           set_vm_poweroff_spec0
           set_vm_state_spec.

      Lemma set_vm_poweroff_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: set_vm_poweroff_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_vm_poweroff_spec0 vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite.
          eexists; split. reflexivity. constructor; reflexivity.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          eexists; split. reflexivity. constructor.
          repeat rewrite ZMap.set2; reflexivity.
        Qed.

      Lemma set_vm_poweroff_spec_ref:
        compatsim (crel RData RData) (gensem set_vm_poweroff_spec) set_vm_poweroff_spec_low.
      Proof.
        Opaque set_vm_poweroff_spec.
        compatsim_simpl (@match_RData).
        exploit set_vm_poweroff_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_vm_poweroff_spec.
      Qed.

      Lemma get_vm_poweron_spec_exists:
        forall habd habd' labd vmid res f
               (Hspec: get_vm_poweron_spec vmid habd = Some (habd', res))
               (Hrel: relate_RData f habd labd),
          exists labd', get_vm_poweron_spec0 vmid labd = Some (labd', res) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite.
          eexists; split. reflexivity. constructor; reflexivity.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          destruct_if; eexists; (split; [reflexivity| constructor; repeat rewrite ZMap.set2; reflexivity]).
        Qed.

      Lemma get_vm_poweron_spec_ref:
        compatsim (crel RData RData) (gensem get_vm_poweron_spec) get_vm_poweron_spec_low.
      Proof.
        Opaque get_vm_poweron_spec.
        compatsim_simpl (@match_RData).
        exploit get_vm_poweron_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent get_vm_poweron_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) VMPower_passthrough MemoryOps.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End VMPowerProofHigh.

```
