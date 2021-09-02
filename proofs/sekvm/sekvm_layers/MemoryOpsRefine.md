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

Require Import AbstractMachine.Spec.
Require Import MemoryOps.Spec.
Require Import RData.
Require Import MemManager.Layer.
Require Import Constants.
Require Import MemoryOps.Layer.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemoryOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MemoryOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MemManager_ops) HDATA).

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

      Lemma clear_vm_range_spec_exists:
        forall habd habd' labd vmid pfn num f
               (Hspec: clear_vm_range_spec vmid pfn num habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', clear_vm_range_spec vmid pfn num labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel; rewrite Hspec.
        eexists; split. reflexivity. constructor; reflexivity.
      Qed.

      Lemma clear_vm_range_spec_ref:
        compatsim (crel RData RData) (gensem clear_vm_range_spec) clear_vm_range_spec_low.
      Proof.
        Opaque clear_vm_range_spec.
        compatsim_simpl (@match_RData).
        exploit clear_vm_range_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent clear_vm_range_spec.
      Qed.

      Lemma prot_and_map_vm_s2pt_spec_exists:
        forall habd habd' labd vmid addr pte level f
               (Hspec: prot_and_map_vm_s2pt_spec vmid addr pte level habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', prot_and_map_vm_s2pt_spec vmid addr pte level labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma prot_and_map_vm_s2pt_spec_ref:
        compatsim (crel RData RData) (gensem prot_and_map_vm_s2pt_spec) prot_and_map_vm_s2pt_spec_low.
      Proof.
        Opaque prot_and_map_vm_s2pt_spec.
        compatsim_simpl (@match_RData).
        exploit prot_and_map_vm_s2pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent prot_and_map_vm_s2pt_spec.
      Qed.

      Lemma grant_stage2_sg_gpa_spec_exists:
        forall habd habd' labd vmid addr size f
               (Hspec: grant_stage2_sg_gpa_spec vmid addr size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', grant_stage2_sg_gpa_spec vmid addr size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma grant_stage2_sg_gpa_spec_ref:
        compatsim (crel RData RData) (gensem grant_stage2_sg_gpa_spec) grant_stage2_sg_gpa_spec_low.
      Proof.
        Opaque grant_stage2_sg_gpa_spec.
        compatsim_simpl (@match_RData).
        exploit grant_stage2_sg_gpa_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent grant_stage2_sg_gpa_spec.
      Qed.

      Lemma revoke_stage2_sg_gpa_spec_exists:
        forall habd habd' labd vmid addr size f
               (Hspec: revoke_stage2_sg_gpa_spec vmid addr size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', revoke_stage2_sg_gpa_spec vmid addr size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma revoke_stage2_sg_gpa_spec_ref:
        compatsim (crel RData RData) (gensem revoke_stage2_sg_gpa_spec) revoke_stage2_sg_gpa_spec_low.
      Proof.
        Opaque revoke_stage2_sg_gpa_spec.
        compatsim_simpl (@match_RData).
        exploit revoke_stage2_sg_gpa_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent revoke_stage2_sg_gpa_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MemoryOpsProofHigh.
```
