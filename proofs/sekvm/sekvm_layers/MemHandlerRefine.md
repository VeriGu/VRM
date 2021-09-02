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
Require Import MemHandler.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import CtxtSwitch.Layer.
Require Import MemHandler.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemHandlerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MemHandler_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := CtxtSwitch_ops) HDATA).

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

      Lemma clear_vm_stage2_range_spec_exists:
        forall habd habd' labd vmid start size f
               (Hspec: clear_vm_stage2_range_spec vmid start size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', clear_vm_stage2_range_spec vmid start size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma clear_vm_stage2_range_spec_ref:
        compatsim (crel RData RData) (gensem clear_vm_stage2_range_spec) clear_vm_stage2_range_spec_low.
      Proof.
        Opaque clear_vm_stage2_range_spec.
        compatsim_simpl (@match_RData).
        exploit clear_vm_stage2_range_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma el2_arm_lpae_map_spec_exists:
        forall habd habd' labd iova paddr prot cbndx index f
               (Hspec: el2_arm_lpae_map_spec iova paddr prot cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', el2_arm_lpae_map_spec iova paddr prot cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma el2_arm_lpae_map_spec_ref:
        compatsim (crel RData RData) (gensem el2_arm_lpae_map_spec) el2_arm_lpae_map_spec_low.
      Proof.
        Opaque el2_arm_lpae_map_spec.
        compatsim_simpl (@match_RData).
        exploit el2_arm_lpae_map_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma kvm_phys_addr_ioremap_spec_exists:
        forall habd habd' labd vmid gpa pa size f
               (Hspec: kvm_phys_addr_ioremap_spec vmid gpa pa size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', kvm_phys_addr_ioremap_spec vmid gpa pa size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros. inv Hrel; subst.
          eexists; split. eassumption.
          constructor; reflexivity.
        Qed.

      Lemma kvm_phys_addr_ioremap_spec_ref:
        compatsim (crel RData RData) (gensem kvm_phys_addr_ioremap_spec) kvm_phys_addr_ioremap_spec_low.
      Proof.
        Opaque kvm_phys_addr_ioremap_spec.
        compatsim_simpl (@match_RData).
        exploit kvm_phys_addr_ioremap_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

  End WITHMEM.

End MemHandlerProofHigh.

```
