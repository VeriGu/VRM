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
Require Import BootAux.Spec.
Require Import BootAux.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import BootCore.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section BootAuxProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := BootAux_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := BootCore_ops) HDATA).

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

      Lemma unmap_and_load_vm_image_spec_exists:
        forall habd habd' labd vmid target_addr remap_addr num f
               (Hspec: unmap_and_load_vm_image_spec vmid target_addr remap_addr num habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', unmap_and_load_vm_image_spec vmid target_addr remap_addr num labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma unmap_and_load_vm_image_spec_ref:
        compatsim (crel RData RData) (gensem unmap_and_load_vm_image_spec) unmap_and_load_vm_image_spec_low.
      Proof.
        Opaque unmap_and_load_vm_image_spec.
        compatsim_simpl (@match_RData).
        exploit unmap_and_load_vm_image_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent unmap_and_load_vm_image_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End BootAuxProofHigh.

```
