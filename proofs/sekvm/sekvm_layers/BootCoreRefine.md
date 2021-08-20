# BootCoreRefine

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

Require Import BootCore.Spec.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import Constants.
Require Import VMPower.Layer.
Require Import HypsecCommLib.
Require Import BootCore.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Transparent H_CalLock.

Section BootCoreProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := BootCore_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := VMPower_ops) HDATA).

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
           acquire_lock_core_spec
           alloc_remap_addr_spec
           alloc_remap_addr_spec0
           check64_spec
           check_spec
           gen_vmid_spec
           gen_vmid_spec0
           get_next_remap_ptr_spec
           get_next_vmid_spec
           panic_spec
           release_lock_core_spec
           set_next_remap_ptr_spec
           set_next_vmid_spec.

      Lemma gen_vmid_spec_exists:
        forall habd habd' labd  res f
               (Hspec: gen_vmid_spec  habd = Some (habd', res))
               (Hrel: relate_RData f habd labd),
          exists labd', gen_vmid_spec0 labd = Some (labd', res) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite.
          eexists; split. reflexivity. constructor; reflexivity.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          eexists; (split; [reflexivity| constructor; repeat rewrite ZMap.set2; reflexivity]).
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          eexists; (split; [reflexivity| constructor; repeat rewrite ZMap.set2; reflexivity]).
        Qed.

      Lemma gen_vmid_spec_ref:
        compatsim (crel RData RData) (gensem gen_vmid_spec) gen_vmid_spec_low.
      Proof.
        Opaque gen_vmid_spec.
        compatsim_simpl (@match_RData).
        exploit gen_vmid_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent gen_vmid_spec.
      Qed.

      Lemma alloc_remap_addr_spec_exists:
        forall habd habd' labd pgnum res f
               (Hspec: alloc_remap_addr_spec pgnum habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', alloc_remap_addr_spec0 pgnum labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; srewrite.
          simpl. destruct_if. eexists; split. reflexivity. constructor; reflexivity.
          eexists; split. reflexivity. constructor; destruct habd'; simpl in *; srewrite; reflexivity.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          eexists; (split; [reflexivity| constructor; repeat rewrite ZMap.set2; reflexivity]).
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat (srewrite; try rewrite ZMap.gss; simpl).
          eexists; (split; [reflexivity| constructor; repeat rewrite ZMap.set2; reflexivity]).
        Qed.

      Lemma alloc_remap_addr_spec_ref:
        compatsim (crel RData RData) (gensem alloc_remap_addr_spec) alloc_remap_addr_spec_low.
      Proof.
        Opaque alloc_remap_addr_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_remap_addr_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_remap_addr_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) BootCore_passthrough VMPower.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End BootCoreProofHigh.

```
