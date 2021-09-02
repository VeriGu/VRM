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
Require Import MmioSPTWalk.Layer.
Require Import MmioSPTWalk.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioSPTOps.Layer.
Require Import MmioSPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioSPTOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioSPTOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioSPTWalk_ops) HDATA).

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
           acquire_lock_spt_spec
           release_lock_spt_spec
           clear_smmu_pt_spec
           walk_smmu_pt_spec
           set_smmu_pt_spec
           init_spt_spec
           init_spt_spec0
           walk_spt_spec
           walk_spt_spec0
           map_spt_spec
           map_spt_spec0
           unmap_spt_spec
           unmap_spt_spec0
           check64_spec.

      Lemma init_spt_spec_exists:
        forall habd habd' labd cbndx index f
               (Hspec: init_spt_spec cbndx index habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', init_spt_spec0 cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C3. simpl_hyp C4. simpl_hyp C5. simpl_hyp C6.
            destruct p3; destruct p3; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            simpl. inv Hspec. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma init_spt_spec_ref:
        compatsim (crel RData RData) (gensem init_spt_spec) init_spt_spec_low.
      Proof.
        Opaque init_spt_spec.
        compatsim_simpl (@match_RData).
        exploit init_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent init_spt_spec.
      Qed.

      Lemma walk_spt_spec_exists:
        forall habd habd' labd cbndx index addr res f
               (Hspec: walk_spt_spec cbndx index addr habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', walk_spt_spec0 cbndx index addr labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec.  repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C7. simpl_hyp C8. simpl_hyp C9. simpl_hyp C10.
            destruct p3; destruct p3; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            simpl. inv Hspec. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma walk_spt_spec_ref:
        compatsim (crel RData RData) (gensem walk_spt_spec) walk_spt_spec_low.
      Proof.
        Opaque walk_spt_spec.
        compatsim_simpl (@match_RData).
        exploit walk_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_spt_spec.
      Qed.

      Lemma map_spt_spec_exists:
        forall habd habd' labd cbndx index addr pte f
               (Hspec: map_spt_spec cbndx index addr pte habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', map_spt_spec0 cbndx index addr pte labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec.  repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C9. simpl_hyp C10. simpl_hyp C11. simpl_hyp C12.
            destruct p4; destruct p4; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            destruct b. inv Hspec. simpl. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
            inv Hspec. simpl. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma map_spt_spec_ref:
        compatsim (crel RData RData) (gensem map_spt_spec) map_spt_spec_low.
      Proof.
        Opaque map_spt_spec.
        compatsim_simpl (@match_RData).
        exploit map_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_spt_spec.
      Qed.

      Lemma unmap_spt_spec_exists:
        forall habd habd' labd cbndx index addr res f
               (Hspec: unmap_spt_spec cbndx index addr habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', unmap_spt_spec0 cbndx index addr labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec.  repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C8. simpl_hyp C9. simpl_hyp C10. simpl_hyp C11.
            destruct p3; destruct p3; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            destruct (z1 =? 0) eqn:Hpte. inv C7.
            inv Hspec. simpl in *. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl in *. rewrite C3. repeat rewrite ZMap.set2. reflexivity.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            destruct b. simpl in *. inv Hspec. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl in *. rewrite C3. repeat rewrite ZMap.set2. reflexivity.
            simpl in *. inv Hspec. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl in *. rewrite C3. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma unmap_spt_spec_ref:
        compatsim (crel RData RData) (gensem unmap_spt_spec) unmap_spt_spec_low.
      Proof.
        Opaque unmap_spt_spec.
        compatsim_simpl (@match_RData).
        exploit unmap_spt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent unmap_spt_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MmioSPTOpsProofHigh.

```
