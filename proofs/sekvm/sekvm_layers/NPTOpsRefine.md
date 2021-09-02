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

Require Import NPTOps.Layer.
Require Import NPTWalk.Layer.
Require Import HypsecCommLib.
Require Import NPTOps.Spec.
Require Import NPTWalk.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import Constants.
Require Import RData.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section NPTOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := NPTOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := NPTWalk_ops) HDATA).

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
           acquire_lock_pt_spec
           release_lock_pt_spec
           get_npt_level_spec
           walk_npt_spec
           set_npt_spec
           check_spec
           check64_spec
           get_level_s2pt_spec
           get_level_s2pt_spec0
           walk_s2pt_spec
           walk_s2pt_spec0
           map_s2pt_spec
           map_s2pt_spec0
           clear_pfn_host_spec
           clear_pfn_host_spec0.

      Lemma get_level_s2pt_spec_exists:
        forall habd habd' labd vmid addr res f
               (Hspec: get_level_s2pt_spec vmid addr habd = Some (habd', res))
               (Hrel: relate_RData f habd labd),
          exists labd', get_level_s2pt_spec0 vmid addr labd = Some (labd', res) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C7. simpl_hyp C8. simpl_hyp C9. simpl_hyp C10.
            destruct p4; destruct p4; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            destruct (phys_page z0 =? 0).
            + simpl. inv Hspec. eexists. split. reflexivity.
              constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
            + srewrite. simpl. inv Hspec. eexists. split. reflexivity.
              constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma get_level_s2pt_spec_ref:
        compatsim (crel RData RData) (gensem get_level_s2pt_spec) get_level_s2pt_spec_low.
      Proof.
        Opaque get_level_s2pt_spec.
        compatsim_simpl (@match_RData).
        exploit get_level_s2pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent get_level_s2pt_spec.
      Qed.

      Lemma walk_s2pt_spec_exists:
        forall habd habd' labd vmid addr res f
               (Hspec: walk_s2pt_spec vmid addr habd = Some (habd', (VZ64 res)))
               (Hrel: relate_RData f habd labd),
          exists labd', walk_s2pt_spec0 vmid addr labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - repeat srewrite; simpl. eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C7. simpl_hyp C8. simpl_hyp C9. simpl_hyp C10.
            destruct p4; destruct p4; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            inv Hspec. eexists. split. reflexivity.
            constructor. destruct labd, shared; simpl. repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma walk_s2pt_spec_ref:
        compatsim (crel RData RData) (gensem walk_s2pt_spec) walk_s2pt_spec_low.
      Proof.
        Opaque walk_s2pt_spec.
        compatsim_simpl (@match_RData).
        exploit walk_s2pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent walk_s2pt_spec.
      Qed.

      Lemma map_s2pt_spec_exists:
        forall habd habd' labd vmid addr level pte f
               (Hspec: map_s2pt_spec vmid addr level pte habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', map_s2pt_spec0 vmid addr level pte labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. repeat srewrite; simpl. eexists.
            split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C10. simpl_hyp C11. simpl_hyp C12. simpl_hyp C13.
            destruct p4; destruct p4; destruct h; destruct o; contra.
            repeat (srewrite; try rewrite ZMap.gss; simpl). destruct b.
            + inv Hspec. eexists. split. reflexivity.
              constructor. destruct labd, shared; simpl.
              repeat rewrite ZMap.set2. reflexivity.
            + inv Hspec. eexists. split. reflexivity.
              constructor. destruct labd, shared; simpl.
              repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma map_s2pt_spec_ref:
        compatsim (crel RData RData) (gensem map_s2pt_spec) map_s2pt_spec_low.
      Proof.
        Opaque map_s2pt_spec.
        compatsim_simpl (@match_RData).
        exploit map_s2pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_s2pt_spec.
      Qed.

      Lemma clear_pfn_host_spec_exists:
        forall habd habd' labd pfn f
               (Hspec: clear_pfn_host_spec pfn habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', clear_pfn_host_spec0 pfn labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          repeat autounfold in *.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. repeat srewrite; simpl.
            extract_if. apply andb_true_iff; split; bool_rel_all; omega. rewrite Cond. simpl.
            eexists. split. reflexivity. constructor; reflexivity.
          - Local Transparent H_CalLock. simpl in *.
            simpl_hyp C8. simpl_hyp C9. simpl_hyp C10. simpl_hyp C11.
            destruct p5; destruct p5; destruct h; destruct o; contra.
            assert(z * 4096 / 4096 = z) by (apply Z_div_mult_full; omega).
            repeat (srewrite; try rewrite ZMap.gss; simpl).
            extract_if. apply andb_true_iff; split; bool_rel_all; omega. rewrite Cond. simpl.
            destruct (phys_page z0 =? 0).
            + simpl in *. inversion C6. rewrite <- H1 in *.
              inversion Hspec. rewrite <- H2 in *. rewrite <- H3 in *.
              eexists. split. reflexivity.
              constructor. destruct labd, shared; simpl in *.
              repeat rewrite ZMap.gss. repeat rewrite ZMap.set2. rewrite C1. reflexivity.
            + srewrite.
              destruct (z2 =? 0).
              * inversion C6. rewrite <- H1 in *.
                inversion Hspec. rewrite <- H2 in *. rewrite <- H3 in *.
                eexists. split. reflexivity.
                constructor. destruct labd, shared; simpl in *.
                repeat rewrite ZMap.gss. repeat rewrite ZMap.set2. rewrite C1. reflexivity.
              * repeat (srewrite; try rewrite ZMap.gss; simpl). destruct b.
                inversion Hspec.  eexists. split. reflexivity.
                constructor. destruct labd, shared; simpl.
                repeat rewrite ZMap.set2. reflexivity.
                inversion Hspec. eexists. split. reflexivity.
                constructor. destruct labd, shared; simpl.
                repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma clear_pfn_host_spec_ref:
        compatsim (crel RData RData) (gensem clear_pfn_host_spec) clear_pfn_host_spec_low.
      Proof.
        Opaque clear_pfn_host_spec.
        compatsim_simpl (@match_RData).
        exploit clear_pfn_host_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent clear_pfn_host_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End NPTOpsProofHigh.

```
