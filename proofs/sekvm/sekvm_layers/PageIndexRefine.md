# PageIndexRefine

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
Require Import PageIndex.Spec.
Require Import MemRegion.Layer.
Require Import HypsecCommLib.
Require Import PageIndex.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PageIndexProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := PageIndex_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MemRegion_ops) HDATA).

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

      Lemma get_s2_page_index_spec_exists:
        forall habd labd addr res f
               (Hspec: get_s2_page_index_spec addr habd = Some (VZ64 res))
               (Hrel: relate_RData f habd labd),
          get_s2_page_index_spec0 addr labd = Some (VZ64 res).
        Proof.
          intros. inv Hrel.
          assert(forall n addr i r, region_search_loop n addr 0 4294967295 (regions labd) = Some (i, r) ->
                           Spec.mem_region_search_loop n addr 0 4294967295 labd = Some (i, r)).
          { induction n. intros. simpl in *. assumption.
            intros. simpl in *.
            unfold Spec.get_mem_region_base_spec, Spec.get_mem_region_size_spec.
            autounfold in *. repeat simpl_hyp H; inv H.
            erewrite IHn; try eassumption.
            repeat auto_rewrite0. reflexivity.
            erewrite IHn; try eassumption.
            repeat auto_rewrite0. reflexivity. }
          Local Opaque Spec.mem_region_search_loop region_search_loop.
          unfold get_s2_page_index_spec0; autounfold.
          hstep. hstep. hstep. hstep.
          hsimpl_func Hspec.
          apply H in C2. repeat srewrite. reflexivity.
          apply H in C2. repeat srewrite. reflexivity.
          apply H in C2. repeat srewrite. reflexivity.
        Qed.

      Lemma get_s2_page_index_spec_ref:
        compatsim (crel RData RData) (gensem get_s2_page_index_spec) get_s2_page_index_spec_low.
      Proof.
        Opaque get_s2_page_index_spec.
        compatsim_simpl (@match_RData).
        exploit get_s2_page_index_spec_exists; eauto 1;
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

  End WITHMEM.

End PageIndexProofHigh.

```
