# ProofLow

```coq
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import MemoryX.
Require Import Events.
Require Import EventsX.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import Locations.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import LoopProof.
Require Import VCGen.
Require Import Errors.
Require Import Op.
Require Import Smallstep.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import GenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import Conventions.
Require Import Clight.
Require Import CDataTypes.
Require Import CLemmas.
Require Import XOmega.
Require Import ZArith.
Require Import TacticsForTesting.
Require Import CommonTactic.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import Ctypes.

Require Import AbstractMachine.Spec.
Require Import Ident.
Require Import MemRegion.Spec.
Require Import MemRegion.Code.
Require Import RData.
Require Import MmioSPTOps.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemRegionProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section mem_region_search_proof.

    Let L : compatlayer (cdata RData) :=
      get_mem_region_base ↦ gensem get_mem_region_base_spec
          ⊕ get_mem_region_cnt ↦ gensem get_mem_region_cnt_spec
          ⊕ get_mem_region_size ↦ gensem get_mem_region_size_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_mem_region_base: block.
      Hypothesis h_get_mem_region_base_s : Genv.find_symbol ge get_mem_region_base = Some b_get_mem_region_base.
      Hypothesis h_get_mem_region_base_p : Genv.find_funct_ptr ge b_get_mem_region_base
                                           = Some (External (EF_external get_mem_region_base
                                                            (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                  (Tcons tuint Tnil) tulong cc_default).
      Variable b_get_mem_region_cnt: block.
      Hypothesis h_get_mem_region_cnt_s : Genv.find_symbol ge get_mem_region_cnt = Some b_get_mem_region_cnt.
      Hypothesis h_get_mem_region_cnt_p : Genv.find_funct_ptr ge b_get_mem_region_cnt
                                          = Some (External (EF_external get_mem_region_cnt
                                                           (signature_of_type Tnil tuint cc_default))
                                                 Tnil tuint cc_default).
      Variable b_get_mem_region_size: block.
      Hypothesis h_get_mem_region_size_s : Genv.find_symbol ge get_mem_region_size = Some b_get_mem_region_size.
      Hypothesis h_get_mem_region_size_p : Genv.find_funct_ptr ge b_get_mem_region_size
                                           = Some (External (EF_external get_mem_region_size
                                                            (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                  (Tcons tuint Tnil) tulong cc_default).

      Lemma mem_region_search_body_correct:
        forall m d env le addr res
               (Henv: env = PTree.empty _)
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: mem_region_search_spec (VZ64 (Int64.unsigned addr)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) mem_region_search_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec mem_region_search_body.
        rewrite invalid_repr. unfold INVALID.
        get_loop_body.
        set (P := fun le0 m0 => m0 = (m, d) /\
                             le0 = (PTree.set _res (Vint (Int.repr 4294967295)) (PTree.set _i (Vint (Int.repr 0))
                                     (PTree.set _cnt (Vint (Int.repr z)) (set_opttemp (Some _t'1) (Vint (Int.repr z)) le))))).
        set (Q := fun le0 m0 => m0 = (m, d) /\ le0 ! _res = Some (Vint res)).
        set (Inv := fun le0 m0 n => exists idx1 res1,
                        mem_region_search_loop (Z.to_nat (z - n)) (Int64.unsigned addr) 0 INVALID d =
                        Some (Int.unsigned idx1, Int.unsigned res1) /\
                        m0 = (m, d) /\ 0 <= n  /\ n <= z /\ Int.unsigned idx1 = z - n /\
                        le0 ! _i = Some (Vint idx1) /\ le0 ! _res = Some (Vint res1) /\
                        le0 ! _addr = Some (Vlong addr) /\ le0 ! _cnt = Some (Vint (Int.repr z))).
        assert(loop_succ: forall N, Z.of_nat N <= z -> exists idx' res',
                    mem_region_search_loop (Z.to_nat (z - Z.of_nat N)) (Int64.unsigned addr) 0 INVALID d =
                    Some (Int.unsigned idx', Int.unsigned res')).
        { add_int C2 z0; try somega.
          induction N. simpl. simpl_case_no_se. autounfold. rewrite C2. intros. repeat eexists; reflexivity.
          intros. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in H.
          assert(Z.of_nat N <= z) by omega.
          apply IHN in H0. destruct H0 as (? & ? & ?).
          Local Opaque Z.of_nat. simpl in H0.
          simpl_func H0.
          autounfold; add_int C3 z2; try somega; repeat eexists; apply C3.
          autounfold; add_int C3 z1; try somega; repeat eexists; apply C3.
          autounfold; add_int C3 z1; try somega; repeat eexists; apply C3.
          autounfold; add_int C3 z1; try somega. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros. destruct H.
            rewrite H0 in *. exists z.
            replace (z - z) with 0 by omega. simpl.
            autounfold in *.
            repeat eexists; first [reflexivity|assumption|solve_proof_low].
            reflexivity. reflexivity.
          -  intros. unfold Inv in H. destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (Int.unsigned x <? z) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro; contra.
              * assert(Z.of_nat (Z.to_nat (n-1)) <= z) by (rewrite Z2Nat.id; omega).
                apply loop_succ in H8. rewrite Z2Nat.id in H8; try omega.
                intro. destruct H8 as (? & ? & ?). duplicate H8.
                rewrite loop_nat_sub1 in H8; try somega. simpl in H8. rewrite H in H8.
                simpl_func H8; repeat destruct_con; contra; bool_rel; try somega;
                  eexists; eexists; split;
                    first [exists (n-1); split; first [split; solve_proof_low | solve_proof_low; subst; unfold Inv;
                           repeat eexists; first[eassumption|solve_proof_low]] | solve_proof_low].
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro. unfold Q.
                assert (n=0) by omega. subst.
                split. reflexivity. solve_proof_low. autounfold in *. rewrite C2 in H. inv H.
                solve_proof_low.
              * intro T. inversion T. }
        assert (Pre: P (PTree.set _res (Vint (Int.repr 4294967295)) (PTree.set _i (Vint (Int.repr 0))
                        (PTree.set _cnt (Vint (Int.repr z)) (set_opttemp (Some _t'1) (Vint (Int.repr z)) le))))
                          (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre).
        destruct H as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec.
        unfold Q in Post. destruct Post. rewrite H in exec.
        eexists. big_vcgen. rewrite H. solve_proof_low.
      Qed.

    End BodyProof.

    Theorem mem_region_search_code_correct:
      spec_le (mem_region_search ↦ mem_region_search_spec_low) (〚 mem_region_search ↦ f_mem_region_search 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (mem_region_search_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_mem_region_search ) (Vlong addr :: nil)
               (create_undef_temps (fn_temps f_mem_region_search)))) hinv.
    Qed.

  End mem_region_search_proof.

End MemRegionProofLow.

```
