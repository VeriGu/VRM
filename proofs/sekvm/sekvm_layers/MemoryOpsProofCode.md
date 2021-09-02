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

Require Import MemManager.Layer.
Require Import NPTOps.Spec.
Require Import MemoryOps.Code.
Require Import MemoryOps.Spec.
Require Import MemManager.Spec.
Require Import Ident.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemoryOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section clear_vm_range_proof.


    Let L : compatlayer (cdata RData) :=
      clear_vm_page ↦ gensem clear_vm_page_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_clear_vm_page: block.
      Hypothesis h_clear_vm_page_s : Genv.find_symbol ge clear_vm_page = Some b_clear_vm_page.
      Hypothesis h_clear_vm_page_p : Genv.find_funct_ptr ge b_clear_vm_page
                                     = Some (External (EF_external clear_vm_page
                                                      (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).

      Lemma clear_vm_range_body_correct:
        forall m d d' env le vmid pfn num
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTnum: PTree.get _num le = Some (Vlong num))
               (Hinv: high_level_invariant d)
               (Hspec: clear_vm_range_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned num)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_vm_range_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_vm_range_body; try solve [eexists; solve_proof_low].
        get_loop_body. clear_hyp.
        remember (Int64.unsigned num) as num0.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le).
        set (Q := fun (le0: temp_env) m0 => m0 = (m, d')).
        set (Inv := fun le0 m0 n => exists pfn1 adt1,
                        clear_vm_loop (Z.to_nat (num0 - n)) (Int64.unsigned pfn) (Int.unsigned vmid) d =
                        Some (Int64.unsigned pfn1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num0 /\ le0 ! _num = Some (Vlong (Int64.repr n)) /\
                        le0 ! _pfn = Some (Vlong pfn1) /\ le0 ! _vmid = Some (Vint vmid)).
        assert(loop_succ: forall N, Z.of_nat N <= num0 -> exists pfn' adt',
                    clear_vm_loop (Z.to_nat (num0 - Z.of_nat N)) (Int64.unsigned pfn) (Int.unsigned vmid) d =
                    Some (Int64.unsigned pfn', adt')).
        { add_int64 C1 z; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C1. intros. repeat eexists; reflexivity.
          intros. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in H.
          assert(Z.of_nat N <= num0) by omega.
          apply IHN in H0. destruct H0 as (? & ? & ?).
          Local Opaque Z.of_nat. Local Opaque clear_vm_page_spec.
          simpl in H0. simpl_func H0.
          add_int64' z0. repeat eexists. somega. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C. destruct C as [C C'].
            rewrite C' in *. exists num0.
            replace (num0 - num0) with 0 by omega. simpl. add_int64' 0; try somega.
            rewrite Heqnum0. repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. repeat split.
              * solve_proof_low.
              * solve_proof_low.
              * intro C. inversion C.
              * assert(Z.of_nat (Z.to_nat (n-1)) <= num0) by (rewrite Z2Nat.id; omega).
                apply loop_succ in H6. rewrite Z2Nat.id in H6; try omega.
                intro. destruct H6 as (? & ? & ?). duplicate H6.
                rewrite loop_nat_sub1 in H6; try somega.
                simpl in H6. rewrite H in H6.
                autounfold in H6; repeat simpl_hyp H6. inversion H6. rewrite H10 in *.
                bool_rel_all. eexists; eexists; split. solve_proof_low.
                exists (n-1). split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]].
              + eexists. eexists. repeat split.
                * solve_proof_low.
                * solve_proof_low.
                * intro. unfold Q.
                  assert (n=0) by omega. rewrite H7 in H. rewrite Z.sub_0_r in H.
                  rewrite C1 in H. inv H. reflexivity.
                * intro C. inversion C. }
        assert (Pre: P le (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre).
        destruct H as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec.
        unfold Q in Post. rewrite Post in exec.
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem clear_vm_range_code_correct:
      spec_le (clear_vm_range ↦ clear_vm_range_spec_low) (〚 clear_vm_range ↦ f_clear_vm_range 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (clear_vm_range_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_clear_vm_range ) (Vint vmid :: Vlong pfn :: Vlong num :: nil)
               (create_undef_temps (fn_temps f_clear_vm_range)))) hinv.
    Qed.

  End clear_vm_range_proof.

  Section prot_and_map_vm_s2pt_proof.

    Let L : compatlayer (cdata RData) :=
      assign_pfn_to_vm ↦ gensem assign_pfn_to_vm_spec
          ⊕ map_pfn_vm ↦ gensem map_pfn_vm_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_assign_pfn_to_vm: block.
      Hypothesis h_assign_pfn_to_vm_s : Genv.find_symbol ge assign_pfn_to_vm = Some b_assign_pfn_to_vm.
      Hypothesis h_assign_pfn_to_vm_p : Genv.find_funct_ptr ge b_assign_pfn_to_vm
                                        = Some (External (EF_external assign_pfn_to_vm
                                                         (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_map_pfn_vm: block.
      Hypothesis h_map_pfn_vm_s : Genv.find_symbol ge map_pfn_vm = Some b_map_pfn_vm.
      Hypothesis h_map_pfn_vm_p : Genv.find_funct_ptr ge b_map_pfn_vm
                                  = Some (External (EF_external map_pfn_vm
                                                   (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma prot_and_map_vm_s2pt_body_correct:
        forall m d d' env le vmid addr pte level
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (HPTlevel: PTree.get _level le = Some (Vint level))
               (Hinv: high_level_invariant d)
               (Hspec: prot_and_map_vm_s2pt_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) (Int.unsigned level) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) prot_and_map_vm_s2pt_body E0 le' (m, d') Out_normal).
      Proof.
        Local Opaque map_pfn_vm_spec assign_pfn_to_vm_spec.
        Local Hint Unfold phys_page.
        solve_code_proof Hspec prot_and_map_vm_s2pt_body; try solve[eexists; solve_proof_low].
        get_loop_body.
        remember 512 as num.
        remember (PTree.set _num (Vlong (Int64.repr num))
                  (PTree.set _gfn (Vlong (Int64.repr ((Int64.unsigned addr) / 4096 / 512 * 512)))
                   (PTree.set _gfn (Vlong (Int64.repr ((Int64.unsigned addr) / 4096)))
                    (PTree.set _pfn (Vlong (Int64.repr (Z.land (Z.land (Int64.unsigned pte) 281474976710655) 1152921504606842880 / 4096)))
                     (PTree.set _target (Vlong (Int64.repr (Z.land (Z.land (Int64.unsigned pte) 281474976710655) 1152921504606842880))) le)))))
                 as le_loop.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, r) /\ le0 ! _vmid = Some (Vint vmid) /\
                             le0 ! _addr = Some (Vlong addr) /\ le0 ! _pte = Some (Vlong pte) /\
                             le0 ! _level = Some (Vint level)).
        set (Inv := fun le0 m0 n => exists gfn1 pfn1 adt1,
                        prot_and_map_vm_loop (Z.to_nat (num - n)) (Int.unsigned vmid) (Int64.unsigned addr / 4096 / 512 * 512)
                          (Z.land (Z.land (Int64.unsigned pte) 281474976710655) 1152921504606842880 / 4096) d =
                        Some (Int64.unsigned gfn1, Int64.unsigned pfn1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ le0 ! _num = Some (Vlong (Int64.repr n)) /\
                        le0 ! _pfn = Some (Vlong pfn1) /\ le0 ! _gfn = Some (Vlong gfn1) /\ le0 ! _vmid = Some (Vint vmid) /\
                        le0 ! _addr = Some (Vlong addr) /\ le0 ! _pte = Some (Vlong pte) /\ le0 ! _level = Some (Vint level)).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists gfn' pfn' adt',
                    prot_and_map_vm_loop (Z.to_nat (num - Z.of_nat N)) (Int.unsigned vmid) (Int64.unsigned addr / 4096 / 512 * 512)
                      (Z.land (Z.land (Int64.unsigned pte) 281474976710655) 1152921504606842880 / 4096) d =
                    Some (Int64.unsigned gfn', Int64.unsigned pfn', adt')).
        { add_int64 C2 z; try somega. add_int64 C2 z0; try somega.
          induction N. rewrite Z.sub_0_r. rewrite <- Heqnum, C2. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop. simpl_func Hnext.
          add_int64' z1; try somega. add_int64' z2; try somega. repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            add_int64' (Z.land (Z.land (Int64.unsigned pte) 281474976710655) 1152921504606842880 / 4096); try somega.
            add_int64' (Int64.unsigned addr / 4096); try somega.
            rewrite Heqnum, Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
            solve_proof_low. pose proof (int64_bound pte). destruct H; assumption.
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro C'. inversion C'.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite H in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext. inversion Hnext. rewrite H15 in *.
                bool_rel_all. eexists; eexists; split. solve_proof_low.
                exists (n-1). split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]].
              + eexists. eexists. split_and.
                * solve_proof_low.
                * solve_proof_low.
                * intro. unfold Q.
                  assert (n=0) by omega. clear Heqle_loop. subst.
                  sstep. rewrite C2 in H. inv H.
                  split_and; first[reflexivity|solve_proof_low].
                * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ? & ? & ? & ?). rewrite Hm' in exec.
        rewrite Heqnum in *. eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem prot_and_map_vm_s2pt_code_correct:
      spec_le (prot_and_map_vm_s2pt ↦ prot_and_map_vm_s2pt_spec_low) (〚 prot_and_map_vm_s2pt ↦ f_prot_and_map_vm_s2pt 〛 L).
    Proof.
      Local Opaque prot_and_map_vm_s2pt_spec.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (prot_and_map_vm_s2pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_prot_and_map_vm_s2pt ) (Vint vmid :: Vlong addr :: Vlong pte :: Vint level :: nil)
               (create_undef_temps (fn_temps f_prot_and_map_vm_s2pt)))) hinv.
    Qed.

  End prot_and_map_vm_s2pt_proof.

  Section grant_stage2_sg_gpa_proof.

    Let L : compatlayer (cdata RData) :=
      get_level_s2pt ↦ gensem get_level_s2pt_spec
          ⊕ grant_vm_page ↦ gensem grant_vm_page_spec
          ⊕ walk_s2pt ↦ gensem walk_s2pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_level_s2pt: block.
      Hypothesis h_get_level_s2pt_s : Genv.find_symbol ge get_level_s2pt = Some b_get_level_s2pt.
      Hypothesis h_get_level_s2pt_p : Genv.find_funct_ptr ge b_get_level_s2pt
                                      = Some (External (EF_external get_level_s2pt
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tuint cc_default).
      Variable b_grant_vm_page: block.
      Hypothesis h_grant_vm_page_s : Genv.find_symbol ge grant_vm_page = Some b_grant_vm_page.
      Hypothesis h_grant_vm_page_p : Genv.find_funct_ptr ge b_grant_vm_page
                                     = Some (External (EF_external grant_vm_page
                                                      (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_walk_s2pt: block.
      Hypothesis h_walk_s2pt_s : Genv.find_symbol ge walk_s2pt = Some b_walk_s2pt.
      Hypothesis h_walk_s2pt_p : Genv.find_funct_ptr ge b_walk_s2pt
                                 = Some (External (EF_external walk_s2pt
                                                  (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).

      Lemma grant_stage2_sg_gpa_body_correct:
        forall m d d' env le vmid addr size
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTsize: PTree.get _size le = Some (Vlong size))
               (Hinv: high_level_invariant d)
               (Hspec: grant_stage2_sg_gpa_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned size)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) grant_stage2_sg_gpa_body E0 le' (m, d') Out_normal).
      Proof.
        Local Hint Unfold phys_page.
        Local Opaque walk_s2pt_spec get_level_s2pt_spec grant_vm_page_spec.
        solve_code_proof Hspec grant_stage2_sg_gpa_body.
        get_loop_body.
        assert(0 <= (Int64.unsigned size + 4095) / 4096 <= Int64.max_unsigned) by somega.
        remember ((Int64.unsigned size  + 4095) / 4096) as num.
        remember (PTree.set _num (Vlong (Int64.repr ((Int64.unsigned size + 4095) / 4096))) le) as le_loop.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, d') /\ le0 ! _vmid = Some (Vint vmid)).
        set (Inv := fun le0 m0 n => exists addr1 adt1,
                        grant_stage2_loop (Z.to_nat (num - n)) (Int.unsigned vmid) (Int64.unsigned addr) d =
                        Some (Int64.unsigned addr1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ le0 ! _num = Some (Vlong (Int64.repr n)) /\
                        le0 ! _addr = Some (Vlong addr1) /\ le0 ! _vmid = Some (Vint vmid)).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists addr' adt',
                    grant_stage2_loop (Z.to_nat (num - Z.of_nat N)) (Int.unsigned vmid) (Int64.unsigned addr) d =
                    Some (Int64.unsigned addr', adt')).
        { add_int64 C2 z; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C2. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; add_int64' z0; try somega; repeat eexists; reflexivity. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            rewrite Heqnum, Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro C'. inversion C'.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite H0 in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext; bool_rel_all; inversion Hnext.
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
              + eexists. eexists. split_and.
                * solve_proof_low.
                * solve_proof_low.
                * intro. unfold Q.
                  assert (n=0) by omega. clear Heqle_loop. subst.
                  sstep. rewrite C2 in H0. inv H0.
                  split_and; first[reflexivity|solve_proof_low].
                * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ?). rewrite Hm' in exec.
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem grant_stage2_sg_gpa_code_correct:
      spec_le (grant_stage2_sg_gpa ↦ grant_stage2_sg_gpa_spec_low) (〚 grant_stage2_sg_gpa ↦ f_grant_stage2_sg_gpa 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (grant_stage2_sg_gpa_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_grant_stage2_sg_gpa ) (Vint vmid :: Vlong addr :: Vlong size :: nil)
               (create_undef_temps (fn_temps f_grant_stage2_sg_gpa)))) hinv.
    Qed.

  End grant_stage2_sg_gpa_proof.

  Section revoke_stage2_sg_gpa_proof.

    Let L : compatlayer (cdata RData) :=
      revoke_vm_page ↦ gensem revoke_vm_page_spec
          ⊕ get_level_s2pt ↦ gensem get_level_s2pt_spec
          ⊕ walk_s2pt ↦ gensem walk_s2pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_revoke_vm_page: block.
      Hypothesis h_revoke_vm_page_s : Genv.find_symbol ge revoke_vm_page = Some b_revoke_vm_page.
      Hypothesis h_revoke_vm_page_p : Genv.find_funct_ptr ge b_revoke_vm_page
                                      = Some (External (EF_external revoke_vm_page
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_get_level_s2pt: block.
      Hypothesis h_get_level_s2pt_s : Genv.find_symbol ge get_level_s2pt = Some b_get_level_s2pt.
      Hypothesis h_get_level_s2pt_p : Genv.find_funct_ptr ge b_get_level_s2pt
                                      = Some (External (EF_external get_level_s2pt
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tuint cc_default).
      Variable b_walk_s2pt: block.
      Hypothesis h_walk_s2pt_s : Genv.find_symbol ge walk_s2pt = Some b_walk_s2pt.
      Hypothesis h_walk_s2pt_p : Genv.find_funct_ptr ge b_walk_s2pt
                                 = Some (External (EF_external walk_s2pt
                                                  (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).

      Lemma revoke_stage2_sg_gpa_body_correct:
        forall m d d' env le vmid addr size
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTsize: PTree.get _size le = Some (Vlong size))
               (Hinv: high_level_invariant d)
               (Hspec: revoke_stage2_sg_gpa_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned size)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) revoke_stage2_sg_gpa_body E0 le' (m, d') Out_normal).
      Proof.
        Local Hint Unfold phys_page.
        Local Opaque walk_s2pt_spec get_level_s2pt_spec revoke_vm_page_spec.
        solve_code_proof Hspec revoke_stage2_sg_gpa_body.
        get_loop_body.
        assert(0 <= (Int64.unsigned size + 4095) / 4096 <= Int64.max_unsigned) by somega.
        remember ((Int64.unsigned size  + 4095) / 4096) as num.
        remember (PTree.set _num (Vlong (Int64.repr ((Int64.unsigned size + 4095) / 4096))) le) as le_loop.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, d') /\ le0 ! _vmid = Some (Vint vmid)).
        set (Inv := fun le0 m0 n => exists addr1 adt1,
                        revoke_stage2_loop (Z.to_nat (num - n)) (Int.unsigned vmid) (Int64.unsigned addr) d =
                        Some (Int64.unsigned addr1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ le0 ! _num = Some (Vlong (Int64.repr n)) /\
                        le0 ! _addr = Some (Vlong addr1) /\ le0 ! _vmid = Some (Vint vmid)).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists addr' adt',
                    revoke_stage2_loop (Z.to_nat (num - Z.of_nat N)) (Int.unsigned vmid) (Int64.unsigned addr) d =
                    Some (Int64.unsigned addr', adt')).
        { add_int64 C2 z; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C2. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; add_int64' z0; try somega; repeat eexists; reflexivity. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            rewrite Heqnum, Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro C'. inversion C'.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite H0 in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext; bool_rel_all; inversion Hnext.
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                rewrite H9, H10 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
              + eexists. eexists. split_and.
                * solve_proof_low.
                * solve_proof_low.
                * intro. unfold Q.
                  assert (n=0) by omega. clear Heqle_loop. subst.
                  sstep. rewrite C2 in H0. inv H0.
                  split_and; first[reflexivity|solve_proof_low].
                * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ?). rewrite Hm' in exec.
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem revoke_stage2_sg_gpa_code_correct:
      spec_le (revoke_stage2_sg_gpa ↦ revoke_stage2_sg_gpa_spec_low) (〚 revoke_stage2_sg_gpa ↦ f_revoke_stage2_sg_gpa 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (revoke_stage2_sg_gpa_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_revoke_stage2_sg_gpa ) (Vint vmid :: Vlong addr :: Vlong size :: nil)
               (create_undef_temps (fn_temps f_revoke_stage2_sg_gpa)))) hinv.
    Qed.

  End revoke_stage2_sg_gpa_proof.

End MemoryOpsProofLow.
```
