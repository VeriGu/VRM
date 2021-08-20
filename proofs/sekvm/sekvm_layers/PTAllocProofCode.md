# PTAllocProofCode

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

Require Import Ident.
Require Import AbstractMachine.Layer.
Require Import PTAlloc.Code.
Require Import HypsecCommLib.
Require Import Constants.
Require Import PTAlloc.Spec.
Require Import AbstractMachine.Spec.
Require Import RData.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PTAllocProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section memcpy_proof.

    Let L : compatlayer (cdata RData) := ∅.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Definition _dest : ident := 53%positive.
    Definition _len : ident := 55%positive.
    Definition _main : ident := 58%positive.
    Definition _memcpy : ident := 57%positive.
    Definition _src : ident := 54%positive.
    Definition _t'1 : ident := 59%positive.
    Definition _t'2 : ident := 60%positive.

    Require Import Coqlib.
    Require Import AST.
    Require Import Integers.
    Require Import Values.
    Require Import Cop.
    Require Import Clight.
    Require Import CDataTypes.
    Require Import Ctypes.

    Definition memcpy_body :=
      (Swhile
        (Ebinop Ogt (Etempvar _len tulong) (Econst_long (Int64.repr 0) tulong)
          tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Etempvar _dest (tptr tuchar)))
                  (Sset _dest
                    (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                      (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                (Sset _t'2 (Etempvar _src (tptr tuchar))))
              (Sset _src
                (Ebinop Oadd (Etempvar _t'2 (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar))))
            (Sassign (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar)
              (Ederef (Etempvar _t'2 (tptr tuchar)) tuchar)))
          (Sset _len
            (Ebinop Osub (Etempvar _len tulong) (Econst_long (Int64.repr 1) tulong)
              tulong)))).

    Context `{Hwb: WritableBlockAllowGlobals}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Fixpoint memcpy_loop n b ofs b' ofs' m :=
      match n with
      | O => Some (ofs, ofs', m)
      | S n' =>
        match memcpy_loop n' b ofs b' ofs' m with
        | Some (ofs1, ofs1', m1) =>
          rely is_int ofs1; rely is_int ofs1';
          match Mem.load Mint8unsigned m1 b' ofs1' with
          | Some (Vint val) =>
            match Mem.store Mint8unsigned m1 b ofs1 (Vint val) with
            | Some m2 =>
              Some (ofs1 + 1, ofs1' + 1, m2)
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      end.

    Definition memcpy_spec b ofs b' ofs' len m :=
      rely is_int ofs; rely is_int ofs'; rely is_int len; rely is_int (ofs + len); rely is_int (ofs' + len);
      match memcpy_loop (Z.to_nat len) b ofs b' ofs' m with
      | Some (ofs1, ofs1', m') =>
        rely is_int ofs1; rely is_int ofs1';
        Some m'
      | _ => None
      end.

    Lemma memcpy_correct:
      forall m m' (d: RData) env le src_b src_offset dst_b dst_offset len src_a dst_a
              (Henv: env = PTree.empty _)
              (Hsrc: PTree.get _src le = Some (Vptr src_b src_offset))
              (Hdst: PTree.get _dest le = Some (Vptr dst_b dst_offset))
              (Hlen: PTree.get _len le = Some (Vlong len))
              (Hsrcarr: Genv.find_symbol ge src_a = Some src_b)
              (Hdstarr: Genv.find_symbol ge dst_a = Some dst_b)
              (Hspec: memcpy_spec dst_b (Int.unsigned dst_offset) src_b (Int.unsigned src_offset) (Int64.unsigned len) m = Some m'),
            exists le', (exec_stmt ge env le ((m, d): mem) memcpy_body E0 le' (m', d) Out_normal).
    Proof.
      solve_code_proof Hspec memcpy_body.
      get_loop_body. clear_hyp.
      remember (Int64.unsigned len) as num0.
      remember (PTree.set _i (Vlong (cast_int_long Unsigned (Int.repr 0))) le) as le_loop.
      set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le).
      set (Q := fun (le0: temp_env) m0 => m0 = (m', d)).
      set (Inv := fun le0 m0 n => exists ofs1 ofs1' m1',
                      memcpy_loop (Z.to_nat (num0 - n)) dst_b (Int.unsigned dst_offset) src_b (Int.unsigned src_offset) m = Some (Int.unsigned ofs1, Int.unsigned ofs1', m1') /\
                      m0 = (m1', d) /\ 0 <= n /\ n <= num0 /\ le0 ! _src = Some (Vptr src_b ofs1') /\
                      le0 ! _dest = Some (Vptr dst_b ofs1) /\ le0 ! _len = Some (Vlong (Int64.repr n))).
      assert(loop_succ: forall N, Z.of_nat N <= num0 -> exists ofs1 ofs1' m1',
                  memcpy_loop (Z.to_nat (num0 - Z.of_nat N)) dst_b (Int.unsigned dst_offset) src_b (Int.unsigned src_offset) m = Some (Int.unsigned ofs1, Int.unsigned ofs1', m1')).
      { add_int C4 z; try somega. add_int C4 z0; try somega.
        induction N. rewrite Z.sub_0_r. rewrite C4. intros. repeat eexists; reflexivity.
        intros. erewrite loop_ind_sub1 in IHN; try omega.
        rewrite Nat2Z.inj_succ, succ_plus_1 in H.
        assert(Z.of_nat N <= num0) by omega.
        apply IHN in H0. destruct H0 as (? & ? & ? & ?).
        Local Transparent memcpy_loop. Local Opaque Z.of_nat. simpl in H0.
        autounfold in H0; repeat simpl_hyp H0; bool_rel_all0.
        bool_rel_all0. add_int' z1; somega. add_int' z2; somega.  repeat eexists. }
      assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
      { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
        - apply Zwf_well_founded.
        - unfold P, Inv. intros ? ? C. destruct C as [C C'].
          rewrite C' in *. exists num0.
          replace (num0 - num0) with 0 by omega. simpl. add_int64' 0; try somega.
          rewrite Heqnum0. repeat eexists; first [reflexivity|assumption|solve_proof_low].
        - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
          rewrite Heqbody, Heqcond in *.
          destruct (n >? 0) eqn:Hn; bool_rel.
          + eexists. eexists. repeat split.
            * solve_proof_low.
            * solve_proof_low.
            * intro C. inversion C.
            * assert(Z.of_nat (Z.to_nat (n-1)) <= num0) by (rewrite Z2Nat.id; omega).
              apply loop_succ in H6. rewrite Z2Nat.id in H6; try omega.
              intro. destruct H6 as (? & ? & ? & ?). duplicate H6.
              rewrite loop_nat_sub1 in H6; try somega.
              simpl in H6. rewrite H in H6.
              autounfold in H6; repeat simpl_hyp H6; contra. inversion H6. rewrite H11 in *.
              duplicate C1. apply Mem.load_cast in D0.
              bool_rel_all. eexists; eexists; split. solve_proof_low; simpl; try omega.
              unfold lift. simpl. rewrite H0. simpl. apply C1.
              unfold sem_cast; simpl. unfold Val.zero_ext in D0. rewrite <- D0. reflexivity.
              unfold lift; simpl. rewrite H0. simpl. rewrite C3. reflexivity.
              replace (sizeof tuchar * 1) with 1 by reflexivity. rewrite H9, H10.
              exists (n-1). split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]].
              rewrite H0. reflexivity.
          + eexists. eexists. repeat split.
            * solve_proof_low.
            * solve_proof_low.
            * intro. unfold Q.
              assert (n=0) by omega. rewrite H7 in H. rewrite Z.sub_0_r in H.
              rewrite C4 in H. inversion H. assumption.
            * intro C. inversion C. }
      assert (Pre: P le (m, d)) by (split; reflexivity).
      pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre).
      destruct H as (le' & m0 & (exec & Post)).
      unfold exec_stmt in exec.
      unfold Q in Post. rewrite Post in exec.
      eexists; solve_proof_low.
    Qed.

  End memcpy_proof.

  Section alloc_pgd_page_proof.

    Let L : compatlayer (cdata RData) :=
      get_pgd_next ↦ gensem get_pgd_next_spec
          ⊕ set_pgd_next ↦ gensem set_pgd_next_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pgd_next: block.
      Hypothesis h_get_pgd_next_s : Genv.find_symbol ge get_pgd_next = Some b_get_pgd_next.
      Hypothesis h_get_pgd_next_p : Genv.find_funct_ptr ge b_get_pgd_next
                                    = Some (External (EF_external get_pgd_next
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_set_pgd_next: block.
      Hypothesis h_set_pgd_next_s : Genv.find_symbol ge set_pgd_next = Some b_set_pgd_next.
      Hypothesis h_set_pgd_next_p : Genv.find_funct_ptr ge b_set_pgd_next
                                    = Some (External (EF_external set_pgd_next
                                                     (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma alloc_pgd_page_body_correct:
        forall m d d' env le vmid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: alloc_pgd_page_spec0 (Int.unsigned vmid) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_pgd_page_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_pgd_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_pgd_page_code_correct:
      spec_le (alloc_pgd_page ↦ alloc_pgd_page_spec_low) (〚 alloc_pgd_page ↦ f_alloc_pgd_page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_pgd_page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_pgd_page ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_alloc_pgd_page)))) hinv.
    Qed.

  End alloc_pgd_page_proof.

  Section alloc_pud_page_proof.

    Let L : compatlayer (cdata RData) :=
      get_pud_next ↦ gensem get_pud_next_spec
          ⊕ set_pud_next ↦ gensem set_pud_next_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pud_next: block.
      Hypothesis h_get_pud_next_s : Genv.find_symbol ge get_pud_next = Some b_get_pud_next.
      Hypothesis h_get_pud_next_p : Genv.find_funct_ptr ge b_get_pud_next
                                    = Some (External (EF_external get_pud_next
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_set_pud_next: block.
      Hypothesis h_set_pud_next_s : Genv.find_symbol ge set_pud_next = Some b_set_pud_next.
      Hypothesis h_set_pud_next_p : Genv.find_funct_ptr ge b_set_pud_next
                                    = Some (External (EF_external set_pud_next
                                                     (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma alloc_pud_page_body_correct:
        forall m d d' env le vmid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: alloc_pud_page_spec0 (Int.unsigned vmid) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_pud_page_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_pud_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_pud_page_code_correct:
      spec_le (alloc_pud_page ↦ alloc_pud_page_spec_low) (〚 alloc_pud_page ↦ f_alloc_pud_page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_pud_page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_pud_page ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_alloc_pud_page)))) hinv.
    Qed.

  End alloc_pud_page_proof.

  Section alloc_pmd_page_proof.

    Let L : compatlayer (cdata RData) :=
      get_pmd_next ↦ gensem get_pmd_next_spec
          ⊕ set_pmd_next ↦ gensem set_pmd_next_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pmd_next: block.
      Hypothesis h_get_pmd_next_s : Genv.find_symbol ge get_pmd_next = Some b_get_pmd_next.
      Hypothesis h_get_pmd_next_p : Genv.find_funct_ptr ge b_get_pmd_next
                                    = Some (External (EF_external get_pmd_next
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_set_pmd_next: block.
      Hypothesis h_set_pmd_next_s : Genv.find_symbol ge set_pmd_next = Some b_set_pmd_next.
      Hypothesis h_set_pmd_next_p : Genv.find_funct_ptr ge b_set_pmd_next
                                    = Some (External (EF_external set_pmd_next
                                                     (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma alloc_pmd_page_body_correct:
        forall m d d' env le vmid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: alloc_pmd_page_spec0 (Int.unsigned vmid) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_pmd_page_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_pmd_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_pmd_page_code_correct:
      spec_le (alloc_pmd_page ↦ alloc_pmd_page_spec_low) (〚 alloc_pmd_page ↦ f_alloc_pmd_page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_pmd_page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_pmd_page ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_alloc_pmd_page)))) hinv.
    Qed.

  End alloc_pmd_page_proof.

End PTAllocProofLow.

```
