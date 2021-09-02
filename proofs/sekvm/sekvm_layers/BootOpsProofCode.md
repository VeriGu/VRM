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

Require Import NPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import MemManager.Spec.
Require Import Ident.
Require Import BootAux.Spec.
Require Import MmioSPTOps.Spec.
Require Import BootOps.Code.
Require Import RData.
Require Import BootAux.Layer.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import BootCore.Spec.
Require Import PageManager.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section BootOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section search_load_info_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_remap_addr ↦ gensem get_vm_remap_addr_spec
          ⊕ get_vm_load_addr ↦ gensem get_vm_load_addr_spec
          ⊕ get_vm_next_load_idx ↦ gensem get_vm_next_load_idx_spec
          ⊕ get_vm_load_size ↦ gensem get_vm_load_size_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_remap_addr: block.
      Hypothesis h_get_vm_remap_addr_s : Genv.find_symbol ge get_vm_remap_addr = Some b_get_vm_remap_addr.
      Hypothesis h_get_vm_remap_addr_p : Genv.find_funct_ptr ge b_get_vm_remap_addr
                                         = Some (External (EF_external get_vm_remap_addr
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_vm_load_addr: block.
      Hypothesis h_get_vm_load_addr_s : Genv.find_symbol ge get_vm_load_addr = Some b_get_vm_load_addr.
      Hypothesis h_get_vm_load_addr_p : Genv.find_funct_ptr ge b_get_vm_load_addr
                                        = Some (External (EF_external get_vm_load_addr
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_vm_next_load_idx: block.
      Hypothesis h_get_vm_next_load_idx_s : Genv.find_symbol ge get_vm_next_load_idx = Some b_get_vm_next_load_idx.
      Hypothesis h_get_vm_next_load_idx_p : Genv.find_funct_ptr ge b_get_vm_next_load_idx
                                            = Some (External (EF_external get_vm_next_load_idx
                                                             (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                   (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vm_load_size: block.
      Hypothesis h_get_vm_load_size_s : Genv.find_symbol ge get_vm_load_size = Some b_get_vm_load_size.
      Hypothesis h_get_vm_load_size_p : Genv.find_funct_ptr ge b_get_vm_load_size
                                        = Some (External (EF_external get_vm_load_size
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma search_load_info_body_correct:
        forall m d d' env le vmid addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: search_load_info_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) search_load_info_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        Local Opaque acquire_lock_vm_spec release_lock_vm_spec get_vm_remap_addr_spec get_vm_load_addr_spec
                     get_vm_next_load_idx_spec get_vm_load_size_spec panic_spec check64_spec.
        solve_code_proof Hspec search_load_info_body; try solve[eexists; solve_proof_low].
        get_loop_body.
        remember
          (PTree.set _ret (Vlong (Int64.repr 0))
              (PTree.set _load_idx (Vint (Int.repr 0))
                (PTree.set _num (Vint (Int.repr z))
                    (set_opttemp (Some _t'1) (Vint (Int.repr z)) (set_opttemp None Vundef le)))))
          as le_loop.
        set (P := fun le0 m0 => m0 = (m, r) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, r) /\ le0 ! _vmid = Some (Vint vmid) /\ le0 ! _ret = Some (Vlong (Int64.repr z1))).
        set (Inv := fun le0 m0 n => exists idx1 ret1,
                        search_load_info_loop0 (Z.to_nat (z - n)) 0 (Int.unsigned vmid) (Int64.unsigned addr) 0 r =
                        Some (Int.unsigned idx1, Int64.unsigned ret1) /\
                        m0 = (m, r) /\ 0 <= n /\ n <= z /\ le0 ! _num = Some (Vint (Int.repr n)) /\ le0 ! _load_idx = Some (Vint idx1) /\
                        le0 ! _vmid = Some (Vint vmid) /\ le0 ! _ret = Some (Vlong ret1) /\ le0 ! _addr = Some (Vlong addr)).
        assert(loop_succ: forall N, Z.of_nat N <= z -> exists idx' ret',
                    search_load_info_loop0 (Z.to_nat (z - Z.of_nat N)) 0 (Int.unsigned vmid) (Int64.unsigned addr) 0 r =
                    Some (Int.unsigned idx', Int64.unsigned ret')).
        { add_int C4 z0; try somega. add_int64 C4 z1; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C4. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= z) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; add_int' z2; try somega; try add_int64' z3; try somega; repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists z.
            replace (z - z) with 0 by omega. simpl.
            rewrite Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
            add_int' 0; try somega. reflexivity.
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro C'. inversion C'.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= z) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite H in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext; bool_rel_all; contra; inversion Hnext.
                rewrite H10, H11 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                apply int64_eq_Z in H11. rewrite H10, H11 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                apply int64_eq_Z in H11. rewrite H10, H11 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                apply int64_eq_Z in H11. rewrite H10, H11 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro. unfold Q.
                assert (n=0) by omega. clear Heqle_loop. subst.
                sstep. rewrite C4 in H. inv H.
                split_and; first[reflexivity|solve_proof_low].
              * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, r)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, r) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ? & ?). rewrite Hm' in exec.
        rewrite Heqbody, Heqcond, Heqle_loop in *.
        eexists; solve_proof_low.
        Grab Existential Variables. apply m0. apply le0.
      Qed.

    End BodyProof.

  End search_load_info_proof.

  Section set_vcpu_active_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vcpu_state ↦ gensem get_vcpu_state_spec
          ⊕ set_vcpu_state ↦ gensem set_vcpu_state_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vcpu_state: block.
      Hypothesis h_get_vcpu_state_s : Genv.find_symbol ge get_vcpu_state = Some b_get_vcpu_state.
      Hypothesis h_get_vcpu_state_p : Genv.find_funct_ptr ge b_get_vcpu_state
                                      = Some (External (EF_external get_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_set_vcpu_state: block.
      Hypothesis h_set_vcpu_state_s : Genv.find_symbol ge set_vcpu_state = Some b_set_vcpu_state.
      Hypothesis h_set_vcpu_state_p : Genv.find_funct_ptr ge b_set_vcpu_state
                                      = Some (External (EF_external set_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                             (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma set_vcpu_active_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: set_vcpu_active_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_vcpu_active_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_vcpu_active_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_vcpu_active_proof.

  Section set_vcpu_inactive_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vcpu_state ↦ gensem get_vcpu_state_spec
          ⊕ set_vcpu_state ↦ gensem set_vcpu_state_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vcpu_state: block.
      Hypothesis h_get_vcpu_state_s : Genv.find_symbol ge get_vcpu_state = Some b_get_vcpu_state.
      Hypothesis h_get_vcpu_state_p : Genv.find_funct_ptr ge b_get_vcpu_state
                                      = Some (External (EF_external get_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_set_vcpu_state: block.
      Hypothesis h_set_vcpu_state_s : Genv.find_symbol ge set_vcpu_state = Some b_set_vcpu_state.
      Hypothesis h_set_vcpu_state_p : Genv.find_funct_ptr ge b_set_vcpu_state
                                      = Some (External (EF_external set_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                             (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma set_vcpu_inactive_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: set_vcpu_inactive_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_vcpu_inactive_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_vcpu_inactive_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_vcpu_inactive_proof.

  Section register_vcpu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vcpu_state ↦ gensem get_vcpu_state_spec
          ⊕ get_shared_vcpu ↦ gensem get_shared_vcpu_spec
          ⊕ set_vm_vcpu ↦ gensem set_vm_vcpu_spec
          ⊕ set_vcpu_state ↦ gensem set_vcpu_state_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vcpu_state: block.
      Hypothesis h_get_vcpu_state_s : Genv.find_symbol ge get_vcpu_state = Some b_get_vcpu_state.
      Hypothesis h_get_vcpu_state_p : Genv.find_funct_ptr ge b_get_vcpu_state
                                      = Some (External (EF_external get_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_get_shared_vcpu: block.
      Hypothesis h_get_shared_vcpu_s : Genv.find_symbol ge get_shared_vcpu = Some b_get_shared_vcpu.
      Hypothesis h_get_shared_vcpu_p : Genv.find_funct_ptr ge b_get_shared_vcpu
                                       = Some (External (EF_external get_shared_vcpu
                                                        (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                              (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_set_vm_vcpu: block.
      Hypothesis h_set_vm_vcpu_s : Genv.find_symbol ge set_vm_vcpu = Some b_set_vm_vcpu.
      Hypothesis h_set_vm_vcpu_p : Genv.find_funct_ptr ge b_set_vm_vcpu
                                   = Some (External (EF_external set_vm_vcpu
                                                    (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_vcpu_state: block.
      Hypothesis h_set_vcpu_state_s : Genv.find_symbol ge set_vcpu_state = Some b_set_vcpu_state.
      Hypothesis h_set_vcpu_state_p : Genv.find_funct_ptr ge b_set_vcpu_state
                                      = Some (External (EF_external set_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                             (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma register_vcpu_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: register_vcpu_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) register_vcpu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec register_vcpu_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End register_vcpu_proof.

  Section register_kvm_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ gen_vmid ↦ gensem gen_vmid_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ set_vm_state ↦ gensem set_vm_state_spec
          ⊕ get_shared_kvm ↦ gensem get_shared_kvm_spec
          ⊕ set_vm_kvm ↦ gensem set_vm_kvm_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_gen_vmid: block.
      Hypothesis h_gen_vmid_s : Genv.find_symbol ge gen_vmid = Some b_gen_vmid.
      Hypothesis h_gen_vmid_p : Genv.find_funct_ptr ge b_gen_vmid
                                = Some (External (EF_external gen_vmid
                                                 (signature_of_type Tnil tuint cc_default))
                                       Tnil tuint cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_set_vm_state: block.
      Hypothesis h_set_vm_state_s : Genv.find_symbol ge set_vm_state = Some b_set_vm_state.
      Hypothesis h_set_vm_state_p : Genv.find_funct_ptr ge b_set_vm_state
                                    = Some (External (EF_external set_vm_state
                                                     (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_get_shared_kvm: block.
      Hypothesis h_get_shared_kvm_s : Genv.find_symbol ge get_shared_kvm = Some b_get_shared_kvm.
      Hypothesis h_get_shared_kvm_p : Genv.find_funct_ptr ge b_get_shared_kvm
                                      = Some (External (EF_external get_shared_kvm
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
      Variable b_set_vm_kvm: block.
      Hypothesis h_set_vm_kvm_s : Genv.find_symbol ge set_vm_kvm = Some b_set_vm_kvm.
      Hypothesis h_set_vm_kvm_p : Genv.find_funct_ptr ge b_set_vm_kvm
                                  = Some (External (EF_external set_vm_kvm
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma register_kvm_body_correct:
        forall m d d' env le  res
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: register_kvm_spec0  d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) register_kvm_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec register_kvm_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End register_kvm_proof.

  Section set_boot_info_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vm_next_load_idx ↦ gensem get_vm_next_load_idx_spec
          ⊕ alloc_remap_addr ↦ gensem alloc_remap_addr_spec
          ⊕ set_vm_next_load_idx ↦ gensem set_vm_next_load_idx_spec
          ⊕ set_vm_load_addr ↦ gensem set_vm_load_addr_spec
          ⊕ set_vm_load_size ↦ gensem set_vm_load_size_spec
          ⊕ set_vm_remap_addr ↦ gensem set_vm_remap_addr_spec
          ⊕ set_vm_mapped_pages ↦ gensem set_vm_mapped_pages_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vm_next_load_idx: block.
      Hypothesis h_get_vm_next_load_idx_s : Genv.find_symbol ge get_vm_next_load_idx = Some b_get_vm_next_load_idx.
      Hypothesis h_get_vm_next_load_idx_p : Genv.find_funct_ptr ge b_get_vm_next_load_idx
                                            = Some (External (EF_external get_vm_next_load_idx
                                                             (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                   (Tcons tuint Tnil) tuint cc_default).
      Variable b_alloc_remap_addr: block.
      Hypothesis h_alloc_remap_addr_s : Genv.find_symbol ge alloc_remap_addr = Some b_alloc_remap_addr.
      Hypothesis h_alloc_remap_addr_p : Genv.find_funct_ptr ge b_alloc_remap_addr
                                        = Some (External (EF_external alloc_remap_addr
                                                         (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                               (Tcons tulong Tnil) tulong cc_default).
      Variable b_set_vm_next_load_idx: block.
      Hypothesis h_set_vm_next_load_idx_s : Genv.find_symbol ge set_vm_next_load_idx = Some b_set_vm_next_load_idx.
      Hypothesis h_set_vm_next_load_idx_p : Genv.find_funct_ptr ge b_set_vm_next_load_idx
                                            = Some (External (EF_external set_vm_next_load_idx
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_vm_load_addr: block.
      Hypothesis h_set_vm_load_addr_s : Genv.find_symbol ge set_vm_load_addr = Some b_set_vm_load_addr.
      Hypothesis h_set_vm_load_addr_p : Genv.find_funct_ptr ge b_set_vm_load_addr
                                        = Some (External (EF_external set_vm_load_addr
                                                         (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_vm_load_size: block.
      Hypothesis h_set_vm_load_size_s : Genv.find_symbol ge set_vm_load_size = Some b_set_vm_load_size.
      Hypothesis h_set_vm_load_size_p : Genv.find_funct_ptr ge b_set_vm_load_size
                                        = Some (External (EF_external set_vm_load_size
                                                         (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_vm_remap_addr: block.
      Hypothesis h_set_vm_remap_addr_s : Genv.find_symbol ge set_vm_remap_addr = Some b_set_vm_remap_addr.
      Hypothesis h_set_vm_remap_addr_p : Genv.find_funct_ptr ge b_set_vm_remap_addr
                                         = Some (External (EF_external set_vm_remap_addr
                                                          (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_vm_mapped_pages: block.
      Hypothesis h_set_vm_mapped_pages_s : Genv.find_symbol ge set_vm_mapped_pages = Some b_set_vm_mapped_pages.
      Hypothesis h_set_vm_mapped_pages_p : Genv.find_funct_ptr ge b_set_vm_mapped_pages
                                           = Some (External (EF_external set_vm_mapped_pages
                                                            (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                  (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma set_boot_info_body_correct:
        forall m d d' env le vmid load_addr size res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTload_addr: PTree.get _load_addr le = Some (Vlong load_addr))
               (HPTsize: PTree.get _size le = Some (Vlong size))
               (Hinv: high_level_invariant d)
               (Hspec: set_boot_info_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned load_addr)) (VZ64 (Int64.unsigned size)) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) set_boot_info_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec set_boot_info_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_boot_info_proof.

  Section remap_vm_image_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_remap_addr ↦ gensem get_vm_remap_addr_spec
          ⊕ get_vm_mapped_pages ↦ gensem get_vm_mapped_pages_spec
          ⊕ set_vm_mapped_pages ↦ gensem set_vm_mapped_pages_spec
          ⊕ get_vm_next_load_idx ↦ gensem get_vm_next_load_idx_spec
          ⊕ map_s2pt ↦ gensem map_s2pt_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vm_load_size ↦ gensem get_vm_load_size_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_remap_addr: block.
      Hypothesis h_get_vm_remap_addr_s : Genv.find_symbol ge get_vm_remap_addr = Some b_get_vm_remap_addr.
      Hypothesis h_get_vm_remap_addr_p : Genv.find_funct_ptr ge b_get_vm_remap_addr
                                         = Some (External (EF_external get_vm_remap_addr
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_vm_mapped_pages: block.
      Hypothesis h_get_vm_mapped_pages_s : Genv.find_symbol ge get_vm_mapped_pages = Some b_get_vm_mapped_pages.
      Hypothesis h_get_vm_mapped_pages_p : Genv.find_funct_ptr ge b_get_vm_mapped_pages
                                           = Some (External (EF_external get_vm_mapped_pages
                                                            (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                  (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_set_vm_mapped_pages: block.
      Hypothesis h_set_vm_mapped_pages_s : Genv.find_symbol ge set_vm_mapped_pages = Some b_set_vm_mapped_pages.
      Hypothesis h_set_vm_mapped_pages_p : Genv.find_funct_ptr ge b_set_vm_mapped_pages
                                           = Some (External (EF_external set_vm_mapped_pages
                                                            (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                  (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_get_vm_next_load_idx: block.
      Hypothesis h_get_vm_next_load_idx_s : Genv.find_symbol ge get_vm_next_load_idx = Some b_get_vm_next_load_idx.
      Hypothesis h_get_vm_next_load_idx_p : Genv.find_funct_ptr ge b_get_vm_next_load_idx
                                            = Some (External (EF_external get_vm_next_load_idx
                                                             (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                   (Tcons tuint Tnil) tuint cc_default).
      Variable b_map_s2pt: block.
      Hypothesis h_map_s2pt_s : Genv.find_symbol ge map_s2pt = Some b_map_s2pt.
      Hypothesis h_map_s2pt_p : Genv.find_funct_ptr ge b_map_s2pt
                                = Some (External (EF_external map_s2pt
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vm_load_size: block.
      Hypothesis h_get_vm_load_size_s : Genv.find_symbol ge get_vm_load_size = Some b_get_vm_load_size.
      Hypothesis h_get_vm_load_size_p : Genv.find_funct_ptr ge b_get_vm_load_size
                                        = Some (External (EF_external get_vm_load_size
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma remap_vm_image_body_correct:
        forall m d d' env le vmid pfn load_idx
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTload_idx: PTree.get _load_idx le = Some (Vint load_idx))
               (Hinv: high_level_invariant d)
               (Hspec: remap_vm_image_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (Int.unsigned load_idx) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) remap_vm_image_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec remap_vm_image_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End remap_vm_image_proof.

  Section verify_and_load_images_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vm_next_load_idx ↦ gensem get_vm_next_load_idx_spec
          ⊕ get_vm_load_addr ↦ gensem get_vm_load_addr_spec
          ⊕ get_vm_remap_addr ↦ gensem get_vm_remap_addr_spec
          ⊕ get_vm_mapped_pages ↦ gensem get_vm_mapped_pages_spec
          ⊕ unmap_and_load_vm_image ↦ gensem unmap_and_load_vm_image_spec
          ⊕ verify_image ↦ gensem verify_image_spec
          ⊕ set_vm_state ↦ gensem set_vm_state_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vm_next_load_idx: block.
      Hypothesis h_get_vm_next_load_idx_s : Genv.find_symbol ge get_vm_next_load_idx = Some b_get_vm_next_load_idx.
      Hypothesis h_get_vm_next_load_idx_p : Genv.find_funct_ptr ge b_get_vm_next_load_idx
                                            = Some (External (EF_external get_vm_next_load_idx
                                                             (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                   (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vm_load_addr: block.
      Hypothesis h_get_vm_load_addr_s : Genv.find_symbol ge get_vm_load_addr = Some b_get_vm_load_addr.
      Hypothesis h_get_vm_load_addr_p : Genv.find_funct_ptr ge b_get_vm_load_addr
                                        = Some (External (EF_external get_vm_load_addr
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_vm_remap_addr: block.
      Hypothesis h_get_vm_remap_addr_s : Genv.find_symbol ge get_vm_remap_addr = Some b_get_vm_remap_addr.
      Hypothesis h_get_vm_remap_addr_p : Genv.find_funct_ptr ge b_get_vm_remap_addr
                                         = Some (External (EF_external get_vm_remap_addr
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_vm_mapped_pages: block.
      Hypothesis h_get_vm_mapped_pages_s : Genv.find_symbol ge get_vm_mapped_pages = Some b_get_vm_mapped_pages.
      Hypothesis h_get_vm_mapped_pages_p : Genv.find_funct_ptr ge b_get_vm_mapped_pages
                                           = Some (External (EF_external get_vm_mapped_pages
                                                            (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                  (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_unmap_and_load_vm_image: block.
      Hypothesis h_unmap_and_load_vm_image_s : Genv.find_symbol ge unmap_and_load_vm_image = Some b_unmap_and_load_vm_image.
      Hypothesis h_unmap_and_load_vm_image_p : Genv.find_funct_ptr ge b_unmap_and_load_vm_image
                                               = Some (External (EF_external unmap_and_load_vm_image
                                                                (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                                      (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_verify_image: block.
      Hypothesis h_verify_image_s : Genv.find_symbol ge verify_image = Some b_verify_image.
      Hypothesis h_verify_image_p : Genv.find_funct_ptr ge b_verify_image
                                    = Some (External (EF_external verify_image
                                                     (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tuint cc_default))
                                           (Tcons tuint (Tcons tulong Tnil)) tuint cc_default).
      Variable b_set_vm_state: block.
      Hypothesis h_set_vm_state_s : Genv.find_symbol ge set_vm_state = Some b_set_vm_state.
      Hypothesis h_set_vm_state_p : Genv.find_funct_ptr ge b_set_vm_state
                                    = Some (External (EF_external set_vm_state
                                                     (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma verify_and_load_images_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: verify_and_load_images_spec (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) verify_and_load_images_body E0 le' (m, d') Out_normal).
      Proof.
        Local Opaque acquire_lock_vm_spec release_lock_vm_spec get_vm_state_spec get_vm_next_load_idx_spec
              get_vm_load_addr_spec get_vm_remap_addr_spec get_vm_mapped_pages_spec unmap_and_load_vm_image_spec
              verify_image_spec set_vm_state_spec panic_spec.
        Local Hint Unfold phys_page.
        solve_code_proof Hspec verify_and_load_images_body; try solve[eexists; solve_proof_low].
        get_loop_body. remember z0 as num.
        remember (PTree.set _load_idx (Vint (Int.repr 0))
                  (PTree.set _load_info_cnt (Vint (Int.repr z0))
                    (set_opttemp (Some _t'2) (Vint (Int.repr z0))
                        (PTree.set _state (Vint (Int.repr z)) (PTree.set _t'1 (Vint (Int.repr z)) le)))))
                 as le_loop.
        set (P := fun le0 m0 => m0 = (m, r) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, r0) /\ le0 ! _vmid = Some (Vint vmid)).
        set (Inv := fun le0 m0 n => exists idx1 adt1,
                        verify_and_load_loop (Z.to_nat (num - n)) (Int.unsigned vmid) 0 r = Some (Int.unsigned idx1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ Int.unsigned idx1 = num - n /\
                        le0 ! _vmid = Some (Vint vmid) /\ le0 ! _load_idx = Some (Vint idx1) /\
                        le0 ! _load_info_cnt = Some (Vint (Int.repr num))).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists idx' adt',
                    verify_and_load_loop (Z.to_nat (num - Z.of_nat N)) (Int.unsigned vmid) 0 r = Some (Int.unsigned idx', adt')).
        { add_int C5 z1; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C5. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop. simpl_func Hnext.
          add_int' z2; try somega. repeat eexists. add_int' z2; try somega. repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            add_int' 0; try somega. rewrite Heqnum, Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
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
                simpl in Hnext. rewrite H in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext. inversion Hnext. rewrite H11 in *.
                bool_rel_all. eexists; eexists; split. solve_proof_low.
                exists (n-1). split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]].
                inversion Hnext. rewrite H11 in *.
                bool_rel_all. eexists; eexists; split. solve_proof_low.
                exists (n-1). split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]].
              + eexists. eexists. split_and.
                * solve_proof_low.
                * solve_proof_low.
                * intro. unfold Q.
                  assert (n=0) by omega. clear Heqle_loop. subst.
                  sstep. rewrite C5 in H. inv H.
                  split_and; first[reflexivity|solve_proof_low].
                * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, r)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, r) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ?). rewrite Hm' in exec.
        rewrite Heqnum in *. eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End verify_and_load_images_proof.

  Section alloc_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ init_spt ↦ gensem init_spt_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_init_spt: block.
      Hypothesis h_init_spt_s : Genv.find_symbol ge init_spt = Some b_init_spt.
      Hypothesis h_init_spt_p : Genv.find_funct_ptr ge b_init_spt
                                = Some (External (EF_external init_spt
                                                 (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                       (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma alloc_smmu_body_correct:
        forall m d d' env le vmid cbndx index
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: alloc_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec alloc_smmu_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption.
      Qed.

    End BodyProof.

  End alloc_smmu_proof.

  Section assign_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ assign_pfn_to_smmu ↦ gensem assign_pfn_to_smmu_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_assign_pfn_to_smmu: block.
      Hypothesis h_assign_pfn_to_smmu_s : Genv.find_symbol ge assign_pfn_to_smmu = Some b_assign_pfn_to_smmu.
      Hypothesis h_assign_pfn_to_smmu_p : Genv.find_funct_ptr ge b_assign_pfn_to_smmu
                                          = Some (External (EF_external assign_pfn_to_smmu
                                                           (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                 (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma assign_smmu_body_correct:
        forall m d d' env le vmid pfn gfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (Hinv: high_level_invariant d)
               (Hspec: assign_smmu_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) assign_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec assign_smmu_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption.
      Qed.

    End BodyProof.

  End assign_smmu_proof.

  Section map_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ update_smmu_page ↦ gensem update_smmu_page_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_update_smmu_page: block.
      Hypothesis h_update_smmu_page_s : Genv.find_symbol ge update_smmu_page = Some b_update_smmu_page.
      Hypothesis h_update_smmu_page_p : Genv.find_funct_ptr ge b_update_smmu_page
                                        = Some (External (EF_external update_smmu_page
                                                         (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma map_smmu_body_correct:
        forall m d d' env le vmid cbndx index iova pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: map_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_smmu_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption.
      Qed.

    End BodyProof.

  End map_smmu_proof.

  Section clear_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ unmap_smmu_page ↦ gensem unmap_smmu_page_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_unmap_smmu_page: block.
      Hypothesis h_unmap_smmu_page_s : Genv.find_symbol ge unmap_smmu_page = Some b_unmap_smmu_page.
      Hypothesis h_unmap_smmu_page_p : Genv.find_funct_ptr ge b_unmap_smmu_page
                                       = Some (External (EF_external unmap_smmu_page
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma clear_smmu_body_correct:
        forall m d d' env le vmid cbndx index iova
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (Hinv: high_level_invariant d)
               (Hspec: clear_smmu_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_smmu_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption.
      Qed.

    End BodyProof.

  End clear_smmu_proof.

  Section map_io_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ map_vm_io ↦ gensem map_vm_io_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_map_vm_io: block.
      Hypothesis h_map_vm_io_s : Genv.find_symbol ge map_vm_io = Some b_map_vm_io.
      Hypothesis h_map_vm_io_p : Genv.find_funct_ptr ge b_map_vm_io
                                 = Some (External (EF_external map_vm_io
                                                  (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                        (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma map_io_body_correct:
        forall m d d' env le vmid gpa pa
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTgpa: PTree.get _gpa le = Some (Vlong gpa))
               (HPTpa: PTree.get _pa le = Some (Vlong pa))
               (Hinv: high_level_invariant d)
               (Hspec: map_io_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gpa)) (VZ64 (Int64.unsigned pa)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_io_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_io_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End map_io_proof.

  Section is_inc_exe_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_inc_exe ↦ gensem get_vm_inc_exe_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_inc_exe: block.
      Hypothesis h_get_vm_inc_exe_s : Genv.find_symbol ge get_vm_inc_exe = Some b_get_vm_inc_exe.
      Hypothesis h_get_vm_inc_exe_p : Genv.find_funct_ptr ge b_get_vm_inc_exe
                                      = Some (External (EF_external get_vm_inc_exe
                                                       (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                             (Tcons tuint Tnil) tuint cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma is_inc_exe_body_correct:
        forall m d d' env le vmid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: is_inc_exe_spec0 (Int.unsigned vmid) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) is_inc_exe_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec is_inc_exe_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End is_inc_exe_proof.

  Section save_encrypted_vcpu_proof.

    Let L : compatlayer (cdata RData) :=
      encrypt_gp_regs ↦ gensem encrypt_gp_regs_spec
          ⊕ encrypt_sys_regs ↦ gensem encrypt_sys_regs_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_encrypt_gp_regs: block.
      Hypothesis h_encrypt_gp_regs_s : Genv.find_symbol ge encrypt_gp_regs = Some b_encrypt_gp_regs.
      Hypothesis h_encrypt_gp_regs_p : Genv.find_funct_ptr ge b_encrypt_gp_regs
                                       = Some (External (EF_external encrypt_gp_regs
                                                        (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_encrypt_sys_regs: block.
      Hypothesis h_encrypt_sys_regs_s : Genv.find_symbol ge encrypt_sys_regs = Some b_encrypt_sys_regs.
      Hypothesis h_encrypt_sys_regs_p : Genv.find_funct_ptr ge b_encrypt_sys_regs
                                        = Some (External (EF_external encrypt_sys_regs
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).

      Lemma save_encrypted_vcpu_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: save_encrypted_vcpu_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) save_encrypted_vcpu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec save_encrypted_vcpu_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End save_encrypted_vcpu_proof.

  Section load_encrypted_vcpu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_vcpu_state ↦ gensem get_vcpu_state_spec
          ⊕ decrypt_gp_regs ↦ gensem decrypt_gp_regs_spec
          ⊕ decrypt_sys_regs ↦ gensem decrypt_sys_regs_spec
          ⊕ set_vm_inc_exe ↦ gensem set_vm_inc_exe_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_vcpu_state: block.
      Hypothesis h_get_vcpu_state_s : Genv.find_symbol ge get_vcpu_state = Some b_get_vcpu_state.
      Hypothesis h_get_vcpu_state_p : Genv.find_funct_ptr ge b_get_vcpu_state
                                      = Some (External (EF_external get_vcpu_state
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_decrypt_gp_regs: block.
      Hypothesis h_decrypt_gp_regs_s : Genv.find_symbol ge decrypt_gp_regs = Some b_decrypt_gp_regs.
      Hypothesis h_decrypt_gp_regs_p : Genv.find_funct_ptr ge b_decrypt_gp_regs
                                       = Some (External (EF_external decrypt_gp_regs
                                                        (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_decrypt_sys_regs: block.
      Hypothesis h_decrypt_sys_regs_s : Genv.find_symbol ge decrypt_sys_regs = Some b_decrypt_sys_regs.
      Hypothesis h_decrypt_sys_regs_p : Genv.find_funct_ptr ge b_decrypt_sys_regs
                                        = Some (External (EF_external decrypt_sys_regs
                                                         (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_vm_inc_exe: block.
      Hypothesis h_set_vm_inc_exe_s : Genv.find_symbol ge set_vm_inc_exe = Some b_set_vm_inc_exe.
      Hypothesis h_set_vm_inc_exe_p : Genv.find_funct_ptr ge b_set_vm_inc_exe
                                      = Some (External (EF_external set_vm_inc_exe
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma load_encrypted_vcpu_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: load_encrypted_vcpu_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) load_encrypted_vcpu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec load_encrypted_vcpu_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End load_encrypted_vcpu_proof.

  Section save_encrypt_buf_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ encrypt_mem_buf ↦ gensem encrypt_mem_buf_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_s2page: block.
      Hypothesis h_acquire_lock_s2page_s : Genv.find_symbol ge acquire_lock_s2page = Some b_acquire_lock_s2page.
      Hypothesis h_acquire_lock_s2page_p : Genv.find_funct_ptr ge b_acquire_lock_s2page
                                           = Some (External (EF_external acquire_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_encrypt_mem_buf: block.
      Hypothesis h_encrypt_mem_buf_s : Genv.find_symbol ge encrypt_mem_buf = Some b_encrypt_mem_buf.
      Hypothesis h_encrypt_mem_buf_p : Genv.find_funct_ptr ge b_encrypt_mem_buf
                                       = Some (External (EF_external encrypt_mem_buf
                                                        (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                              (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma save_encrypt_buf_body_correct:
        forall m d d' env le vmid inbuf outbuf
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTinbuf: PTree.get _inbuf le = Some (Vlong inbuf))
               (HPToutbuf: PTree.get _outbuf le = Some (Vlong outbuf))
               (Hinv: high_level_invariant d)
               (Hspec: save_encrypt_buf_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned inbuf)) (VZ64 (Int64.unsigned outbuf)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) save_encrypt_buf_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec save_encrypt_buf_body;
        pose proof (int64_bound inbuf);
        pose proof (int64_bound outbuf);
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End save_encrypt_buf_proof.

  Section load_decrypt_buf_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ set_pfn_owner ↦ gensem set_pfn_owner_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ set_pfn_map ↦ gensem set_pfn_map_spec
          ⊕ clear_pfn_host ↦ gensem clear_pfn_host_spec
          ⊕ decrypt_mem_buf ↦ gensem decrypt_mem_buf_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_acquire_lock_s2page: block.
      Hypothesis h_acquire_lock_s2page_s : Genv.find_symbol ge acquire_lock_s2page = Some b_acquire_lock_s2page.
      Hypothesis h_acquire_lock_s2page_p : Genv.find_funct_ptr ge b_acquire_lock_s2page
                                           = Some (External (EF_external acquire_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_owner: block.
      Hypothesis h_set_pfn_owner_s : Genv.find_symbol ge set_pfn_owner = Some b_set_pfn_owner.
      Hypothesis h_set_pfn_owner_p : Genv.find_funct_ptr ge b_set_pfn_owner
                                     = Some (External (EF_external set_pfn_owner
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_pfn_map: block.
      Hypothesis h_set_pfn_map_s : Genv.find_symbol ge set_pfn_map = Some b_set_pfn_map.
      Hypothesis h_set_pfn_map_p : Genv.find_funct_ptr ge b_set_pfn_map
                                   = Some (External (EF_external set_pfn_map
                                                    (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                          (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_clear_pfn_host: block.
      Hypothesis h_clear_pfn_host_s : Genv.find_symbol ge clear_pfn_host = Some b_clear_pfn_host.
      Hypothesis h_clear_pfn_host_p : Genv.find_funct_ptr ge b_clear_pfn_host
                                      = Some (External (EF_external clear_pfn_host
                                                       (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                             (Tcons tulong Tnil) tvoid cc_default).
      Variable b_decrypt_mem_buf: block.
      Hypothesis h_decrypt_mem_buf_s : Genv.find_symbol ge decrypt_mem_buf = Some b_decrypt_mem_buf.
      Hypothesis h_decrypt_mem_buf_p : Genv.find_funct_ptr ge b_decrypt_mem_buf
                                       = Some (External (EF_external decrypt_mem_buf
                                                        (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                              (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma load_decrypt_buf_body_correct:
        forall m d d' env le vmid inbuf
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTinbuf: PTree.get _inbuf le = Some (Vlong inbuf))
               (Hinv: high_level_invariant d)
               (Hspec: load_decrypt_buf_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned inbuf)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) load_decrypt_buf_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec load_decrypt_buf_body;
          pose proof (int64_bound inbuf);
          eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End load_decrypt_buf_proof.

End BootOpsProofLow.

```
