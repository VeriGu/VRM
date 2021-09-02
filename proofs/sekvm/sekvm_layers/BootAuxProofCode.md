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
Require Import BootAux.Code.
Require Import MemoryOps.Spec.
Require Import BootCore.Layer.
Require Import MemManager.Spec.
Require Import Ident.
Require Import BootAux.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section BootAuxProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section unmap_and_load_vm_image_proof.

    Let L : compatlayer (cdata RData) :=
          walk_s2pt ↦ gensem walk_s2pt_spec
          ⊕ prot_and_map_vm_s2pt ↦ gensem prot_and_map_vm_s2pt_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_walk_s2pt: block.
      Hypothesis h_walk_s2pt_s : Genv.find_symbol ge walk_s2pt = Some b_walk_s2pt.
      Hypothesis h_walk_s2pt_p : Genv.find_funct_ptr ge b_walk_s2pt
                                 = Some (External (EF_external walk_s2pt
                                                  (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_prot_and_map_vm_s2pt: block.
      Hypothesis h_prot_and_map_vm_s2pt_s : Genv.find_symbol ge prot_and_map_vm_s2pt = Some b_prot_and_map_vm_s2pt.
      Hypothesis h_prot_and_map_vm_s2pt_p : Genv.find_funct_ptr ge b_prot_and_map_vm_s2pt
                                            = Some (External (EF_external prot_and_map_vm_s2pt
                                                             (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma unmap_and_load_vm_image_body_correct:
        forall m d d' env le vmid target_addr remap_addr num
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTtarget_addr: PTree.get _target_addr le = Some (Vlong target_addr))
               (HPTremap_addr: PTree.get _remap_addr le = Some (Vlong remap_addr))
               (HPTnum: PTree.get _num le = Some (Vlong num))
               (Hinv: high_level_invariant d)
               (Hspec: unmap_and_load_vm_image_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned target_addr)) (VZ64 (Int64.unsigned remap_addr)) (VZ64 (Int64.unsigned num)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) unmap_and_load_vm_image_body E0 le' (m, d') Out_normal).
      Proof.
        Local Hint Unfold phys_page.
        Local Opaque prot_and_map_vm_s2pt_spec walk_s2pt_spec panic_spec.
        solve_code_proof Hspec unmap_and_load_vm_image_body. get_loop_body.
        remember ((Int64.unsigned target_addr + Int64.unsigned num * 4096 - Int64.unsigned target_addr / 2097152 * 2097152 + 2097151) / 2097152) as num0.
        remember (PTree.set _num (Vlong (Int64.repr num0))
                  (PTree.set _end (Vlong (Int64.repr (Int64.unsigned target_addr + Int64.unsigned num * 4096)))
                   (PTree.set _start (Vlong (Int64.repr (Int64.unsigned target_addr / 2097152 * 2097152))) le))) as le_loop.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
        set (Q := fun le0 m0 => m0 = (m, d') /\ le0 ! _vmid = Some (Vint vmid)).
        set (Inv := fun le0 m0 n => exists start1 target1 remap1 adt1,
                        unmap_and_load_loop (Z.to_nat (num0 - n)) (Int.unsigned vmid) (Int64.unsigned target_addr / 2097152 * 2097152)
                                             (Int64.unsigned target_addr) (Int64.unsigned remap_addr) d =
                        Some (Int64.unsigned start1, Int64.unsigned target1, Int64.unsigned remap1, adt1) /\
                        m0 = (m, adt1) /\ 0 <= n /\ n <= num0 /\ le0 ! _num = Some (Vlong (Int64.repr n)) /\
                        le0 ! _start = Some (Vlong start1) /\ le0 ! _target_addr = Some (Vlong target1) /\
                        le0 ! _remap_addr = Some (Vlong remap1) /\ le0 ! _vmid = Some (Vint vmid)).
        assert(loop_succ: forall N, Z.of_nat N <= num0 -> exists start' target' remap' adt',
                    unmap_and_load_loop (Z.to_nat (num0 - Z.of_nat N)) (Int.unsigned vmid) (Int64.unsigned target_addr / 2097152 * 2097152)
                                         (Int64.unsigned target_addr) (Int64.unsigned remap_addr) d =
                        Some (Int64.unsigned start', Int64.unsigned target', Int64.unsigned remap', adt')).
        { add_int64 C5 z0; try somega. add_int64 C5 z1; try somega. add_int64 C5 z; try somega.
          induction N. rewrite Z.sub_0_r. rewrite C5. intros. repeat eexists; reflexivity.
          intro C'. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in C'.
          assert(Hcc: Z.of_nat N <= num0) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & ? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; add_int64' z2; try somega; add_int64' z3; try somega; add_int64' z4; try somega; repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? C'. destruct C' as [C'1 C'2].
            rewrite C'2 in *. exists num0.
            replace (num0 - num0) with 0 by omega. simpl.
            rewrite Heqle_loop in *. repeat eexists; first [reflexivity|assumption|solve_proof_low].
            solve_proof_low.
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro C'. inversion C'.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num0) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & ? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite H in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext; bool_rel_all; inversion Hnext.
                rewrite H13 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                rewrite H13 in *; eexists; eexists; split; [solve_proof_low|
                exists (n-1); split; [split; solve_proof_low| solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low]]].
                assert(1152921504606842880 ?= 4503599627370495 / 512 * 2097152 = Lt) by reflexivity.
                red; rewrite H9; red; intro T; inversion T.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro. unfold Q.
                assert (n=0) by omega. clear Heqle_loop. subst.
                sstep. rewrite C5 in H. inv H.
                split_and; first[reflexivity|solve_proof_low].
              * intro C'. inversion C'. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Hm' & ?). rewrite Hm' in exec.
        rewrite Heqbody, Heqcond, Heqle_loop in *.
        eexists; solve_proof_low.
        assert(0 <=  Int64.unsigned target_addr / 2097152 * 2097152) by somega. omega.
        rewrite Heqnum0 in exec. solve_proof_low.
        assert(0 <=  Int64.unsigned target_addr / 2097152 * 2097152) by somega. omega.
      Qed.

    End BodyProof.

    Theorem unmap_and_load_vm_image_code_correct:
      spec_le (unmap_and_load_vm_image ↦ unmap_and_load_vm_image_spec_low) (〚 unmap_and_load_vm_image ↦ f_unmap_and_load_vm_image 〛 L).
    Proof.
      Local Opaque unmap_and_load_vm_image_spec.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (unmap_and_load_vm_image_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_unmap_and_load_vm_image ) (Vint vmid :: Vlong target_addr :: Vlong remap_addr :: Vlong num :: nil)
               (create_undef_temps (fn_temps f_unmap_and_load_vm_image)))) hinv.
    Qed.

  End unmap_and_load_vm_image_proof.

End BootAuxProofLow.

```
