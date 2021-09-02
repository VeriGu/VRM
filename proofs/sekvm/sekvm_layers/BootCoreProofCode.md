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
Require Import Locks.Spec.
Require Import BootCore.Code.
Require Import VMPower.Layer.
Require Import Ident.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import BootCore.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section BootCoreProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section gen_vmid_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_core ↦ gensem acquire_lock_core_spec
          ⊕ get_next_vmid ↦ gensem get_next_vmid_spec
          ⊕ set_next_vmid ↦ gensem set_next_vmid_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ release_lock_core ↦ gensem release_lock_core_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_core: block.
      Hypothesis h_acquire_lock_core_s : Genv.find_symbol ge acquire_lock_core = Some b_acquire_lock_core.
      Hypothesis h_acquire_lock_core_p : Genv.find_funct_ptr ge b_acquire_lock_core
                                         = Some (External (EF_external acquire_lock_core
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_next_vmid: block.
      Hypothesis h_get_next_vmid_s : Genv.find_symbol ge get_next_vmid = Some b_get_next_vmid.
      Hypothesis h_get_next_vmid_p : Genv.find_funct_ptr ge b_get_next_vmid
                                     = Some (External (EF_external get_next_vmid
                                                      (signature_of_type Tnil tuint cc_default))
                                            Tnil tuint cc_default).
      Variable b_set_next_vmid: block.
      Hypothesis h_set_next_vmid_s : Genv.find_symbol ge set_next_vmid = Some b_set_next_vmid.
      Hypothesis h_set_next_vmid_p : Genv.find_funct_ptr ge b_set_next_vmid
                                     = Some (External (EF_external set_next_vmid
                                                      (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                            (Tcons tuint Tnil) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_release_lock_core: block.
      Hypothesis h_release_lock_core_s : Genv.find_symbol ge release_lock_core = Some b_release_lock_core.
      Hypothesis h_release_lock_core_p : Genv.find_funct_ptr ge b_release_lock_core
                                         = Some (External (EF_external release_lock_core
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma gen_vmid_body_correct:
        forall m d d' env le  res
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: gen_vmid_spec0  d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) gen_vmid_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec gen_vmid_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem gen_vmid_code_correct:
      spec_le (gen_vmid ↦ gen_vmid_spec_low) (〚 gen_vmid ↦ f_gen_vmid 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (gen_vmid_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_gen_vmid) nil
               (create_undef_temps (fn_temps f_gen_vmid)))) hinv.
    Qed.

  End gen_vmid_proof.

  Section alloc_remap_addr_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_core ↦ gensem acquire_lock_core_spec
          ⊕ get_next_remap_ptr ↦ gensem get_next_remap_ptr_spec
          ⊕ release_lock_core ↦ gensem release_lock_core_spec
          ⊕ set_next_remap_ptr ↦ gensem set_next_remap_ptr_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_core: block.
      Hypothesis h_acquire_lock_core_s : Genv.find_symbol ge acquire_lock_core = Some b_acquire_lock_core.
      Hypothesis h_acquire_lock_core_p : Genv.find_funct_ptr ge b_acquire_lock_core
                                         = Some (External (EF_external acquire_lock_core
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_next_remap_ptr: block.
      Hypothesis h_get_next_remap_ptr_s : Genv.find_symbol ge get_next_remap_ptr = Some b_get_next_remap_ptr.
      Hypothesis h_get_next_remap_ptr_p : Genv.find_funct_ptr ge b_get_next_remap_ptr
                                          = Some (External (EF_external get_next_remap_ptr
                                                           (signature_of_type Tnil tulong cc_default))
                                                 Tnil tulong cc_default).
      Variable b_release_lock_core: block.
      Hypothesis h_release_lock_core_s : Genv.find_symbol ge release_lock_core = Some b_release_lock_core.
      Hypothesis h_release_lock_core_p : Genv.find_funct_ptr ge b_release_lock_core
                                         = Some (External (EF_external release_lock_core
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_set_next_remap_ptr: block.
      Hypothesis h_set_next_remap_ptr_s : Genv.find_symbol ge set_next_remap_ptr = Some b_set_next_remap_ptr.
      Hypothesis h_set_next_remap_ptr_p : Genv.find_funct_ptr ge b_set_next_remap_ptr
                                          = Some (External (EF_external set_next_remap_ptr
                                                           (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                 (Tcons tulong Tnil) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma alloc_remap_addr_body_correct:
        forall m d d' env le pgnum res
               (Henv: env = PTree.empty _)
               (HPTpgnum: PTree.get _pgnum le = Some (Vlong pgnum))
               (Hinv: high_level_invariant d)
               (Hspec: alloc_remap_addr_spec0 (VZ64 (Int64.unsigned pgnum)) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_remap_addr_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_remap_addr_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_remap_addr_code_correct:
      spec_le (alloc_remap_addr ↦ alloc_remap_addr_spec_low) (〚 alloc_remap_addr ↦ f_alloc_remap_addr 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_remap_addr_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_remap_addr ) (Vlong pgnum :: nil)
               (create_undef_temps (fn_temps f_alloc_remap_addr)))) hinv.
    Qed.

  End alloc_remap_addr_proof.

End BootCoreProofLow.

```
