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

Require Import Ident.
Require Import NPTWalk.Layer.
Require Import NPTOps.Code.
Require Import HypsecCommLib.
Require Import NPTOps.Spec.
Require Import Constants.
Require Import NPTWalk.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import RData.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section NPTOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section get_level_s2pt_proof.

    Let L : compatlayer (cdata RData) :=
      get_npt_level ↦ gensem get_npt_level_spec
          ⊕ acquire_lock_pt ↦ gensem acquire_lock_pt_spec
          ⊕ release_lock_pt ↦ gensem release_lock_pt_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_npt_level: block.
      Hypothesis h_get_npt_level_s : Genv.find_symbol ge get_npt_level = Some b_get_npt_level.
      Hypothesis h_get_npt_level_p : Genv.find_funct_ptr ge b_get_npt_level
                                     = Some (External (EF_external get_npt_level
                                                      (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tuint cc_default))
                                            (Tcons tuint (Tcons tulong Tnil)) tuint cc_default).
      Variable b_acquire_lock_pt: block.
      Hypothesis h_acquire_lock_pt_s : Genv.find_symbol ge acquire_lock_pt = Some b_acquire_lock_pt.
      Hypothesis h_acquire_lock_pt_p : Genv.find_funct_ptr ge b_acquire_lock_pt
                                       = Some (External (EF_external acquire_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_pt: block.
      Hypothesis h_release_lock_pt_s : Genv.find_symbol ge release_lock_pt = Some b_release_lock_pt.
      Hypothesis h_release_lock_pt_p : Genv.find_funct_ptr ge b_release_lock_pt
                                       = Some (External (EF_external release_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma get_level_s2pt_body_correct:
        forall m d d' env le vmid addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: get_level_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) get_level_s2pt_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec get_level_s2pt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End get_level_s2pt_proof.

  Section walk_s2pt_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_pt ↦ gensem acquire_lock_pt_spec
          ⊕ release_lock_pt ↦ gensem release_lock_pt_spec
          ⊕ walk_npt ↦ gensem walk_npt_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_pt: block.
      Hypothesis h_acquire_lock_pt_s : Genv.find_symbol ge acquire_lock_pt = Some b_acquire_lock_pt.
      Hypothesis h_acquire_lock_pt_p : Genv.find_funct_ptr ge b_acquire_lock_pt
                                       = Some (External (EF_external acquire_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_pt: block.
      Hypothesis h_release_lock_pt_s : Genv.find_symbol ge release_lock_pt = Some b_release_lock_pt.
      Hypothesis h_release_lock_pt_p : Genv.find_funct_ptr ge b_release_lock_pt
                                       = Some (External (EF_external release_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_walk_npt: block.
      Hypothesis h_walk_npt_s : Genv.find_symbol ge walk_npt = Some b_walk_npt.
      Hypothesis h_walk_npt_p : Genv.find_funct_ptr ge b_walk_npt
                                = Some (External (EF_external walk_npt
                                                 (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                       (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_s2pt_body_correct:
        forall m d d' env le vmid addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_s2pt_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_s2pt_body; eexists; solve_proof_low.
      Qed.
    End BodyProof.

  End walk_s2pt_proof.

  Section map_s2pt_proof.

    Let L : compatlayer (cdata RData) :=
      set_npt ↦ gensem set_npt_spec
          ⊕ acquire_lock_pt ↦ gensem acquire_lock_pt_spec
          ⊕ release_lock_pt ↦ gensem release_lock_pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_npt: block.
      Hypothesis h_set_npt_s : Genv.find_symbol ge set_npt = Some b_set_npt.
      Hypothesis h_set_npt_p : Genv.find_funct_ptr ge b_set_npt
                               = Some (External (EF_external set_npt
                                                (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                      (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_acquire_lock_pt: block.
      Hypothesis h_acquire_lock_pt_s : Genv.find_symbol ge acquire_lock_pt = Some b_acquire_lock_pt.
      Hypothesis h_acquire_lock_pt_p : Genv.find_funct_ptr ge b_acquire_lock_pt
                                       = Some (External (EF_external acquire_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_pt: block.
      Hypothesis h_release_lock_pt_s : Genv.find_symbol ge release_lock_pt = Some b_release_lock_pt.
      Hypothesis h_release_lock_pt_p : Genv.find_funct_ptr ge b_release_lock_pt
                                       = Some (External (EF_external release_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).

      Lemma map_s2pt_body_correct:
        forall m d d' env le vmid addr level pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTlevel: PTree.get _level le = Some (Vint level))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: map_s2pt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (Int.unsigned level) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_s2pt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_s2pt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End map_s2pt_proof.

  Section clear_pfn_host_proof.

    Let L : compatlayer (cdata RData) :=
      get_npt_level ↦ gensem get_npt_level_spec
          ⊕ set_npt ↦ gensem set_npt_spec
          ⊕ acquire_lock_pt ↦ gensem acquire_lock_pt_spec
          ⊕ release_lock_pt ↦ gensem release_lock_pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_npt_level: block.
      Hypothesis h_get_npt_level_s : Genv.find_symbol ge get_npt_level = Some b_get_npt_level.
      Hypothesis h_get_npt_level_p : Genv.find_funct_ptr ge b_get_npt_level
                                     = Some (External (EF_external get_npt_level
                                                      (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tuint cc_default))
                                            (Tcons tuint (Tcons tulong Tnil)) tuint cc_default).
      Variable b_set_npt: block.
      Hypothesis h_set_npt_s : Genv.find_symbol ge set_npt = Some b_set_npt.
      Hypothesis h_set_npt_p : Genv.find_funct_ptr ge b_set_npt
                               = Some (External (EF_external set_npt
                                                (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                      (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_acquire_lock_pt: block.
      Hypothesis h_acquire_lock_pt_s : Genv.find_symbol ge acquire_lock_pt = Some b_acquire_lock_pt.
      Hypothesis h_acquire_lock_pt_p : Genv.find_funct_ptr ge b_acquire_lock_pt
                                       = Some (External (EF_external acquire_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_release_lock_pt: block.
      Hypothesis h_release_lock_pt_s : Genv.find_symbol ge release_lock_pt = Some b_release_lock_pt.
      Hypothesis h_release_lock_pt_p : Genv.find_funct_ptr ge b_release_lock_pt
                                       = Some (External (EF_external release_lock_pt
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).

      Lemma clear_pfn_host_body_correct:
        forall m d d' env le pfn
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: clear_pfn_host_spec0 (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_pfn_host_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_pfn_host_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End clear_pfn_host_proof.

End NPTOpsProofLow.

```
