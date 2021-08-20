# MmioSPTOpsProofCode

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
Require Import MmioSPTWalk.Layer.
Require Import Ident.
Require Import MmioSPTOps.Code.
Require Import MmioSPTWalk.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioSPTOps.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioSPTOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section init_spt_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_spt ↦ gensem acquire_lock_spt_spec
          ⊕ clear_smmu_pt ↦ gensem clear_smmu_pt_spec
          ⊕ release_lock_spt ↦ gensem release_lock_spt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_spt: block.
      Hypothesis h_acquire_lock_spt_s : Genv.find_symbol ge acquire_lock_spt = Some b_acquire_lock_spt.
      Hypothesis h_acquire_lock_spt_p : Genv.find_funct_ptr ge b_acquire_lock_spt
                                        = Some (External (EF_external acquire_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_clear_smmu_pt: block.
      Hypothesis h_clear_smmu_pt_s : Genv.find_symbol ge clear_smmu_pt = Some b_clear_smmu_pt.
      Hypothesis h_clear_smmu_pt_p : Genv.find_funct_ptr ge b_clear_smmu_pt
                                     = Some (External (EF_external clear_smmu_pt
                                                      (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_release_lock_spt: block.
      Hypothesis h_release_lock_spt_s : Genv.find_symbol ge release_lock_spt = Some b_release_lock_spt.
      Hypothesis h_release_lock_spt_p : Genv.find_funct_ptr ge b_release_lock_spt
                                        = Some (External (EF_external release_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).

      Lemma init_spt_body_correct:
        forall m d d' env le cbndx index
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: init_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) init_spt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec init_spt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End init_spt_proof.

  Section walk_spt_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_spt ↦ gensem acquire_lock_spt_spec
          ⊕ walk_smmu_pt ↦ gensem walk_smmu_pt_spec
          ⊕ release_lock_spt ↦ gensem release_lock_spt_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_spt: block.
      Hypothesis h_acquire_lock_spt_s : Genv.find_symbol ge acquire_lock_spt = Some b_acquire_lock_spt.
      Hypothesis h_acquire_lock_spt_p : Genv.find_funct_ptr ge b_acquire_lock_spt
                                        = Some (External (EF_external acquire_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_walk_smmu_pt: block.
      Hypothesis h_walk_smmu_pt_s : Genv.find_symbol ge walk_smmu_pt = Some b_walk_smmu_pt.
      Hypothesis h_walk_smmu_pt_p : Genv.find_funct_ptr ge b_walk_smmu_pt
                                    = Some (External (EF_external walk_smmu_pt
                                                     (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default))
                                           (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default).
      Variable b_release_lock_spt: block.
      Hypothesis h_release_lock_spt_s : Genv.find_symbol ge release_lock_spt = Some b_release_lock_spt.
      Hypothesis h_release_lock_spt_p : Genv.find_funct_ptr ge b_release_lock_spt
                                        = Some (External (EF_external release_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_spt_body_correct:
        forall m d d' env le cbndx index addr res
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_spt_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_spt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_spt_proof.

  Section map_spt_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_spt ↦ gensem acquire_lock_spt_spec
          ⊕ set_smmu_pt ↦ gensem set_smmu_pt_spec
          ⊕ release_lock_spt ↦ gensem release_lock_spt_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_spt: block.
      Hypothesis h_acquire_lock_spt_s : Genv.find_symbol ge acquire_lock_spt = Some b_acquire_lock_spt.
      Hypothesis h_acquire_lock_spt_p : Genv.find_funct_ptr ge b_acquire_lock_spt
                                        = Some (External (EF_external acquire_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_set_smmu_pt: block.
      Hypothesis h_set_smmu_pt_s : Genv.find_symbol ge set_smmu_pt = Some b_set_smmu_pt.
      Hypothesis h_set_smmu_pt_p : Genv.find_funct_ptr ge b_set_smmu_pt
                                   = Some (External (EF_external set_smmu_pt
                                                    (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_release_lock_spt: block.
      Hypothesis h_release_lock_spt_s : Genv.find_symbol ge release_lock_spt = Some b_release_lock_spt.
      Hypothesis h_release_lock_spt_p : Genv.find_funct_ptr ge b_release_lock_spt
                                        = Some (External (EF_external release_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma map_spt_body_correct:
        forall m d d' env le cbndx index addr pte
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: map_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_spt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_spt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End map_spt_proof.

  Section unmap_spt_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_spt ↦ gensem acquire_lock_spt_spec
          ⊕ walk_smmu_pt ↦ gensem walk_smmu_pt_spec
          ⊕ set_smmu_pt ↦ gensem set_smmu_pt_spec
          ⊕ release_lock_spt ↦ gensem release_lock_spt_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_spt: block.
      Hypothesis h_acquire_lock_spt_s : Genv.find_symbol ge acquire_lock_spt = Some b_acquire_lock_spt.
      Hypothesis h_acquire_lock_spt_p : Genv.find_funct_ptr ge b_acquire_lock_spt
                                        = Some (External (EF_external acquire_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_walk_smmu_pt: block.
      Hypothesis h_walk_smmu_pt_s : Genv.find_symbol ge walk_smmu_pt = Some b_walk_smmu_pt.
      Hypothesis h_walk_smmu_pt_p : Genv.find_funct_ptr ge b_walk_smmu_pt
                                    = Some (External (EF_external walk_smmu_pt
                                                     (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default))
                                           (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default).
      Variable b_set_smmu_pt: block.
      Hypothesis h_set_smmu_pt_s : Genv.find_symbol ge set_smmu_pt = Some b_set_smmu_pt.
      Hypothesis h_set_smmu_pt_p : Genv.find_funct_ptr ge b_set_smmu_pt
                                   = Some (External (EF_external set_smmu_pt
                                                    (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_release_lock_spt: block.
      Hypothesis h_release_lock_spt_s : Genv.find_symbol ge release_lock_spt = Some b_release_lock_spt.
      Hypothesis h_release_lock_spt_p : Genv.find_funct_ptr ge b_release_lock_spt
                                        = Some (External (EF_external release_lock_spt
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma unmap_spt_body_correct:
        forall m d d' env le cbndx index addr res
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: unmap_spt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) unmap_spt_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec unmap_spt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End unmap_spt_proof.

End MmioSPTOpsProofLow.

```
