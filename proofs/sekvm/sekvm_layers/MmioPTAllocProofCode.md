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

Require Import NPTOps.Layer.
Require Import Ident.
Require Import HypsecCommLib.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import MmioPTAlloc.Code.
Require Import RData.
Require Import MmioPTAlloc.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioPTAllocProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section alloc_smmu_pgd_page_proof.

    Let L : compatlayer (cdata RData) :=
      get_smmu_pgd_next ↦ gensem get_smmu_pgd_next_spec
          ⊕ set_smmu_pgd_next ↦ gensem set_smmu_pgd_next_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_smmu_pgd_next: block.
      Hypothesis h_get_smmu_pgd_next_s : Genv.find_symbol ge get_smmu_pgd_next = Some b_get_smmu_pgd_next.
      Hypothesis h_get_smmu_pgd_next_p : Genv.find_funct_ptr ge b_get_smmu_pgd_next
                                         = Some (External (EF_external get_smmu_pgd_next
                                                          (signature_of_type Tnil tulong cc_default))
                                                Tnil tulong cc_default).
      Variable b_set_smmu_pgd_next: block.
      Hypothesis h_set_smmu_pgd_next_s : Genv.find_symbol ge set_smmu_pgd_next = Some b_set_smmu_pgd_next.
      Hypothesis h_set_smmu_pgd_next_p : Genv.find_funct_ptr ge b_set_smmu_pgd_next
                                         = Some (External (EF_external set_smmu_pgd_next
                                                          (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                (Tcons tulong Tnil) tvoid cc_default).
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

      Lemma alloc_smmu_pgd_page_body_correct:
        forall m d d' env le  res
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: alloc_smmu_pgd_page_spec0  d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_smmu_pgd_page_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_smmu_pgd_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_smmu_pgd_page_code_correct:
      spec_le (alloc_smmu_pgd_page ↦ alloc_smmu_pgd_page_spec_low) (〚 alloc_smmu_pgd_page ↦ f_alloc_smmu_pgd_page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_smmu_pgd_page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_smmu_pgd_page ) nil
               (create_undef_temps (fn_temps f_alloc_smmu_pgd_page)))) hinv.
    Qed.

  End alloc_smmu_pgd_page_proof.

  Section alloc_smmu_pmd_page_proof.

    Let L : compatlayer (cdata RData) :=
      get_smmu_pmd_next ↦ gensem get_smmu_pmd_next_spec
          ⊕ set_smmu_pmd_next ↦ gensem set_smmu_pmd_next_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_smmu_pmd_next: block.
      Hypothesis h_get_smmu_pmd_next_s : Genv.find_symbol ge get_smmu_pmd_next = Some b_get_smmu_pmd_next.
      Hypothesis h_get_smmu_pmd_next_p : Genv.find_funct_ptr ge b_get_smmu_pmd_next
                                         = Some (External (EF_external get_smmu_pmd_next
                                                          (signature_of_type Tnil tulong cc_default))
                                                Tnil tulong cc_default).
      Variable b_set_smmu_pmd_next: block.
      Hypothesis h_set_smmu_pmd_next_s : Genv.find_symbol ge set_smmu_pmd_next = Some b_set_smmu_pmd_next.
      Hypothesis h_set_smmu_pmd_next_p : Genv.find_funct_ptr ge b_set_smmu_pmd_next
                                         = Some (External (EF_external set_smmu_pmd_next
                                                          (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                (Tcons tulong Tnil) tvoid cc_default).
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

      Lemma alloc_smmu_pmd_page_body_correct:
        forall m d d' env le  res
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: alloc_smmu_pmd_page_spec0  d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) alloc_smmu_pmd_page_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec alloc_smmu_pmd_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem alloc_smmu_pmd_page_code_correct:
      spec_le (alloc_smmu_pmd_page ↦ alloc_smmu_pmd_page_spec_low) (〚 alloc_smmu_pmd_page ↦ f_alloc_smmu_pmd_page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (alloc_smmu_pmd_page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_alloc_smmu_pmd_page ) nil
               (create_undef_temps (fn_temps f_alloc_smmu_pmd_page)))) hinv.
    Qed.

  End alloc_smmu_pmd_page_proof.

End MmioPTAllocProofLow.

```
