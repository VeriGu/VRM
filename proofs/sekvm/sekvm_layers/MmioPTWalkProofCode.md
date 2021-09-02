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

Require Import MmioPTAlloc.Spec.
Require Import Ident.
Require Import MmioPTWalk.Code.
Require Import HypsecCommLib.
Require Import MmioPTAlloc.Layer.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import MmioPTWalk.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioPTWalkProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Local Hint Unfold
        phys_page
        pmd_page
        stage2_pgd_index
        pgd_index
        pud_index
        pmd_index
        pte_index.

  Section walk_smmu_pgd_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_pt_store ↦ gensem smmu_pt_store_spec
          ⊕ smmu_pt_load ↦ gensem smmu_pt_load_spec
          ⊕ alloc_smmu_pgd_page ↦ gensem alloc_smmu_pgd_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_pt_store: block.
      Hypothesis h_smmu_pt_store_s : Genv.find_symbol ge smmu_pt_store = Some b_smmu_pt_store.
      Hypothesis h_smmu_pt_store_p : Genv.find_funct_ptr ge b_smmu_pt_store
                                     = Some (External (EF_external smmu_pt_store
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_smmu_pt_load: block.
      Hypothesis h_smmu_pt_load_s : Genv.find_symbol ge smmu_pt_load = Some b_smmu_pt_load.
      Hypothesis h_smmu_pt_load_p : Genv.find_funct_ptr ge b_smmu_pt_load
                                    = Some (External (EF_external smmu_pt_load
                                                     (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                           (Tcons tulong Tnil) tulong cc_default).
      Variable b_alloc_smmu_pgd_page: block.
      Hypothesis h_alloc_smmu_pgd_page_s : Genv.find_symbol ge alloc_smmu_pgd_page = Some b_alloc_smmu_pgd_page.
      Hypothesis h_alloc_smmu_pgd_page_p : Genv.find_funct_ptr ge b_alloc_smmu_pgd_page
                                           = Some (External (EF_external alloc_smmu_pgd_page
                                                            (signature_of_type Tnil tulong cc_default))
                                                  Tnil tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_smmu_pgd_body_correct:
        forall m d d' env le ttbr addr alloc res
               (Henv: env = PTree.empty _)
               (HPTttbr: PTree.get _ttbr le = Some (Vlong ttbr))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_smmu_pgd_spec0 (VZ64 (Int64.unsigned ttbr)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_smmu_pgd_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_smmu_pgd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_smmu_pgd_code_correct:
      spec_le (walk_smmu_pgd ↦ walk_smmu_pgd_spec_low) (〚 walk_smmu_pgd ↦ f_walk_smmu_pgd 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_smmu_pgd_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_smmu_pgd ) (Vlong ttbr :: Vlong addr :: Vint alloc :: nil)
               (create_undef_temps (fn_temps f_walk_smmu_pgd)))) hinv.
    Qed.

  End walk_smmu_pgd_proof.

  Section walk_smmu_pmd_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_pt_store ↦ gensem smmu_pt_store_spec
          ⊕ smmu_pt_load ↦ gensem smmu_pt_load_spec
          ⊕ alloc_smmu_pmd_page ↦ gensem alloc_smmu_pmd_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_pt_store: block.
      Hypothesis h_smmu_pt_store_s : Genv.find_symbol ge smmu_pt_store = Some b_smmu_pt_store.
      Hypothesis h_smmu_pt_store_p : Genv.find_funct_ptr ge b_smmu_pt_store
                                     = Some (External (EF_external smmu_pt_store
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_smmu_pt_load: block.
      Hypothesis h_smmu_pt_load_s : Genv.find_symbol ge smmu_pt_load = Some b_smmu_pt_load.
      Hypothesis h_smmu_pt_load_p : Genv.find_funct_ptr ge b_smmu_pt_load
                                    = Some (External (EF_external smmu_pt_load
                                                     (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                           (Tcons tulong Tnil) tulong cc_default).
      Variable b_alloc_smmu_pmd_page: block.
      Hypothesis h_alloc_smmu_pmd_page_s : Genv.find_symbol ge alloc_smmu_pmd_page = Some b_alloc_smmu_pmd_page.
      Hypothesis h_alloc_smmu_pmd_page_p : Genv.find_funct_ptr ge b_alloc_smmu_pmd_page
                                           = Some (External (EF_external alloc_smmu_pmd_page
                                                            (signature_of_type Tnil tulong cc_default))
                                                  Tnil tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_smmu_pmd_body_correct:
        forall m d d' env le pgd addr alloc res
               (Henv: env = PTree.empty _)
               (HPTpgd: PTree.get _pgd le = Some (Vlong pgd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_smmu_pmd_spec0 (VZ64 (Int64.unsigned pgd)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_smmu_pmd_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_smmu_pmd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_smmu_pmd_code_correct:
      spec_le (walk_smmu_pmd ↦ walk_smmu_pmd_spec_low) (〚 walk_smmu_pmd ↦ f_walk_smmu_pmd 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_smmu_pmd_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_smmu_pmd ) (Vlong pgd :: Vlong addr :: Vint alloc :: nil)
               (create_undef_temps (fn_temps f_walk_smmu_pmd)))) hinv.
    Qed.

  End walk_smmu_pmd_proof.

  Section walk_smmu_pte_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_pt_load ↦ gensem smmu_pt_load_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_pt_load: block.
      Hypothesis h_smmu_pt_load_s : Genv.find_symbol ge smmu_pt_load = Some b_smmu_pt_load.
      Hypothesis h_smmu_pt_load_p : Genv.find_funct_ptr ge b_smmu_pt_load
                                    = Some (External (EF_external smmu_pt_load
                                                     (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                           (Tcons tulong Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_smmu_pte_body_correct:
        forall m d env le pmd addr res
               (Henv: env = PTree.empty _)
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_smmu_pte_spec0 (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_smmu_pte_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_smmu_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_smmu_pte_code_correct:
      spec_le (walk_smmu_pte ↦ walk_smmu_pte_spec_low) (〚 walk_smmu_pte ↦ f_walk_smmu_pte 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_smmu_pte_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_smmu_pte ) (Vlong pmd :: Vlong addr :: nil)
               (create_undef_temps (fn_temps f_walk_smmu_pte)))) hinv.
    Qed.

  End walk_smmu_pte_proof.

  Section set_smmu_pte_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_pt_store ↦ gensem smmu_pt_store_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_pt_store: block.
      Hypothesis h_smmu_pt_store_s : Genv.find_symbol ge smmu_pt_store = Some b_smmu_pt_store.
      Hypothesis h_smmu_pt_store_p : Genv.find_funct_ptr ge b_smmu_pt_store
                                     = Some (External (EF_external smmu_pt_store
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).

      Lemma set_smmu_pte_body_correct:
        forall m d d' env le pmd addr pte
               (Henv: env = PTree.empty _)
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: set_smmu_pte_spec0 (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_smmu_pte_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_smmu_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_smmu_pte_code_correct:
      spec_le (set_smmu_pte ↦ set_smmu_pte_spec_low) (〚 set_smmu_pte ↦ f_set_smmu_pte 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_smmu_pte_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_smmu_pte ) (Vlong pmd :: Vlong addr :: Vlong pte :: nil)
               (create_undef_temps (fn_temps f_set_smmu_pte)))) hinv.
    Qed.

  End set_smmu_pte_proof.

End MmioPTWalkProofLow.

```
