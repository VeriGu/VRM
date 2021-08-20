# MmioSPTWalkProofCode

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

Require Import MmioPTWalk.Spec.
Require Import Ident.
Require Import RData.
Require Import Constants.
Require Import AbstractMachine.Spec.
Require Import MmioPTWalk.Layer.
Require Import HypsecCommLib.
Require Import MmioSPTWalk.Spec.
Require Import MmioSPTWalk.Code.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Lemma walk_smmu_pgd_0_adt:
  forall ttbr addr adt adt' res (Hspec: walk_smmu_pgd_spec ttbr addr 0 adt = Some (adt', res)),
    adt = adt'.
Proof.
  intros. hsimpl_func Hspec; bool_rel_all; try reflexivity; try omega.
Qed.

Lemma walk_smmu_pmd_0_adt:
  forall pud addr adt adt' res (Hspec: walk_smmu_pmd_spec pud addr 0 adt = Some (adt', res)),
    adt = adt'.
Proof.
  intros. hsimpl_func Hspec; bool_rel_all; try reflexivity; try omega.
Qed.

Local Hint Unfold
      phys_page
      pmd_page
      stage2_pgd_index
      pgd_index
      pud_index
      pmd_index
      pte_index.

Section MmioSPTWalkProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section clear_smmu_pt_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_pt_clear ↦ gensem smmu_pt_clear_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_pt_clear: block.
      Hypothesis h_smmu_pt_clear_s : Genv.find_symbol ge smmu_pt_clear = Some b_smmu_pt_clear.
      Hypothesis h_smmu_pt_clear_p : Genv.find_funct_ptr ge b_smmu_pt_clear
                                     = Some (External (EF_external smmu_pt_clear
                                                      (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).

      Lemma clear_smmu_pt_body_correct:
        forall m d d' env le cbndx index
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: clear_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_smmu_pt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_smmu_pt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem clear_smmu_pt_code_correct:
      spec_le (clear_smmu_pt ↦ clear_smmu_pt_spec_low) (〚 clear_smmu_pt ↦ f_clear_smmu_pt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (clear_smmu_pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_clear_smmu_pt ) (Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_clear_smmu_pt)))) hinv.
    Qed.

  End clear_smmu_pt_proof.

  Section walk_smmu_pt_proof.

    Let L : compatlayer (cdata RData) :=
      get_smmu_cfg_hw_ttbr ↦ gensem get_smmu_cfg_hw_ttbr_spec
          ⊕ walk_smmu_pgd ↦ gensem walk_smmu_pgd_spec
          ⊕ walk_smmu_pmd ↦ gensem walk_smmu_pmd_spec
          ⊕ walk_smmu_pte ↦ gensem walk_smmu_pte_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_smmu_cfg_hw_ttbr: block.
      Hypothesis h_get_smmu_cfg_hw_ttbr_s : Genv.find_symbol ge get_smmu_cfg_hw_ttbr = Some b_get_smmu_cfg_hw_ttbr.
      Hypothesis h_get_smmu_cfg_hw_ttbr_p : Genv.find_funct_ptr ge b_get_smmu_cfg_hw_ttbr
                                            = Some (External (EF_external get_smmu_cfg_hw_ttbr
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_walk_smmu_pgd: block.
      Hypothesis h_walk_smmu_pgd_s : Genv.find_symbol ge walk_smmu_pgd = Some b_walk_smmu_pgd.
      Hypothesis h_walk_smmu_pgd_p : Genv.find_funct_ptr ge b_walk_smmu_pgd
                                     = Some (External (EF_external walk_smmu_pgd
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default).
      Variable b_walk_smmu_pmd: block.
      Hypothesis h_walk_smmu_pmd_s : Genv.find_symbol ge walk_smmu_pmd = Some b_walk_smmu_pmd.
      Hypothesis h_walk_smmu_pmd_p : Genv.find_funct_ptr ge b_walk_smmu_pmd
                                     = Some (External (EF_external walk_smmu_pmd
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default).
      Variable b_walk_smmu_pte: block.
      Hypothesis h_walk_smmu_pte_s : Genv.find_symbol ge walk_smmu_pte = Some b_walk_smmu_pte.
      Hypothesis h_walk_smmu_pte_p : Genv.find_funct_ptr ge b_walk_smmu_pte
                                     = Some (External (EF_external walk_smmu_pte
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_smmu_pt_body_correct:
        forall m d env le cbndx index addr res
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_smmu_pt_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_smmu_pt_body;
        match goal with
        | [H: context[walk_smmu_pgd_spec _ _ _ _] |- _] =>
          pose proof (walk_smmu_pgd_0_adt _ _ _ _ _ H) as e; inv e
        end;
        match goal with
        | [H: context[walk_smmu_pmd_spec _ _ _ _] |- _] =>
          pose proof (walk_smmu_pmd_0_adt _ _ _ _ _ H) as e; inv e
        end;
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_smmu_pt_code_correct:
      spec_le (walk_smmu_pt ↦ walk_smmu_pt_spec_low) (〚 walk_smmu_pt ↦ f_walk_smmu_pt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_smmu_pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_smmu_pt ) (Vint cbndx :: Vint index :: Vlong addr :: nil)
               (create_undef_temps (fn_temps f_walk_smmu_pt)))) hinv.
    Qed.

  End walk_smmu_pt_proof.

  Section set_smmu_pt_proof.

    Let L : compatlayer (cdata RData) :=
      get_smmu_cfg_hw_ttbr ↦ gensem get_smmu_cfg_hw_ttbr_spec
          ⊕ walk_smmu_pgd ↦ gensem walk_smmu_pgd_spec
          ⊕ walk_smmu_pmd ↦ gensem walk_smmu_pmd_spec
          ⊕ set_smmu_pte ↦ gensem set_smmu_pte_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_smmu_cfg_hw_ttbr: block.
      Hypothesis h_get_smmu_cfg_hw_ttbr_s : Genv.find_symbol ge get_smmu_cfg_hw_ttbr = Some b_get_smmu_cfg_hw_ttbr.
      Hypothesis h_get_smmu_cfg_hw_ttbr_p : Genv.find_funct_ptr ge b_get_smmu_cfg_hw_ttbr
                                            = Some (External (EF_external get_smmu_cfg_hw_ttbr
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_walk_smmu_pgd: block.
      Hypothesis h_walk_smmu_pgd_s : Genv.find_symbol ge walk_smmu_pgd = Some b_walk_smmu_pgd.
      Hypothesis h_walk_smmu_pgd_p : Genv.find_funct_ptr ge b_walk_smmu_pgd
                                     = Some (External (EF_external walk_smmu_pgd
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default).
      Variable b_walk_smmu_pmd: block.
      Hypothesis h_walk_smmu_pmd_s : Genv.find_symbol ge walk_smmu_pmd = Some b_walk_smmu_pmd.
      Hypothesis h_walk_smmu_pmd_p : Genv.find_funct_ptr ge b_walk_smmu_pmd
                                     = Some (External (EF_external walk_smmu_pmd
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tuint Tnil))) tulong cc_default).
      Variable b_set_smmu_pte: block.
      Hypothesis h_set_smmu_pte_s : Genv.find_symbol ge set_smmu_pte = Some b_set_smmu_pte.
      Hypothesis h_set_smmu_pte_p : Genv.find_funct_ptr ge b_set_smmu_pte
                                    = Some (External (EF_external set_smmu_pte
                                                     (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                           (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma set_smmu_pt_body_correct:
        forall m d d' env le cbndx index addr pte
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: set_smmu_pt_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_smmu_pt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_smmu_pt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_smmu_pt_code_correct:
      spec_le (set_smmu_pt ↦ set_smmu_pt_spec_low) (〚 set_smmu_pt ↦ f_set_smmu_pt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_smmu_pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_smmu_pt ) (Vint cbndx :: Vint num :: Vlong addr :: Vlong pte :: nil)
               (create_undef_temps (fn_temps f_set_smmu_pt)))) hinv.
    Qed.

  End set_smmu_pt_proof.

  Section dev_load_ref_proof.

    Let L : compatlayer (cdata RData) :=
      dev_load_raw ↦ gensem dev_load_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_dev_load_raw: block.
      Hypothesis h_dev_load_raw_s : Genv.find_symbol ge dev_load_raw = Some b_dev_load_raw.
      Hypothesis h_dev_load_raw_p : Genv.find_funct_ptr ge b_dev_load_raw
                                    = Some (External (EF_external dev_load_raw
                                                     (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default))
                                           (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma dev_load_ref_body_correct:
        forall m d d' env le gfn reg cbndx index
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: dev_load_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) dev_load_ref_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec dev_load_ref_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem dev_load_ref_code_correct:
      spec_le (dev_load_ref ↦ dev_load_ref_spec_low) (〚 dev_load_ref ↦ f_dev_load_ref 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (dev_load_ref_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_dev_load_ref ) (Vlong gfn :: Vint reg :: Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_dev_load_ref)))) hinv.
    Qed.

  End dev_load_ref_proof.

  Section dev_store_ref_proof.

    Let L : compatlayer (cdata RData) :=
      dev_store_raw ↦ gensem dev_store_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_dev_store_raw: block.
      Hypothesis h_dev_store_raw_s : Genv.find_symbol ge dev_store_raw = Some b_dev_store_raw.
      Hypothesis h_dev_store_raw_p : Genv.find_funct_ptr ge b_dev_store_raw
                                     = Some (External (EF_external dev_store_raw
                                                      (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma dev_store_ref_body_correct:
        forall m d d' env le gfn reg cbndx index
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: dev_store_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) dev_store_ref_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec dev_store_ref_body; eexists; solve_proof_low.
      Qed.
    End BodyProof.

    Theorem dev_store_ref_code_correct:
      spec_le (dev_store_ref ↦ dev_store_ref_spec_low) (〚 dev_store_ref ↦ f_dev_store_ref 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (dev_store_ref_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_dev_store_ref ) (Vlong gfn :: Vint reg :: Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_dev_store_ref)))) hinv.
    Qed.

  End dev_store_ref_proof.

End MmioSPTWalkProofLow.

```
