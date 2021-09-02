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

Require Import NPTWalk.Code.
Require Import Ident.
Require Import HypsecCommLib.
Require Import Constants.
Require Import NPTWalk.Spec.
Require Import PTWalk.Layer.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import PTWalk.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Lemma walk_pgd_0_adt:
  forall vmid vttbr addr adt adt' res (Hspec: walk_pgd_spec vmid vttbr addr 0 adt = Some (adt', res)),
    adt = adt'.
Proof.
  intros. hsimpl_func Hspec; bool_rel_all; try reflexivity; try omega.
Qed.

Lemma walk_pud_0_adt:
  forall vmid pgd addr adt adt' res (Hspec: walk_pud_spec vmid pgd addr 0 adt = Some (adt', res)),
    adt = adt'.
Proof.
  intros. hsimpl_func Hspec; bool_rel_all; try reflexivity; try omega.
Qed.

Lemma walk_pmd_0_adt:
  forall vmid pud addr adt adt' res (Hspec: walk_pmd_spec vmid pud addr 0 adt = Some (adt', res)),
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

Section NPTWalkProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section get_npt_level_proof.

    Let L : compatlayer (cdata RData) :=
      get_pt_vttbr ↦ gensem get_pt_vttbr_spec
          ⊕ walk_pgd ↦ gensem walk_pgd_spec
          ⊕ walk_pud ↦ gensem walk_pud_spec
          ⊕ walk_pmd ↦ gensem walk_pmd_spec
          ⊕ walk_pte ↦ gensem walk_pte_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pt_vttbr: block.
      Hypothesis h_get_pt_vttbr_s : Genv.find_symbol ge get_pt_vttbr = Some b_get_pt_vttbr.
      Hypothesis h_get_pt_vttbr_p : Genv.find_funct_ptr ge b_get_pt_vttbr
                                    = Some (External (EF_external get_pt_vttbr
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_walk_pgd: block.
      Hypothesis h_walk_pgd_s : Genv.find_symbol ge walk_pgd = Some b_walk_pgd.
      Hypothesis h_walk_pgd_p : Genv.find_funct_ptr ge b_walk_pgd
                                = Some (External (EF_external walk_pgd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pud: block.
      Hypothesis h_walk_pud_s : Genv.find_symbol ge walk_pud = Some b_walk_pud.
      Hypothesis h_walk_pud_p : Genv.find_funct_ptr ge b_walk_pud
                                = Some (External (EF_external walk_pud
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pmd: block.
      Hypothesis h_walk_pmd_s : Genv.find_symbol ge walk_pmd = Some b_walk_pmd.
      Hypothesis h_walk_pmd_p : Genv.find_funct_ptr ge b_walk_pmd
                                = Some (External (EF_external walk_pmd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pte: block.
      Hypothesis h_walk_pte_s : Genv.find_symbol ge walk_pte = Some b_walk_pte.
      Hypothesis h_walk_pte_p : Genv.find_funct_ptr ge b_walk_pte
                                = Some (External (EF_external walk_pte
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tulong cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma get_npt_level_body_correct:
        forall m d env le vmid addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: get_npt_level_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) get_npt_level_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec get_npt_level_body;
        match goal with
        | [H: context[walk_pgd_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pgd_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        match goal with
        | [H: context[walk_pud_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pud_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        match goal with
        | [H: context[walk_pmd_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pmd_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End get_npt_level_proof.

  Section walk_npt_proof.

    Let L : compatlayer (cdata RData) :=
      get_pt_vttbr ↦ gensem get_pt_vttbr_spec
          ⊕ walk_pgd ↦ gensem walk_pgd_spec
          ⊕ walk_pud ↦ gensem walk_pud_spec
          ⊕ walk_pmd ↦ gensem walk_pmd_spec
          ⊕ walk_pte ↦ gensem walk_pte_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pt_vttbr: block.
      Hypothesis h_get_pt_vttbr_s : Genv.find_symbol ge get_pt_vttbr = Some b_get_pt_vttbr.
      Hypothesis h_get_pt_vttbr_p : Genv.find_funct_ptr ge b_get_pt_vttbr
                                    = Some (External (EF_external get_pt_vttbr
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_walk_pgd: block.
      Hypothesis h_walk_pgd_s : Genv.find_symbol ge walk_pgd = Some b_walk_pgd.
      Hypothesis h_walk_pgd_p : Genv.find_funct_ptr ge b_walk_pgd
                                = Some (External (EF_external walk_pgd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pud: block.
      Hypothesis h_walk_pud_s : Genv.find_symbol ge walk_pud = Some b_walk_pud.
      Hypothesis h_walk_pud_p : Genv.find_funct_ptr ge b_walk_pud
                                = Some (External (EF_external walk_pud
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pmd: block.
      Hypothesis h_walk_pmd_s : Genv.find_symbol ge walk_pmd = Some b_walk_pmd.
      Hypothesis h_walk_pmd_p : Genv.find_funct_ptr ge b_walk_pmd
                                = Some (External (EF_external walk_pmd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pte: block.
      Hypothesis h_walk_pte_s : Genv.find_symbol ge walk_pte = Some b_walk_pte.
      Hypothesis h_walk_pte_p : Genv.find_funct_ptr ge b_walk_pte
                                = Some (External (EF_external walk_pte
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_npt_body_correct:
        forall m d env le vmid addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_npt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_npt_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_npt_body;
        match goal with
        | [H: context[walk_pgd_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pgd_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        match goal with
        | [H: context[walk_pud_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pud_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        match goal with
        | [H: context[walk_pmd_spec _ _ _ _ _] |- _] =>
          pose proof (walk_pmd_0_adt _ _ _ _ _ _ H) as e; inv e
        end;
        eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_npt_proof.

  Section set_npt_proof.

    Let L : compatlayer (cdata RData) :=
      get_pt_vttbr ↦ gensem get_pt_vttbr_spec
          ⊕ walk_pgd ↦ gensem walk_pgd_spec
          ⊕ walk_pud ↦ gensem walk_pud_spec
          ⊕ walk_pmd ↦ gensem walk_pmd_spec
          ⊕ set_pmd ↦ gensem set_pmd_spec
          ⊕ set_pte ↦ gensem set_pte_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_pt_vttbr: block.
      Hypothesis h_get_pt_vttbr_s : Genv.find_symbol ge get_pt_vttbr = Some b_get_pt_vttbr.
      Hypothesis h_get_pt_vttbr_p : Genv.find_funct_ptr ge b_get_pt_vttbr
                                    = Some (External (EF_external get_pt_vttbr
                                                     (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                           (Tcons tuint Tnil) tulong cc_default).
      Variable b_walk_pgd: block.
      Hypothesis h_walk_pgd_s : Genv.find_symbol ge walk_pgd = Some b_walk_pgd.
      Hypothesis h_walk_pgd_p : Genv.find_funct_ptr ge b_walk_pgd
                                = Some (External (EF_external walk_pgd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pud: block.
      Hypothesis h_walk_pud_s : Genv.find_symbol ge walk_pud = Some b_walk_pud.
      Hypothesis h_walk_pud_p : Genv.find_funct_ptr ge b_walk_pud
                                = Some (External (EF_external walk_pud
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_walk_pmd: block.
      Hypothesis h_walk_pmd_s : Genv.find_symbol ge walk_pmd = Some b_walk_pmd.
      Hypothesis h_walk_pmd_p : Genv.find_funct_ptr ge b_walk_pmd
                                = Some (External (EF_external walk_pmd
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tulong cc_default).
      Variable b_set_pmd: block.
      Hypothesis h_set_pmd_s : Genv.find_symbol ge set_pmd = Some b_set_pmd.
      Hypothesis h_set_pmd_p : Genv.find_funct_ptr ge b_set_pmd
                               = Some (External (EF_external set_pmd
                                                (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                      (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_set_pte: block.
      Hypothesis h_set_pte_s : Genv.find_symbol ge set_pte = Some b_set_pte.
      Hypothesis h_set_pte_p : Genv.find_funct_ptr ge b_set_pte
                               = Some (External (EF_external set_pte
                                                (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                      (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma set_npt_body_correct:
        forall m d d' env le vmid addr level pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTlevel: PTree.get _level le = Some (Vint level))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: set_npt_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (Int.unsigned level) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_npt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_npt_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_npt_proof.

  Section mem_load_ref_proof.

    Let L : compatlayer (cdata RData) :=
      mem_load_raw ↦ gensem mem_load_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_mem_load_raw: block.
      Hypothesis h_mem_load_raw_s : Genv.find_symbol ge mem_load_raw = Some b_mem_load_raw.
      Hypothesis h_mem_load_raw_p : Genv.find_funct_ptr ge b_mem_load_raw
                                    = Some (External (EF_external mem_load_raw
                                                     (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                           (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).

      Lemma mem_load_ref_body_correct:
        forall m d d' env le gfn reg
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (Hinv: high_level_invariant d)
               (Hspec: mem_load_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) mem_load_ref_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec mem_load_ref_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End mem_load_ref_proof.

  Section mem_store_ref_proof.

    Let L : compatlayer (cdata RData) :=
      mem_store_raw ↦ gensem mem_store_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_mem_store_raw: block.
      Hypothesis h_mem_store_raw_s : Genv.find_symbol ge mem_store_raw = Some b_mem_store_raw.
      Hypothesis h_mem_store_raw_p : Genv.find_funct_ptr ge b_mem_store_raw
                                     = Some (External (EF_external mem_store_raw
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).

      Lemma mem_store_ref_body_correct:
        forall m d d' env le gfn reg
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (Hinv: high_level_invariant d)
               (Hspec: mem_store_ref_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) mem_store_ref_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec mem_store_ref_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End mem_store_ref_proof.

End NPTWalkProofLow.

```
