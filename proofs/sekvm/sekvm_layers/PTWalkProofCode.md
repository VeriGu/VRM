# PTWalkProofCode

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

Require Import PTWalk.Code.
Require Import Ident.
Require Import PTAlloc.Layer.
Require Import HypsecCommLib.
Require Import Constants.
Require Import PTAlloc.Spec.
Require Import AbstractMachine.Spec.
Require Import RData.
Require Import PTWalk.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Local Hint Unfold
      phys_page
      pmd_page
      stage2_pgd_index
      pgd_index
      pud_index
      pmd_index
      pte_index.

Section PTWalkProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section walk_pgd_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec
          ⊕ pt_load ↦ gensem pt_load_spec
          ⊕ alloc_pgd_page ↦ gensem alloc_pgd_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_alloc_pgd_page: block.
      Hypothesis h_alloc_pgd_page_s : Genv.find_symbol ge alloc_pgd_page = Some b_alloc_pgd_page.
      Hypothesis h_alloc_pgd_page_p : Genv.find_funct_ptr ge b_alloc_pgd_page
                                      = Some (External (EF_external alloc_pgd_page
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pgd_body_correct:
        forall m d d' env le vmid vttbr addr alloc res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvttbr: PTree.get _vttbr le = Some (Vlong vttbr))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pgd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned vttbr)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pgd_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pgd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_pgd_proof.

  Section walk_pud_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec
          ⊕ pt_load ↦ gensem pt_load_spec
          ⊕ alloc_pud_page ↦ gensem alloc_pud_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_alloc_pud_page: block.
      Hypothesis h_alloc_pud_page_s : Genv.find_symbol ge alloc_pud_page = Some b_alloc_pud_page.
      Hypothesis h_alloc_pud_page_p : Genv.find_funct_ptr ge b_alloc_pud_page
                                      = Some (External (EF_external alloc_pud_page
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pud_body_correct:
        forall m d d' env le vmid pgd addr alloc res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpgd: PTree.get _pgd le = Some (Vlong pgd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pud_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pgd)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pud_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pud_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_pud_proof.

  Section walk_pmd_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec
          ⊕ pt_load ↦ gensem pt_load_spec
          ⊕ alloc_pmd_page ↦ gensem alloc_pmd_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_alloc_pmd_page: block.
      Hypothesis h_alloc_pmd_page_s : Genv.find_symbol ge alloc_pmd_page = Some b_alloc_pmd_page.
      Hypothesis h_alloc_pmd_page_p : Genv.find_funct_ptr ge b_alloc_pmd_page
                                      = Some (External (EF_external alloc_pmd_page
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pmd_body_correct:
        forall m d d' env le vmid pud addr alloc res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpud: PTree.get _pud le = Some (Vlong pud))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pmd_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pmd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_pmd_proof.

  Section walk_pte_proof.

    Let L : compatlayer (cdata RData) :=
      pt_load ↦ gensem pt_load_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pte_body_correct:
        forall m d env le vmid pmd addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pte_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End walk_pte_proof.

  Section set_pmd_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma set_pmd_body_correct:
        forall m d d' env le vmid pud addr pmd
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpud: PTree.get _pud le = Some (Vlong pud))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (Hinv: high_level_invariant d)
               (Hspec: set_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pmd)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pmd_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pmd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_pmd_proof.

  Section set_pte_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma set_pte_body_correct:
        forall m d d' env le vmid pmd addr pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: set_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pte_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End set_pte_proof.

End PTWalkProofLow.

```
