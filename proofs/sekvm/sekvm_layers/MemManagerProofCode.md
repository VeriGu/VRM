# MemManagerProofCode

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

Require Import PageManager.Spec.
Require Import NPTOps.Spec.
Require Import AbstractMachine.Spec.
Require Import MemManager.Spec.
Require Import Ident.
Require Import MmioSPTOps.Spec.
Require Import RData.
Require Import PageManager.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MemManager.Code.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemManagerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section map_page_host_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ map_s2pt ↦ gensem map_s2pt_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_map_s2pt: block.
      Hypothesis h_map_s2pt_s : Genv.find_symbol ge map_s2pt = Some b_map_s2pt.
      Hypothesis h_map_s2pt_p : Genv.find_funct_ptr ge b_map_s2pt
                                = Some (External (EF_external map_s2pt
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma map_page_host_body_correct:
        forall m d d' env le addr
               (Henv: env = PTree.empty _)
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: map_page_host_spec0 (VZ64 (Int64.unsigned addr)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_page_host_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_page_host_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End map_page_host_proof.

  Section clear_vm_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ clear_pfn_host ↦ gensem clear_pfn_host_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ set_pfn_owner ↦ gensem set_pfn_owner_spec
          ⊕ set_pfn_map ↦ gensem set_pfn_map_spec
          ⊕ clear_phys_page ↦ gensem clear_phys_page_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_clear_pfn_host: block.
      Hypothesis h_clear_pfn_host_s : Genv.find_symbol ge clear_pfn_host = Some b_clear_pfn_host.
      Hypothesis h_clear_pfn_host_p : Genv.find_funct_ptr ge b_clear_pfn_host
                                      = Some (External (EF_external clear_pfn_host
                                                       (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                             (Tcons tulong Tnil) tvoid cc_default).
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_pfn_owner: block.
      Hypothesis h_set_pfn_owner_s : Genv.find_symbol ge set_pfn_owner = Some b_set_pfn_owner.
      Hypothesis h_set_pfn_owner_p : Genv.find_funct_ptr ge b_set_pfn_owner
                                     = Some (External (EF_external set_pfn_owner
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_pfn_map: block.
      Hypothesis h_set_pfn_map_s : Genv.find_symbol ge set_pfn_map = Some b_set_pfn_map.
      Hypothesis h_set_pfn_map_p : Genv.find_funct_ptr ge b_set_pfn_map
                                     = Some (External (EF_external set_pfn_map
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_clear_phys_page: block.
      Hypothesis h_clear_phys_page_s : Genv.find_symbol ge clear_phys_page = Some b_clear_phys_page.
      Hypothesis h_clear_phys_page_p : Genv.find_funct_ptr ge b_clear_phys_page
                                       = Some (External (EF_external clear_phys_page
                                                        (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                              (Tcons tulong Tnil) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma clear_vm_page_body_correct:
        forall m d d' env le vmid pfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: clear_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_vm_page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_vm_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End clear_vm_page_proof.

  Section assign_pfn_to_vm_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ get_pfn_map ↦ gensem get_pfn_map_spec
          ⊕ set_pfn_owner ↦ gensem set_pfn_owner_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ set_pfn_map ↦ gensem set_pfn_map_spec
          ⊕ clear_pfn_host ↦ gensem clear_pfn_host_spec
          ⊕ fetch_from_doracle ↦ gensem fetch_from_doracle_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_map: block.
      Hypothesis h_get_pfn_map_s : Genv.find_symbol ge get_pfn_map = Some b_get_pfn_map.
      Hypothesis h_get_pfn_map_p : Genv.find_funct_ptr ge b_get_pfn_map
                                   = Some (External (EF_external get_pfn_map
                                                    (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                          (Tcons tulong Tnil) tulong cc_default).
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
      Variable b_fetch_from_doracle: block.
      Hypothesis h_fetch_from_doracle_s : Genv.find_symbol ge fetch_from_doracle = Some b_fetch_from_doracle.
      Hypothesis h_fetch_from_doracle_p : Genv.find_funct_ptr ge b_fetch_from_doracle
                                          = Some (External (EF_external fetch_from_doracle
                                                           (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                 (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma assign_pfn_to_vm_body_correct:
        forall m d d' env le vmid gfn pfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: assign_pfn_to_vm_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gfn)) (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) assign_pfn_to_vm_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec assign_pfn_to_vm_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption. assumption.
      Qed.

    End BodyProof.

  End assign_pfn_to_vm_proof.

  Section map_pfn_vm_proof.

    Let L : compatlayer (cdata RData) :=
      map_s2pt ↦ gensem map_s2pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_map_s2pt: block.
      Hypothesis h_map_s2pt_s : Genv.find_symbol ge map_s2pt = Some b_map_s2pt.
      Hypothesis h_map_s2pt_p : Genv.find_funct_ptr ge b_map_s2pt
                                = Some (External (EF_external map_s2pt
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).

      Lemma map_pfn_vm_body_correct:
        forall m d d' env le vmid addr pte level
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (HPTlevel: PTree.get _level le = Some (Vint level))
               (Hinv: high_level_invariant d)
               (Hspec: map_pfn_vm_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) (Int.unsigned level) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_pfn_vm_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_pfn_vm_body;
        eexists; repeat (repeat (try replace (Int64.unsigned (Int64.repr (-3))) with 18446744073709551613 by reflexivity; sstep); big_vcgen).
      Qed.

    End BodyProof.

  End map_pfn_vm_proof.

  Section map_vm_io_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ map_s2pt ↦ gensem map_s2pt_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_map_s2pt: block.
      Hypothesis h_map_s2pt_s : Genv.find_symbol ge map_s2pt = Some b_map_s2pt.
      Hypothesis h_map_s2pt_p : Genv.find_funct_ptr ge b_map_s2pt
                                = Some (External (EF_external map_s2pt
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma map_vm_io_body_correct:
        forall m d d' env le vmid gpa pa
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTgpa: PTree.get _gpa le = Some (Vlong gpa))
               (HPTpa: PTree.get _pa le = Some (Vlong pa))
               (Hinv: high_level_invariant d)
               (Hspec: map_vm_io_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gpa)) (VZ64 (Int64.unsigned pa)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) map_vm_io_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec map_vm_io_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End map_vm_io_proof.

  Section grant_vm_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma grant_vm_page_body_correct:
        forall m d d' env le vmid pfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: grant_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) grant_vm_page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec grant_vm_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End grant_vm_page_proof.

  Section revoke_vm_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ clear_pfn_host ↦ gensem clear_pfn_host_spec
          ⊕ fetch_from_doracle ↦ gensem fetch_from_doracle_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_clear_pfn_host: block.
      Hypothesis h_clear_pfn_host_s : Genv.find_symbol ge clear_pfn_host = Some b_clear_pfn_host.
      Hypothesis h_clear_pfn_host_p : Genv.find_funct_ptr ge b_clear_pfn_host
                                      = Some (External (EF_external clear_pfn_host
                                                       (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                             (Tcons tulong Tnil) tvoid cc_default).
      Variable b_fetch_from_doracle: block.
      Hypothesis h_fetch_from_doracle_s : Genv.find_symbol ge fetch_from_doracle = Some b_fetch_from_doracle.
      Hypothesis h_fetch_from_doracle_p : Genv.find_funct_ptr ge b_fetch_from_doracle
                                          = Some (External (EF_external fetch_from_doracle
                                                           (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                 (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma revoke_vm_page_body_correct:
        forall m d d' env le vmid pfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: revoke_vm_page_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) revoke_vm_page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec revoke_vm_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End revoke_vm_page_proof.

  Section assign_pfn_to_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ get_pfn_map ↦ gensem get_pfn_map_spec
          ⊕ set_pfn_owner ↦ gensem set_pfn_owner_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ set_pfn_map ↦ gensem set_pfn_map_spec
          ⊕ clear_pfn_host ↦ gensem clear_pfn_host_spec
          ⊕ fetch_from_doracle ↦ gensem fetch_from_doracle_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_map: block.
      Hypothesis h_get_pfn_map_s : Genv.find_symbol ge get_pfn_map = Some b_get_pfn_map.
      Hypothesis h_get_pfn_map_p : Genv.find_funct_ptr ge b_get_pfn_map
                                   = Some (External (EF_external get_pfn_map
                                                    (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                          (Tcons tulong Tnil) tulong cc_default).
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
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma assign_pfn_to_smmu_body_correct:
        forall m d d' env le vmid gfn pfn
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: assign_pfn_to_smmu_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned gfn)) (VZ64 (Int64.unsigned pfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) assign_pfn_to_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec assign_pfn_to_smmu_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End assign_pfn_to_smmu_proof.

  Section update_smmu_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_map ↦ gensem get_pfn_map_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ map_spt ↦ gensem map_spt_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
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
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_map: block.
      Hypothesis h_get_pfn_map_s : Genv.find_symbol ge get_pfn_map = Some b_get_pfn_map.
      Hypothesis h_get_pfn_map_p : Genv.find_funct_ptr ge b_get_pfn_map
                                   = Some (External (EF_external get_pfn_map
                                                    (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                          (Tcons tulong Tnil) tulong cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_map_spt: block.
      Hypothesis h_map_spt_s : Genv.find_symbol ge map_spt = Some b_map_spt.
      Hypothesis h_map_spt_p : Genv.find_funct_ptr ge b_map_spt
                               = Some (External (EF_external map_spt
                                                (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                      (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma update_smmu_page_body_correct:
        forall m d d' env le vmid cbndx index iova pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: update_smmu_page_spec0 (Int.unsigned vmid) (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) update_smmu_page_body E0 le' (m, d') Out_normal).
      Proof.
        Local Hint Unfold phys_page.
        solve_code_proof Hspec update_smmu_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End update_smmu_page_proof.

  Section unmap_smmu_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ unmap_spt ↦ gensem unmap_spt_spec
          ⊕ get_pfn_owner ↦ gensem get_pfn_owner_spec
          ⊕ get_pfn_count ↦ gensem get_pfn_count_spec
          ⊕ set_pfn_count ↦ gensem set_pfn_count_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec.

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
      Variable b_unmap_spt: block.
      Hypothesis h_unmap_spt_s : Genv.find_symbol ge unmap_spt = Some b_unmap_spt.
      Hypothesis h_unmap_spt_p : Genv.find_funct_ptr ge b_unmap_spt
                                 = Some (External (EF_external unmap_spt
                                                  (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default))
                                        (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default).
      Variable b_get_pfn_owner: block.
      Hypothesis h_get_pfn_owner_s : Genv.find_symbol ge get_pfn_owner = Some b_get_pfn_owner.
      Hypothesis h_get_pfn_owner_p : Genv.find_funct_ptr ge b_get_pfn_owner
                                     = Some (External (EF_external get_pfn_owner
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_pfn_count: block.
      Hypothesis h_get_pfn_count_s : Genv.find_symbol ge get_pfn_count = Some b_get_pfn_count.
      Hypothesis h_get_pfn_count_p : Genv.find_funct_ptr ge b_get_pfn_count
                                     = Some (External (EF_external get_pfn_count
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_set_pfn_count: block.
      Hypothesis h_set_pfn_count_s : Genv.find_symbol ge set_pfn_count = Some b_set_pfn_count.
      Hypothesis h_set_pfn_count_p : Genv.find_funct_ptr ge b_set_pfn_count
                                     = Some (External (EF_external set_pfn_count
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_release_lock_s2page: block.
      Hypothesis h_release_lock_s2page_s : Genv.find_symbol ge release_lock_s2page = Some b_release_lock_s2page.
      Hypothesis h_release_lock_s2page_p : Genv.find_funct_ptr ge b_release_lock_s2page
                                           = Some (External (EF_external release_lock_s2page
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma unmap_smmu_page_body_correct:
        forall m d d' env le cbndx index iova
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (Hinv: high_level_invariant d)
               (Hspec: unmap_smmu_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) unmap_smmu_page_body E0 le' (m, d') Out_normal).
      Proof.
        Local Hint Unfold phys_page.
        solve_code_proof Hspec unmap_smmu_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End unmap_smmu_page_proof.

End MemManagerProofLow.

```
