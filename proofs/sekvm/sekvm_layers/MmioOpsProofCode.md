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
Require Import MmioOpsAux.Spec.
Require Import Ident.
Require Import MmioOps.Spec.
Require Import MmioSPTWalk.Spec.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioSPTOps.Spec.
Require Import MmioOps.Code.
Require Import MmioOpsAux.Layer.
Require Import VMPower.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section emulate_mmio_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ is_smmu_range ↦ gensem is_smmu_range_spec
          ⊕ handle_host_mmio ↦ gensem handle_host_mmio_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_is_smmu_range: block.
      Hypothesis h_is_smmu_range_s : Genv.find_symbol ge is_smmu_range = Some b_is_smmu_range.
      Hypothesis h_is_smmu_range_p : Genv.find_funct_ptr ge b_is_smmu_range
                                     = Some (External (EF_external is_smmu_range
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
      Variable b_handle_host_mmio: block.
      Hypothesis h_handle_host_mmio_s : Genv.find_symbol ge handle_host_mmio = Some b_handle_host_mmio.
      Hypothesis h_handle_host_mmio_p : Genv.find_funct_ptr ge b_handle_host_mmio
                                        = Some (External (EF_external handle_host_mmio
                                                         (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                               (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma emulate_mmio_body_correct:
        forall m d d' env le addr hsr res
               (Henv: env = PTree.empty _)
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (Hinv: high_level_invariant d)
               (Hspec: emulate_mmio_spec0 (VZ64 (Int64.unsigned addr)) (Int.unsigned hsr) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) emulate_mmio_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec emulate_mmio_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End emulate_mmio_proof.

  Section el2_free_smmu_pgd_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ get_vm_poweron ↦ gensem get_vm_poweron_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ set_smmu_cfg_vmid ↦ gensem set_smmu_cfg_vmid_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_vm_poweron: block.
      Hypothesis h_get_vm_poweron_s : Genv.find_symbol ge get_vm_poweron = Some b_get_vm_poweron.
      Hypothesis h_get_vm_poweron_p : Genv.find_funct_ptr ge b_get_vm_poweron
                                      = Some (External (EF_external get_vm_poweron
                                                       (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                             (Tcons tuint Tnil) tuint cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_set_smmu_cfg_vmid: block.
      Hypothesis h_set_smmu_cfg_vmid_s : Genv.find_symbol ge set_smmu_cfg_vmid = Some b_set_smmu_cfg_vmid.
      Hypothesis h_set_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_set_smmu_cfg_vmid
                                         = Some (External (EF_external set_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                                (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).

      Lemma el2_free_smmu_pgd_body_correct:
        forall m d d' env le cbndx index
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: el2_free_smmu_pgd_spec0 (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) el2_free_smmu_pgd_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec el2_free_smmu_pgd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End el2_free_smmu_pgd_proof.

  Section el2_alloc_smmu_pgd_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ get_smmu_num_context_banks ↦ gensem get_smmu_num_context_banks_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
          ⊕ set_smmu_cfg_vmid ↦ gensem set_smmu_cfg_vmid_spec
          ⊕ alloc_smmu ↦ gensem alloc_smmu_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_smmu_num_context_banks: block.
      Hypothesis h_get_smmu_num_context_banks_s : Genv.find_symbol ge get_smmu_num_context_banks = Some b_get_smmu_num_context_banks.
      Hypothesis h_get_smmu_num_context_banks_p : Genv.find_funct_ptr ge b_get_smmu_num_context_banks
                                                  = Some (External (EF_external get_smmu_num_context_banks
                                                                   (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                         (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_set_smmu_cfg_vmid: block.
      Hypothesis h_set_smmu_cfg_vmid_s : Genv.find_symbol ge set_smmu_cfg_vmid = Some b_set_smmu_cfg_vmid.
      Hypothesis h_set_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_set_smmu_cfg_vmid
                                         = Some (External (EF_external set_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                                (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_alloc_smmu: block.
      Hypothesis h_alloc_smmu_s : Genv.find_symbol ge alloc_smmu = Some b_alloc_smmu.
      Hypothesis h_alloc_smmu_p : Genv.find_funct_ptr ge b_alloc_smmu
                                = Some (External (EF_external alloc_smmu
                                                 (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma el2_alloc_smmu_pgd_body_correct:
        forall m d d' env le cbndx vmid index
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: el2_alloc_smmu_pgd_spec0 (Int.unsigned cbndx) (Int.unsigned vmid) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) el2_alloc_smmu_pgd_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec el2_alloc_smmu_pgd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End el2_alloc_smmu_pgd_proof.

  Section smmu_assign_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
          ⊕ assign_smmu ↦ gensem assign_smmu_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_assign_smmu: block.
      Hypothesis h_assign_smmu_s : Genv.find_symbol ge assign_smmu = Some b_assign_smmu.
      Hypothesis h_assign_smmu_p : Genv.find_funct_ptr ge b_assign_smmu
                                   = Some (External (EF_external assign_smmu
                                                    (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                          (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma smmu_assign_page_body_correct:
        forall m d d' env le cbndx index pfn gfn
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (Hinv: high_level_invariant d)
               (Hspec: smmu_assign_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) smmu_assign_page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec smmu_assign_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End smmu_assign_page_proof.

  Section smmu_map_page_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
          ⊕ map_smmu ↦ gensem map_smmu_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_map_smmu: block.
      Hypothesis h_map_smmu_s : Genv.find_symbol ge map_smmu = Some b_map_smmu.
      Hypothesis h_map_smmu_p : Genv.find_funct_ptr ge b_map_smmu
                                = Some (External (EF_external map_smmu
                                                 (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default))
                                       (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma smmu_map_page_body_correct:
        forall m d d' env le cbndx index iova pte
               (Henv: env = PTree.empty _)
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: smmu_map_page_spec0 (Int.unsigned cbndx) (Int.unsigned index) (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) smmu_map_page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec smmu_map_page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End smmu_map_page_proof.

  Section el2_arm_lpae_iova_to_phys_proof.

    Let L : compatlayer (cdata RData) :=
      walk_spt ↦ gensem walk_spt_spec
      ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_walk_spt: block.
      Hypothesis h_walk_spt_s : Genv.find_symbol ge walk_spt = Some b_walk_spt.
      Hypothesis h_walk_spt_p : Genv.find_funct_ptr ge b_walk_spt
                                    = Some (External (EF_external walk_spt
                                                     (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default))
                                           (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma el2_arm_lpae_iova_to_phys_body_correct:
        forall m d d' env le iova cbndx index res
               (Henv: env = PTree.empty _)
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: el2_arm_lpae_iova_to_phys_spec0 (VZ64 (Int64.unsigned iova)) (Int.unsigned cbndx) (Int.unsigned index) d = Some (d', VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) el2_arm_lpae_iova_to_phys_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        Local Hint Unfold phys_page.
        solve_code_proof Hspec el2_arm_lpae_iova_to_phys_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End el2_arm_lpae_iova_to_phys_proof.

  Section el2_arm_lpae_clear_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
          ⊕ clear_smmu ↦ gensem clear_smmu_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_smmu: block.
      Hypothesis h_acquire_lock_smmu_s : Genv.find_symbol ge acquire_lock_smmu = Some b_acquire_lock_smmu.
      Hypothesis h_acquire_lock_smmu_p : Genv.find_funct_ptr ge b_acquire_lock_smmu
                                         = Some (External (EF_external acquire_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_release_lock_smmu: block.
      Hypothesis h_release_lock_smmu_s : Genv.find_symbol ge release_lock_smmu = Some b_release_lock_smmu.
      Hypothesis h_release_lock_smmu_p : Genv.find_funct_ptr ge b_release_lock_smmu
                                         = Some (External (EF_external release_lock_smmu
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_clear_smmu: block.
      Hypothesis h_clear_smmu_s : Genv.find_symbol ge clear_smmu = Some b_clear_smmu.
      Hypothesis h_clear_smmu_p : Genv.find_funct_ptr ge b_clear_smmu
                                  = Some (External (EF_external clear_smmu
                                                   (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                         (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).

      Lemma el2_arm_lpae_clear_body_correct:
        forall m d d' env le iova cbndx index
               (Henv: env = PTree.empty _)
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: el2_arm_lpae_clear_spec0 (VZ64 (Int64.unsigned iova)) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) el2_arm_lpae_clear_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec el2_arm_lpae_clear_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End el2_arm_lpae_clear_proof.

End MmioOpsProofLow.

```
