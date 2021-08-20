# VCPUOpsAuxProofCode

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

Require Import VMPower.Spec.
Require Import AbstractMachine.Spec.
Require Import MemoryOps.Spec.
Require Import Ident.
Require Import MmioOps.Layer.
Require Import VCPUOpsAux.Spec.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import VCPUOpsAux.Code.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section VCPUOpsAuxProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section reset_gp_regs_proof.

    Let L : compatlayer (cdata RData) :=
      get_int_pc ↦ gensem get_int_pc_spec
          ⊕ search_load_info ↦ gensem search_load_info_spec
          ⊕ clear_shadow_gp_regs ↦ gensem clear_shadow_gp_regs_spec
          ⊕ get_int_pstate ↦ gensem get_int_pstate_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ reset_fp_regs ↦ gensem reset_fp_regs_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_int_pc: block.
      Hypothesis h_get_int_pc_s : Genv.find_symbol ge get_int_pc = Some b_get_int_pc.
      Hypothesis h_get_int_pc_p : Genv.find_funct_ptr ge b_get_int_pc
                                  = Some (External (EF_external get_int_pc
                                                   (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_search_load_info: block.
      Hypothesis h_search_load_info_s : Genv.find_symbol ge search_load_info = Some b_search_load_info.
      Hypothesis h_search_load_info_p : Genv.find_funct_ptr ge b_search_load_info
                                        = Some (External (EF_external search_load_info
                                                         (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                               (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_clear_shadow_gp_regs: block.
      Hypothesis h_clear_shadow_gp_regs_s : Genv.find_symbol ge clear_shadow_gp_regs = Some b_clear_shadow_gp_regs.
      Hypothesis h_clear_shadow_gp_regs_p : Genv.find_funct_ptr ge b_clear_shadow_gp_regs
                                            = Some (External (EF_external clear_shadow_gp_regs
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_get_int_pstate: block.
      Hypothesis h_get_int_pstate_s : Genv.find_symbol ge get_int_pstate = Some b_get_int_pstate.
      Hypothesis h_get_int_pstate_p : Genv.find_funct_ptr ge b_get_int_pstate
                                      = Some (External (EF_external get_int_pstate
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_reset_fp_regs: block.
      Hypothesis h_reset_fp_regs_s : Genv.find_symbol ge reset_fp_regs = Some b_reset_fp_regs.
      Hypothesis h_reset_fp_regs_p : Genv.find_funct_ptr ge b_reset_fp_regs
                                     = Some (External (EF_external reset_fp_regs
                                                      (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma reset_gp_regs_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: reset_gp_regs_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) reset_gp_regs_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec reset_gp_regs_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End reset_gp_regs_proof.

  Section prep_wfx_proof.

    Let L : compatlayer (cdata RData) :=
      set_shadow_dirty_bit ↦ gensem set_shadow_dirty_bit_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_shadow_dirty_bit: block.
      Hypothesis h_set_shadow_dirty_bit_s : Genv.find_symbol ge set_shadow_dirty_bit = Some b_set_shadow_dirty_bit.
      Hypothesis h_set_shadow_dirty_bit_p : Genv.find_funct_ptr ge b_set_shadow_dirty_bit
                                            = Some (External (EF_external set_shadow_dirty_bit
                                                             (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).

      Lemma prep_wfx_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: prep_wfx_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) prep_wfx_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec prep_wfx_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End prep_wfx_proof.

  Section prep_hvc_proof.

    Let L : compatlayer (cdata RData) :=
      set_shadow_dirty_bit ↦ gensem set_shadow_dirty_bit_spec
          ⊕ set_int_gpr ↦ gensem set_int_gpr_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ set_vm_poweroff ↦ gensem set_vm_poweroff_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_shadow_dirty_bit: block.
      Hypothesis h_set_shadow_dirty_bit_s : Genv.find_symbol ge set_shadow_dirty_bit = Some b_set_shadow_dirty_bit.
      Hypothesis h_set_shadow_dirty_bit_p : Genv.find_funct_ptr ge b_set_shadow_dirty_bit
                                            = Some (External (EF_external set_shadow_dirty_bit
                                                             (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_int_gpr: block.
      Hypothesis h_set_int_gpr_s : Genv.find_symbol ge set_int_gpr = Some b_set_int_gpr.
      Hypothesis h_set_int_gpr_p : Genv.find_funct_ptr ge b_set_int_gpr
                                   = Some (External (EF_external set_int_gpr
                                                    (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_set_vm_poweroff: block.
      Hypothesis h_set_vm_poweroff_s : Genv.find_symbol ge set_vm_poweroff = Some b_set_vm_poweroff.
      Hypothesis h_set_vm_poweroff_p : Genv.find_funct_ptr ge b_set_vm_poweroff
                                       = Some (External (EF_external set_vm_poweroff
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).

      Lemma prep_hvc_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: prep_hvc_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) prep_hvc_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec prep_hvc_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption.
      Qed.

    End BodyProof.

  End prep_hvc_proof.

  Section update_exception_gp_regs_proof.

    Let L : compatlayer (cdata RData) :=
      get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ get_exception_vector ↦ gensem get_exception_vector_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_get_exception_vector: block.
      Hypothesis h_get_exception_vector_s : Genv.find_symbol ge get_exception_vector = Some b_get_exception_vector.
      Hypothesis h_get_exception_vector_p : Genv.find_funct_ptr ge b_get_exception_vector
                                            = Some (External (EF_external get_exception_vector
                                                             (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                   (Tcons tulong Tnil) tulong cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).

      Lemma update_exception_gp_regs_body_correct:
        forall m d d' env le vmid vcpuid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: update_exception_gp_regs_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) update_exception_gp_regs_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec update_exception_gp_regs_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End update_exception_gp_regs_proof.

  Section post_handle_shadow_s2pt_fault_proof.

    Let L : compatlayer (cdata RData) :=
      get_int_new_pte ↦ gensem get_int_new_pte_spec
          ⊕ get_int_new_level ↦ gensem get_int_new_level_spec
          ⊕ prot_and_map_vm_s2pt ↦ gensem prot_and_map_vm_s2pt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_int_new_pte: block.
      Hypothesis h_get_int_new_pte_s : Genv.find_symbol ge get_int_new_pte = Some b_get_int_new_pte.
      Hypothesis h_get_int_new_pte_p : Genv.find_funct_ptr ge b_get_int_new_pte
                                       = Some (External (EF_external get_int_new_pte
                                                        (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                              (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_get_int_new_level: block.
      Hypothesis h_get_int_new_level_s : Genv.find_symbol ge get_int_new_level = Some b_get_int_new_level.
      Hypothesis h_get_int_new_level_p : Genv.find_funct_ptr ge b_get_int_new_level
                                       = Some (External (EF_external get_int_new_level
                                                        (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                              (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_prot_and_map_vm_s2pt: block.
      Hypothesis h_prot_and_map_vm_s2pt_s : Genv.find_symbol ge prot_and_map_vm_s2pt = Some b_prot_and_map_vm_s2pt.
      Hypothesis h_prot_and_map_vm_s2pt_p : Genv.find_funct_ptr ge b_prot_and_map_vm_s2pt
                                            = Some (External (EF_external prot_and_map_vm_s2pt
                                                             (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma post_handle_shadow_s2pt_fault_body_correct:
        forall m d d' env le vmid vcpuid addr
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: post_handle_shadow_s2pt_fault_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) (VZ64 (Int64.unsigned addr)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) post_handle_shadow_s2pt_fault_body E0 le' (m, d') Out_normal).
      Proof.
        Local Opaque prot_and_map_vm_s2pt_spec.
        solve_code_proof Hspec post_handle_shadow_s2pt_fault_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End post_handle_shadow_s2pt_fault_proof.

End VCPUOpsAuxProofLow.
```
