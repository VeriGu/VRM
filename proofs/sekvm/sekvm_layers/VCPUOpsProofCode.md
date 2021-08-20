# VCPUOpsProofCode

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

Require Import VCPUOps.Code.
Require Import AbstractMachine.Spec.
Require Import Ident.
Require Import VCPUOps.Spec.
Require Import VCPUOpsAux.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import VCPUOpsAux.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section VCPUOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section save_shadow_kvm_regs_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ get_shadow_esr ↦ gensem get_shadow_esr_spec
          ⊕ prep_abort ↦ gensem prep_abort_spec
          ⊕ prep_hvc ↦ gensem prep_hvc_spec
          ⊕ prep_wfx ↦ gensem prep_wfx_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_cur_vmid: block.
      Hypothesis h_get_cur_vmid_s : Genv.find_symbol ge get_cur_vmid = Some b_get_cur_vmid.
      Hypothesis h_get_cur_vmid_p : Genv.find_funct_ptr ge b_get_cur_vmid
                                    = Some (External (EF_external get_cur_vmid
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
      Variable b_get_cur_vcpuid: block.
      Hypothesis h_get_cur_vcpuid_s : Genv.find_symbol ge get_cur_vcpuid = Some b_get_cur_vcpuid.
      Hypothesis h_get_cur_vcpuid_p : Genv.find_funct_ptr ge b_get_cur_vcpuid
                                      = Some (External (EF_external get_cur_vcpuid
                                                       (signature_of_type Tnil tuint cc_default))
                                             Tnil tuint cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_get_shadow_esr: block.
      Hypothesis h_get_shadow_esr_s : Genv.find_symbol ge get_shadow_esr = Some b_get_shadow_esr.
      Hypothesis h_get_shadow_esr_p : Genv.find_funct_ptr ge b_get_shadow_esr
                                      = Some (External (EF_external get_shadow_esr
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_prep_abort: block.
      Hypothesis h_prep_abort_s : Genv.find_symbol ge prep_abort = Some b_prep_abort.
      Hypothesis h_prep_abort_p : Genv.find_funct_ptr ge b_prep_abort
                                  = Some (External (EF_external prep_abort
                                                   (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_prep_hvc: block.
      Hypothesis h_prep_hvc_s : Genv.find_symbol ge prep_hvc = Some b_prep_hvc.
      Hypothesis h_prep_hvc_p : Genv.find_funct_ptr ge b_prep_hvc
                                = Some (External (EF_external prep_hvc
                                                 (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                       (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_prep_wfx: block.
      Hypothesis h_prep_wfx_s : Genv.find_symbol ge prep_wfx = Some b_prep_wfx.
      Hypothesis h_prep_wfx_p : Genv.find_funct_ptr ge b_prep_wfx
                                = Some (External (EF_external prep_wfx
                                                 (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                       (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma save_shadow_kvm_regs_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: save_shadow_kvm_regs_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) save_shadow_kvm_regs_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec save_shadow_kvm_regs_body; admit
      Qed.
    End BodyProof.

    Theorem save_shadow_kvm_regs_code_correct:
      spec_le (save_shadow_kvm_regs ↦ save_shadow_kvm_regs_spec_low) (〚 save_shadow_kvm_regs ↦ f_save_shadow_kvm_regs 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (save_shadow_kvm_regs_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_save_shadow_kvm_regs ) ( :: nil)
               (create_undef_temps (fn_temps f_save_shadow_kvm_regs)))) hinv.
    Qed.
  End save_shadow_kvm_regs_proof.

  Section restore_shadow_kvm_regs_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ reset_gp_regs ↦ gensem reset_gp_regs_spec
          ⊕ reset_sys_regs ↦ gensem reset_sys_regs_spec
          ⊕ set_shadow_dirty_bit ↦ gensem set_shadow_dirty_bit_spec
          ⊕ sync_dirty_to_shadow ↦ gensem sync_dirty_to_shadow_spec
          ⊕ update_exception_gp_regs ↦ gensem update_exception_gp_regs_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ get_vm_fault_addr ↦ gensem get_vm_fault_addr_spec
          ⊕ post_handle_shadow_s2pt_fault ↦ gensem post_handle_shadow_s2pt_fault_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_cur_vmid: block.
      Hypothesis h_get_cur_vmid_s : Genv.find_symbol ge get_cur_vmid = Some b_get_cur_vmid.
      Hypothesis h_get_cur_vmid_p : Genv.find_funct_ptr ge b_get_cur_vmid
                                    = Some (External (EF_external get_cur_vmid
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
      Variable b_get_cur_vcpuid: block.
      Hypothesis h_get_cur_vcpuid_s : Genv.find_symbol ge get_cur_vcpuid = Some b_get_cur_vcpuid.
      Hypothesis h_get_cur_vcpuid_p : Genv.find_funct_ptr ge b_get_cur_vcpuid
                                      = Some (External (EF_external get_cur_vcpuid
                                                       (signature_of_type Tnil tuint cc_default))
                                             Tnil tuint cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_reset_gp_regs: block.
      Hypothesis h_reset_gp_regs_s : Genv.find_symbol ge reset_gp_regs = Some b_reset_gp_regs.
      Hypothesis h_reset_gp_regs_p : Genv.find_funct_ptr ge b_reset_gp_regs
                                     = Some (External (EF_external reset_gp_regs
                                                      (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_reset_sys_regs: block.
      Hypothesis h_reset_sys_regs_s : Genv.find_symbol ge reset_sys_regs = Some b_reset_sys_regs.
      Hypothesis h_reset_sys_regs_p : Genv.find_funct_ptr ge b_reset_sys_regs
                                      = Some (External (EF_external reset_sys_regs
                                                       (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_shadow_dirty_bit: block.
      Hypothesis h_set_shadow_dirty_bit_s : Genv.find_symbol ge set_shadow_dirty_bit = Some b_set_shadow_dirty_bit.
      Hypothesis h_set_shadow_dirty_bit_p : Genv.find_funct_ptr ge b_set_shadow_dirty_bit
                                            = Some (External (EF_external set_shadow_dirty_bit
                                                             (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_sync_dirty_to_shadow: block.
      Hypothesis h_sync_dirty_to_shadow_s : Genv.find_symbol ge sync_dirty_to_shadow = Some b_sync_dirty_to_shadow.
      Hypothesis h_sync_dirty_to_shadow_p : Genv.find_funct_ptr ge b_sync_dirty_to_shadow
                                            = Some (External (EF_external sync_dirty_to_shadow
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_update_exception_gp_regs: block.
      Hypothesis h_update_exception_gp_regs_s : Genv.find_symbol ge update_exception_gp_regs = Some b_update_exception_gp_regs.
      Hypothesis h_update_exception_gp_regs_p : Genv.find_funct_ptr ge b_update_exception_gp_regs
                                                = Some (External (EF_external update_exception_gp_regs
                                                                 (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                                       (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_get_vm_fault_addr: block.
      Hypothesis h_get_vm_fault_addr_s : Genv.find_symbol ge get_vm_fault_addr = Some b_get_vm_fault_addr.
      Hypothesis h_get_vm_fault_addr_p : Genv.find_funct_ptr ge b_get_vm_fault_addr
                                         = Some (External (EF_external get_vm_fault_addr
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b_post_handle_shadow_s2pt_fault: block.
      Hypothesis h_post_handle_shadow_s2pt_fault_s : Genv.find_symbol ge post_handle_shadow_s2pt_fault = Some b_post_handle_shadow_s2pt_fault.
      Hypothesis h_post_handle_shadow_s2pt_fault_p : Genv.find_funct_ptr ge b_post_handle_shadow_s2pt_fault
                                                     = Some (External (EF_external post_handle_shadow_s2pt_fault
                                                                      (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                            (Tcons tuint (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).

      Lemma restore_shadow_kvm_regs_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: restore_shadow_kvm_regs_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) restore_shadow_kvm_regs_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec restore_shadow_kvm_regs_body; admit
      Qed.
    End BodyProof.

    Theorem restore_shadow_kvm_regs_code_correct:
      spec_le (restore_shadow_kvm_regs ↦ restore_shadow_kvm_regs_spec_low) (〚 restore_shadow_kvm_regs ↦ f_restore_shadow_kvm_regs 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (restore_shadow_kvm_regs_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp b8 Hb8fs Hb8fp b9 Hb9fs Hb9fp b10 Hb10fs Hb10fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_restore_shadow_kvm_regs ) ( :: nil)
               (create_undef_temps (fn_temps f_restore_shadow_kvm_regs)))) hinv.
    Qed.
  End restore_shadow_kvm_regs_proof.

End VCPUOpsProofLow.

```
