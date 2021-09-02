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
Require Import CtxtSwitch.Code.
Require Import CtxtSwitch.Spec.
Require Import BootOps.Spec.
Require Import Ident.
Require Import VCPUOps.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import VCPUOps.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section CtxtSwitchProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section save_host_proof.

    Let L : compatlayer (cdata RData) :=
      save_sysregs ↦ gensem save_sysregs_spec
          ⊕ fpsimd_save_state ↦ gensem fpsimd_save_state_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_save_sysregs: block.
      Hypothesis h_save_sysregs_s : Genv.find_symbol ge save_sysregs = Some b_save_sysregs.
      Hypothesis h_save_sysregs_p : Genv.find_funct_ptr ge b_save_sysregs
                                    = Some (External (EF_external save_sysregs
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_fpsimd_save_state: block.
      Hypothesis h_fpsimd_save_state_s : Genv.find_symbol ge fpsimd_save_state = Some b_fpsimd_save_state.
      Hypothesis h_fpsimd_save_state_p : Genv.find_funct_ptr ge b_fpsimd_save_state
                                         = Some (External (EF_external fpsimd_save_state
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).

      Lemma save_host_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: save_host_spec  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) save_host_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec save_host_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem save_host_code_correct:
      spec_le (save_host ↦ save_host_spec_low) (〚 save_host ↦ f_save_host 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (save_host_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_save_host ) nil
               (create_undef_temps (fn_temps f_save_host)))) hinv.
    Qed.

  End save_host_proof.

  Section restore_host_proof.

    Let L : compatlayer (cdata RData) :=
      set_per_cpu ↦ gensem set_per_cpu_spec
          ⊕ host_el2_restore_state ↦ gensem host_el2_restore_state_spec
          ⊕ restore_sysregs ↦ gensem restore_sysregs_spec
          ⊕ fpsimd_restore_state ↦ gensem fpsimd_restore_state_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_per_cpu: block.
      Hypothesis h_set_per_cpu_s : Genv.find_symbol ge set_per_cpu = Some b_set_per_cpu.
      Hypothesis h_set_per_cpu_p : Genv.find_funct_ptr ge b_set_per_cpu
                                   = Some (External (EF_external set_per_cpu
                                                    (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_host_el2_restore_state: block.
      Hypothesis h_host_el2_restore_state_s : Genv.find_symbol ge host_el2_restore_state = Some b_host_el2_restore_state.
      Hypothesis h_host_el2_restore_state_p : Genv.find_funct_ptr ge b_host_el2_restore_state
                                              = Some (External (EF_external host_el2_restore_state
                                                               (signature_of_type Tnil tvoid cc_default))
                                                     Tnil tvoid cc_default).
      Variable b_restore_sysregs: block.
      Hypothesis h_restore_sysregs_s : Genv.find_symbol ge restore_sysregs = Some b_restore_sysregs.
      Hypothesis h_restore_sysregs_p : Genv.find_funct_ptr ge b_restore_sysregs
                                       = Some (External (EF_external restore_sysregs
                                                        (signature_of_type Tnil tvoid cc_default))
                                              Tnil tvoid cc_default).
      Variable b_fpsimd_restore_state: block.
      Hypothesis h_fpsimd_restore_state_s : Genv.find_symbol ge fpsimd_restore_state = Some b_fpsimd_restore_state.
      Hypothesis h_fpsimd_restore_state_p : Genv.find_funct_ptr ge b_fpsimd_restore_state
                                         = Some (External (EF_external fpsimd_restore_state
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).

      Lemma restore_host_body_correct:
        forall m d d' env le
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: restore_host_spec  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) restore_host_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec restore_host_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem restore_host_code_correct:
      spec_le (restore_host ↦ restore_host_spec_low) (〚 restore_host ↦ f_restore_host 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (restore_host_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_restore_host ) nil
               (create_undef_temps (fn_temps f_restore_host)))) hinv.
    Qed.

  End restore_host_proof.

  Section save_vm_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ save_sysregs ↦ gensem save_sysregs_spec
          ⊕ fpsimd_save_state ↦ gensem fpsimd_save_state_spec
          ⊕ deactivate_traps ↦ gensem deactivate_traps_spec
          ⊕ timer_enable_traps ↦ gensem timer_enable_traps_spec
          ⊕ set_vcpu_inactive ↦ gensem set_vcpu_inactive_spec
          ⊕ save_shadow_kvm_regs ↦ gensem save_shadow_kvm_regs_spec.

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
      Variable b_save_sysregs: block.
      Hypothesis h_save_sysregs_s : Genv.find_symbol ge save_sysregs = Some b_save_sysregs.
      Hypothesis h_save_sysregs_p : Genv.find_funct_ptr ge b_save_sysregs
                                    = Some (External (EF_external save_sysregs
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_fpsimd_save_state: block.
      Hypothesis h_fpsimd_save_state_s : Genv.find_symbol ge fpsimd_save_state = Some b_fpsimd_save_state.
      Hypothesis h_fpsimd_save_state_p : Genv.find_funct_ptr ge b_fpsimd_save_state
                                         = Some (External (EF_external fpsimd_save_state
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_deactivate_traps: block.
      Hypothesis h_deactivate_traps_s : Genv.find_symbol ge deactivate_traps = Some b_deactivate_traps.
      Hypothesis h_deactivate_traps_p : Genv.find_funct_ptr ge b_deactivate_traps
                                        = Some (External (EF_external deactivate_traps
                                                         (signature_of_type Tnil tvoid cc_default))
                                               Tnil tvoid cc_default).
      Variable b_timer_enable_traps: block.
      Hypothesis h_timer_enable_traps_s : Genv.find_symbol ge timer_enable_traps = Some b_timer_enable_traps.
      Hypothesis h_timer_enable_traps_p : Genv.find_funct_ptr ge b_timer_enable_traps
                                          = Some (External (EF_external timer_enable_traps
                                                           (signature_of_type Tnil tvoid cc_default))
                                                 Tnil tvoid cc_default).
      Variable b_save_shadow_kvm_regs: block.
      Hypothesis h_save_shadow_kvm_regs_s : Genv.find_symbol ge save_shadow_kvm_regs = Some b_save_shadow_kvm_regs.
      Hypothesis h_save_shadow_kvm_regs_p : Genv.find_funct_ptr ge b_save_shadow_kvm_regs
                                            = Some (External (EF_external save_shadow_kvm_regs
                                                             (signature_of_type Tnil tvoid cc_default))
                                                   Tnil tvoid cc_default).
      Variable b_set_vcpu_inactive: block.
      Hypothesis h_set_vcpu_inactive_s : Genv.find_symbol ge set_vcpu_inactive = Some b_set_vcpu_inactive.
      Hypothesis h_set_vcpu_inactive_p : Genv.find_funct_ptr ge b_set_vcpu_inactive
                                            = Some (External (EF_external set_vcpu_inactive
                                                    (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                          (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).

      Lemma save_vm_body_correct:
        forall m d d' env le
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: save_vm_spec  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) save_vm_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec save_vm_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End save_vm_proof.

End CtxtSwitchProofLow.

```
