# TrapHandlerRawProofCode

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

Require Import TrapHandlerRaw.Spec.
Require Import AbstractMachine.Spec.
Require Import FaultHandler.Spec.
Require Import TrapDispatcher.Spec.
Require Import CtxtSwitch.Spec.
Require Import Ident.
Require Import TrapHandlerRaw.Code.
Require Import RData.
Require Import TrapDispatcher.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TrapHandlerRawProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section host_hvc_handler_raw_proof.

    Let L : compatlayer (cdata RData) :=
      host_to_core ↦ gensem host_to_core_spec
          ⊕ host_hvc_dispatcher ↦ gensem host_hvc_dispatcher_spec
          ⊕ core_to_host ↦ gensem core_to_host_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_to_core: block.
      Hypothesis h_host_to_core_s : Genv.find_symbol ge host_to_core = Some b_host_to_core.
      Hypothesis h_host_to_core_p : Genv.find_funct_ptr ge b_host_to_core
                                    = Some (External (EF_external host_to_core
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_host_hvc_dispatcher: block.
      Hypothesis h_host_hvc_dispatcher_s : Genv.find_symbol ge host_hvc_dispatcher = Some b_host_hvc_dispatcher.
      Hypothesis h_host_hvc_dispatcher_p : Genv.find_funct_ptr ge b_host_hvc_dispatcher
                                           = Some (External (EF_external host_hvc_dispatcher
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_core_to_host: block.
      Hypothesis h_core_to_host_s : Genv.find_symbol ge core_to_host = Some b_core_to_host.
      Hypothesis h_core_to_host_p : Genv.find_funct_ptr ge b_core_to_host
                                    = Some (External (EF_external core_to_host
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).

      Lemma host_hvc_handler_raw_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_hvc_handler_raw_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_hvc_handler_raw_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_hvc_handler_raw_body; admit
      Qed.
    End BodyProof.

    Theorem host_hvc_handler_raw_code_correct:
      spec_le (host_hvc_handler_raw ↦ host_hvc_handler_raw_spec_low) (〚 host_hvc_handler_raw ↦ f_host_hvc_handler_raw 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_hvc_handler_raw_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_hvc_handler_raw ) ( :: nil)
               (create_undef_temps (fn_temps f_host_hvc_handler_raw)))) hinv.
    Qed.
  End host_hvc_handler_raw_proof.

  Section host_npt_handler_raw_proof.

    Let L : compatlayer (cdata RData) :=
      host_to_core ↦ gensem host_to_core_spec
          ⊕ handle_host_stage2_fault ↦ gensem handle_host_stage2_fault_spec
          ⊕ core_to_host ↦ gensem core_to_host_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_to_core: block.
      Hypothesis h_host_to_core_s : Genv.find_symbol ge host_to_core = Some b_host_to_core.
      Hypothesis h_host_to_core_p : Genv.find_funct_ptr ge b_host_to_core
                                    = Some (External (EF_external host_to_core
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_handle_host_stage2_fault: block.
      Hypothesis h_handle_host_stage2_fault_s : Genv.find_symbol ge handle_host_stage2_fault = Some b_handle_host_stage2_fault.
      Hypothesis h_handle_host_stage2_fault_p : Genv.find_funct_ptr ge b_handle_host_stage2_fault
                                                = Some (External (EF_external handle_host_stage2_fault
                                                                 (signature_of_type Tnil tvoid cc_default))
                                                       Tnil tvoid cc_default).
      Variable b_core_to_host: block.
      Hypothesis h_core_to_host_s : Genv.find_symbol ge core_to_host = Some b_core_to_host.
      Hypothesis h_core_to_host_p : Genv.find_funct_ptr ge b_core_to_host
                                    = Some (External (EF_external core_to_host
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).

      Lemma host_npt_handler_raw_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_npt_handler_raw_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_npt_handler_raw_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_npt_handler_raw_body; admit
      Qed.
    End BodyProof.

    Theorem host_npt_handler_raw_code_correct:
      spec_le (host_npt_handler_raw ↦ host_npt_handler_raw_spec_low) (〚 host_npt_handler_raw ↦ f_host_npt_handler_raw 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_npt_handler_raw_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_npt_handler_raw ) ( :: nil)
               (create_undef_temps (fn_temps f_host_npt_handler_raw)))) hinv.
    Qed.
  End host_npt_handler_raw_proof.

  Section host_vcpu_run_handler_raw_proof.

    Let L : compatlayer (cdata RData) :=
      host_to_core ↦ gensem host_to_core_spec
          ⊕ save_host ↦ gensem save_host_spec
          ⊕ restore_vm ↦ gensem restore_vm_spec
          ⊕ core_to_vm ↦ gensem core_to_vm_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_to_core: block.
      Hypothesis h_host_to_core_s : Genv.find_symbol ge host_to_core = Some b_host_to_core.
      Hypothesis h_host_to_core_p : Genv.find_funct_ptr ge b_host_to_core
                                    = Some (External (EF_external host_to_core
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_save_host: block.
      Hypothesis h_save_host_s : Genv.find_symbol ge save_host = Some b_save_host.
      Hypothesis h_save_host_p : Genv.find_funct_ptr ge b_save_host
                                 = Some (External (EF_external save_host
                                                  (signature_of_type Tnil tvoid cc_default))
                                        Tnil tvoid cc_default).
      Variable b_restore_vm: block.
      Hypothesis h_restore_vm_s : Genv.find_symbol ge restore_vm = Some b_restore_vm.
      Hypothesis h_restore_vm_p : Genv.find_funct_ptr ge b_restore_vm
                                  = Some (External (EF_external restore_vm
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).
      Variable b_core_to_vm: block.
      Hypothesis h_core_to_vm_s : Genv.find_symbol ge core_to_vm = Some b_core_to_vm.
      Hypothesis h_core_to_vm_p : Genv.find_funct_ptr ge b_core_to_vm
                                  = Some (External (EF_external core_to_vm
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).

      Lemma host_vcpu_run_handler_raw_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_vcpu_run_handler_raw_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_vcpu_run_handler_raw_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_vcpu_run_handler_raw_body; admit
      Qed.
    End BodyProof.

    Theorem host_vcpu_run_handler_raw_code_correct:
      spec_le (host_vcpu_run_handler_raw ↦ host_vcpu_run_handler_raw_spec_low) (〚 host_vcpu_run_handler_raw ↦ f_host_vcpu_run_handler_raw 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_vcpu_run_handler_raw_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_vcpu_run_handler_raw ) ( :: nil)
               (create_undef_temps (fn_temps f_host_vcpu_run_handler_raw)))) hinv.
    Qed.
  End host_vcpu_run_handler_raw_proof.

  Section vm_exit_handler_raw_proof.

    Let L : compatlayer (cdata RData) :=
      vm_to_core ↦ gensem vm_to_core_spec
          ⊕ get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ exit_populate_fault ↦ gensem exit_populate_fault_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ vm_exit_dispatcher ↦ gensem vm_exit_dispatcher_spec
          ⊕ core_to_vm ↦ gensem core_to_vm_spec
          ⊕ save_vm ↦ gensem save_vm_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ restore_host ↦ gensem restore_host_spec
          ⊕ core_to_host ↦ gensem core_to_host_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_vm_to_core: block.
      Hypothesis h_vm_to_core_s : Genv.find_symbol ge vm_to_core = Some b_vm_to_core.
      Hypothesis h_vm_to_core_p : Genv.find_funct_ptr ge b_vm_to_core
                                  = Some (External (EF_external vm_to_core
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).
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
      Variable b_exit_populate_fault: block.
      Hypothesis h_exit_populate_fault_s : Genv.find_symbol ge exit_populate_fault = Some b_exit_populate_fault.
      Hypothesis h_exit_populate_fault_p : Genv.find_funct_ptr ge b_exit_populate_fault
                                           = Some (External (EF_external exit_populate_fault
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_vm_exit_dispatcher: block.
      Hypothesis h_vm_exit_dispatcher_s : Genv.find_symbol ge vm_exit_dispatcher = Some b_vm_exit_dispatcher.
      Hypothesis h_vm_exit_dispatcher_p : Genv.find_funct_ptr ge b_vm_exit_dispatcher
                                          = Some (External (EF_external vm_exit_dispatcher
                                                           (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                 (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_core_to_vm: block.
      Hypothesis h_core_to_vm_s : Genv.find_symbol ge core_to_vm = Some b_core_to_vm.
      Hypothesis h_core_to_vm_p : Genv.find_funct_ptr ge b_core_to_vm
                                  = Some (External (EF_external core_to_vm
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).
      Variable b_save_vm: block.
      Hypothesis h_save_vm_s : Genv.find_symbol ge save_vm = Some b_save_vm.
      Hypothesis h_save_vm_p : Genv.find_funct_ptr ge b_save_vm
                               = Some (External (EF_external save_vm
                                                (signature_of_type Tnil tvoid cc_default))
                                      Tnil tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_restore_host: block.
      Hypothesis h_restore_host_s : Genv.find_symbol ge restore_host = Some b_restore_host.
      Hypothesis h_restore_host_p : Genv.find_funct_ptr ge b_restore_host
                                    = Some (External (EF_external restore_host
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
      Variable b_core_to_host: block.
      Hypothesis h_core_to_host_s : Genv.find_symbol ge core_to_host = Some b_core_to_host.
      Hypothesis h_core_to_host_p : Genv.find_funct_ptr ge b_core_to_host
                                    = Some (External (EF_external core_to_host
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).

      Lemma vm_exit_handler_raw_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: vm_exit_handler_raw_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) vm_exit_handler_raw_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec vm_exit_handler_raw_body; admit
      Qed.
    End BodyProof.

    Theorem vm_exit_handler_raw_code_correct:
      spec_le (vm_exit_handler_raw ↦ vm_exit_handler_raw_spec_low) (〚 vm_exit_handler_raw ↦ f_vm_exit_handler_raw 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (vm_exit_handler_raw_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp b8 Hb8fs Hb8fp b9 Hb9fs Hb9fp b10 Hb10fs Hb10fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_vm_exit_handler_raw ) ( :: nil)
               (create_undef_temps (fn_temps f_vm_exit_handler_raw)))) hinv.
    Qed.
  End vm_exit_handler_raw_proof.

End TrapHandlerRawProofLow.

```
