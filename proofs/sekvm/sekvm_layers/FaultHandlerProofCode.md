# FaultHandlerProofCode

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
Require Import FaultHandler.Spec.
Require Import FaultHandler.Code.
Require Import MemoryOps.Spec.
Require Import MemManager.Spec.
Require Import Ident.
Require Import MemHandler.Layer.
Require Import MmioOps.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section FaultHandlerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section handle_host_stage2_fault_proof.

    Let L : compatlayer (cdata RData) :=
      read_hpfar_el2 ↦ gensem read_hpfar_el2_spec
          ⊕ read_esr_el2 ↦ gensem read_esr_el2_spec
          ⊕ map_page_host ↦ gensem map_page_host_spec
          ⊕ emulate_mmio ↦ gensem emulate_mmio_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_read_hpfar_el2: block.
      Hypothesis h_read_hpfar_el2_s : Genv.find_symbol ge read_hpfar_el2 = Some b_read_hpfar_el2.
      Hypothesis h_read_hpfar_el2_p : Genv.find_funct_ptr ge b_read_hpfar_el2
                                      = Some (External (EF_external read_hpfar_el2
                                                       (signature_of_type Tnil tulong cc_default))
                                             Tnil tulong cc_default).
      Variable b_read_esr_el2: block.
      Hypothesis h_read_esr_el2_s : Genv.find_symbol ge read_esr_el2 = Some b_read_esr_el2.
      Hypothesis h_read_esr_el2_p : Genv.find_funct_ptr ge b_read_esr_el2
                                    = Some (External (EF_external read_esr_el2
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
      Variable b_map_page_host: block.
      Hypothesis h_map_page_host_s : Genv.find_symbol ge map_page_host = Some b_map_page_host.
      Hypothesis h_map_page_host_p : Genv.find_funct_ptr ge b_map_page_host
                                     = Some (External (EF_external map_page_host
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
      Variable b_emulate_mmio: block.
      Hypothesis h_emulate_mmio_s : Genv.find_symbol ge emulate_mmio = Some b_emulate_mmio.
      Hypothesis h_emulate_mmio_p : Genv.find_funct_ptr ge b_emulate_mmio
                                    = Some (External (EF_external emulate_mmio
                                                     (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tuint cc_default))
                                           (Tcons tulong (Tcons tuint Tnil)) tuint cc_default).

      Lemma handle_host_stage2_fault_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: handle_host_stage2_fault_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) handle_host_stage2_fault_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec handle_host_stage2_fault_body; admit
      Qed.
    End BodyProof.

    Theorem handle_host_stage2_fault_code_correct:
      spec_le (handle_host_stage2_fault ↦ handle_host_stage2_fault_spec_low) (〚 handle_host_stage2_fault ↦ f_handle_host_stage2_fault 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (handle_host_stage2_fault_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_handle_host_stage2_fault ) ( :: nil)
               (create_undef_temps (fn_temps f_handle_host_stage2_fault)))) hinv.
    Qed.
  End handle_host_stage2_fault_proof.

  Section core_handle_pvops_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ grant_stage2_sg_gpa ↦ gensem grant_stage2_sg_gpa_spec
          ⊕ revoke_stage2_sg_gpa ↦ gensem revoke_stage2_sg_gpa_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ check ↦ gensem check_spec.

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
      Variable b_grant_stage2_sg_gpa: block.
      Hypothesis h_grant_stage2_sg_gpa_s : Genv.find_symbol ge grant_stage2_sg_gpa = Some b_grant_stage2_sg_gpa.
      Hypothesis h_grant_stage2_sg_gpa_p : Genv.find_funct_ptr ge b_grant_stage2_sg_gpa
                                           = Some (External (EF_external grant_stage2_sg_gpa
                                                            (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                  (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_revoke_stage2_sg_gpa: block.
      Hypothesis h_revoke_stage2_sg_gpa_s : Genv.find_symbol ge revoke_stage2_sg_gpa = Some b_revoke_stage2_sg_gpa.
      Hypothesis h_revoke_stage2_sg_gpa_p : Genv.find_funct_ptr ge b_revoke_stage2_sg_gpa
                                            = Some (External (EF_external revoke_stage2_sg_gpa
                                                             (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma core_handle_pvops_body_correct:
        forall m d d' env le  res
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: core_handle_pvops_spec0  d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) core_handle_pvops_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec core_handle_pvops_body; admit
      Qed.
    End BodyProof.

    Theorem core_handle_pvops_code_correct:
      spec_le (core_handle_pvops ↦ core_handle_pvops_spec_low) (〚 core_handle_pvops ↦ f_core_handle_pvops 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (core_handle_pvops_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_core_handle_pvops ) ( :: nil)
               (create_undef_temps (fn_temps f_core_handle_pvops)))) hinv.
    Qed.
  End core_handle_pvops_proof.

End FaultHandlerProofLow.

```
