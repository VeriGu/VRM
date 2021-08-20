# MmioCoreAuxProofCode

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

Require Import MmioRaw.Layer.
Require Import MmioCoreAux.Spec.
Require Import AbstractMachine.Spec.
Require Import Ident.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioCoreAux.Code.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioCoreAuxProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section handle_smmu_global_access_proof.

    Let L : compatlayer (cdata RData) :=
      host_get_mmio_data ↦ gensem host_get_mmio_data_spec
      ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
      ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_get_mmio_data: block.
      Hypothesis h_host_get_mmio_data_s : Genv.find_symbol ge host_get_mmio_data = Some b_host_get_mmio_data.
      Hypothesis h_host_get_mmio_data_p : Genv.find_funct_ptr ge b_host_get_mmio_data
                                          = Some (External (EF_external host_get_mmio_data
                                                           (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                 (Tcons tuint Tnil) tulong cc_default).
      Variable b_get_smmu_cfg_vmid: block.
      Hypothesis h_get_smmu_cfg_vmid_s : Genv.find_symbol ge get_smmu_cfg_vmid = Some b_get_smmu_cfg_vmid.
      Hypothesis h_get_smmu_cfg_vmid_p : Genv.find_funct_ptr ge b_get_smmu_cfg_vmid
                                         = Some (External (EF_external get_smmu_cfg_vmid
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma handle_smmu_global_access_body_correct:
        forall m d env le hsr offset smmu_index res
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (HPToffset: PTree.get _offset le = Some (Vlong offset))
               (HPTsmmu_index: PTree.get _smmu_index le = Some (Vint smmu_index))
               (Hinv: high_level_invariant d)
               (Hspec: handle_smmu_global_access_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned offset)) (Int.unsigned smmu_index) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) handle_smmu_global_access_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec handle_smmu_global_access_body; eexists; solve_proof_low.
        Grab Existential Variables. assumption. assumption. assumption. assumption.
        assumption. assumption. assumption. assumption. assumption. assumption.
        assumption. assumption. assumption. assumption. assumption. assumption.
        assumption.
      Qed.

    End BodyProof.

  End handle_smmu_global_access_proof.

  Section handle_smmu_cb_access_proof.

    Let L : compatlayer (cdata RData) :=
      check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).


      Lemma handle_smmu_cb_access_body_correct:
        forall m d env le offset res
               (Henv: env = PTree.empty _)
               (HPToffset: PTree.get _offset le = Some (Vlong offset))
               (Hinv: high_level_invariant d)
               (Hspec: handle_smmu_cb_access_spec0 (VZ64 (Int64.unsigned offset)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) handle_smmu_cb_access_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec handle_smmu_cb_access_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End handle_smmu_cb_access_proof.

  Section __handle_smmu_write_proof.

    Let L : compatlayer (cdata RData) :=
      host_get_mmio_data ↦ gensem host_get_mmio_data_spec
          ⊕ writeq_relaxed ↦ gensem writeq_relaxed_spec
          ⊕ writel_relaxed ↦ gensem writel_relaxed_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_get_mmio_data: block.
      Hypothesis h_host_get_mmio_data_s : Genv.find_symbol ge host_get_mmio_data = Some b_host_get_mmio_data.
      Hypothesis h_host_get_mmio_data_p : Genv.find_funct_ptr ge b_host_get_mmio_data
                                          = Some (External (EF_external host_get_mmio_data
                                                           (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                 (Tcons tuint Tnil) tulong cc_default).
      Variable b_writeq_relaxed: block.
      Hypothesis h_writeq_relaxed_s : Genv.find_symbol ge writeq_relaxed = Some b_writeq_relaxed.
      Hypothesis h_writeq_relaxed_p : Genv.find_funct_ptr ge b_writeq_relaxed
                                      = Some (External (EF_external writeq_relaxed
                                                       (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_writel_relaxed: block.
      Hypothesis h_writel_relaxed_s : Genv.find_symbol ge writel_relaxed = Some b_writel_relaxed.
      Hypothesis h_writel_relaxed_p : Genv.find_funct_ptr ge b_writel_relaxed
                                      = Some (External (EF_external writel_relaxed
                                                       (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma __handle_smmu_write_body_correct:
        forall m d d' env le hsr fault_ipa len val write_val
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (HPTfault_ipa: PTree.get _fault_ipa le = Some (Vlong fault_ipa))
               (HPTlen: PTree.get _len le = Some (Vint len))
               (HPTval: PTree.get _val le = Some (Vlong val))
               (HPTwrite_val: PTree.get _write_val le = Some (Vint write_val))
               (Hinv: high_level_invariant d)
               (Hspec: __handle_smmu_write_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) (VZ64 (Int64.unsigned val)) (Int.unsigned write_val) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) __handle_smmu_write_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec __handle_smmu_write_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End __handle_smmu_write_proof.

  Section __handle_smmu_read_proof.

    Let L : compatlayer (cdata RData) :=
      host_dabt_get_rd ↦ gensem host_dabt_get_rd_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ readq_relaxed ↦ gensem readq_relaxed_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ readl_relaxed ↦ gensem readl_relaxed_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_dabt_get_rd: block.
      Hypothesis h_host_dabt_get_rd_s : Genv.find_symbol ge host_dabt_get_rd = Some b_host_dabt_get_rd.
      Hypothesis h_host_dabt_get_rd_p : Genv.find_funct_ptr ge b_host_dabt_get_rd
                                        = Some (External (EF_external host_dabt_get_rd
                                                         (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                               (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_cur_vcpuid: block.
      Hypothesis h_get_cur_vcpuid_s : Genv.find_symbol ge get_cur_vcpuid = Some b_get_cur_vcpuid.
      Hypothesis h_get_cur_vcpuid_p : Genv.find_funct_ptr ge b_get_cur_vcpuid
                                      = Some (External (EF_external get_cur_vcpuid
                                                       (signature_of_type Tnil tuint cc_default))
                                             Tnil tuint cc_default).
      Variable b_readq_relaxed: block.
      Hypothesis h_readq_relaxed_s : Genv.find_symbol ge readq_relaxed = Some b_readq_relaxed.
      Hypothesis h_readq_relaxed_p : Genv.find_funct_ptr ge b_readq_relaxed
                                     = Some (External (EF_external readq_relaxed
                                                      (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                            (Tcons tulong Tnil) tulong cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_readl_relaxed: block.
      Hypothesis h_readl_relaxed_s : Genv.find_symbol ge readl_relaxed = Some b_readl_relaxed.
      Hypothesis h_readl_relaxed_p : Genv.find_funct_ptr ge b_readl_relaxed
                                     = Some (External (EF_external readl_relaxed
                                                      (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                            (Tcons tulong Tnil) tulong cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma __handle_smmu_read_body_correct:
        forall m d d' env le hsr fault_ipa len
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (HPTfault_ipa: PTree.get _fault_ipa le = Some (Vlong fault_ipa))
               (HPTlen: PTree.get _len le = Some (Vint len))
               (Hinv: high_level_invariant d)
               (Hspec: __handle_smmu_read_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) __handle_smmu_read_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec __handle_smmu_read_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End __handle_smmu_read_proof.

End MmioCoreAuxProofLow.

```
