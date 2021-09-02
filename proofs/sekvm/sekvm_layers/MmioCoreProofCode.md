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

Require Import MmioCoreAux.Spec.
Require Import AbstractMachine.Spec.
Require Import Ident.
Require Import MmioCoreAux.Layer.
Require Import RData.
Require Import MmioCore.Code.
Require Import MmioRaw.Spec.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioCore.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioCoreProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section handle_smmu_write_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_get_cbndx ↦ gensem smmu_get_cbndx_spec
          ⊕ handle_smmu_global_access ↦ gensem handle_smmu_global_access_spec
          ⊕ handle_smmu_cb_access ↦ gensem handle_smmu_cb_access_spec
          ⊕ get_smmu_cfg_hw_ttbr ↦ gensem get_smmu_cfg_hw_ttbr_spec
          ⊕ __handle_smmu_write ↦ gensem __handle_smmu_write_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_get_cbndx: block.
      Hypothesis h_smmu_get_cbndx_s : Genv.find_symbol ge smmu_get_cbndx = Some b_smmu_get_cbndx.
      Hypothesis h_smmu_get_cbndx_p : Genv.find_funct_ptr ge b_smmu_get_cbndx
                                      = Some (External (EF_external smmu_get_cbndx
                                                       (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                             (Tcons tulong Tnil) tuint cc_default).
      Variable b_handle_smmu_global_access: block.
      Hypothesis h_handle_smmu_global_access_s : Genv.find_symbol ge handle_smmu_global_access = Some b_handle_smmu_global_access.
      Hypothesis h_handle_smmu_global_access_p : Genv.find_funct_ptr ge b_handle_smmu_global_access
                                                 = Some (External (EF_external handle_smmu_global_access
                                                                  (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tuint cc_default))
                                                        (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tuint cc_default).
      Variable b_handle_smmu_cb_access: block.
      Hypothesis h_handle_smmu_cb_access_s : Genv.find_symbol ge handle_smmu_cb_access = Some b_handle_smmu_cb_access.
      Hypothesis h_handle_smmu_cb_access_p : Genv.find_funct_ptr ge b_handle_smmu_cb_access
                                             = Some (External (EF_external handle_smmu_cb_access
                                                              (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                    (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_smmu_cfg_hw_ttbr: block.
      Hypothesis h_get_smmu_cfg_hw_ttbr_s : Genv.find_symbol ge get_smmu_cfg_hw_ttbr = Some b_get_smmu_cfg_hw_ttbr.
      Hypothesis h_get_smmu_cfg_hw_ttbr_p : Genv.find_funct_ptr ge b_get_smmu_cfg_hw_ttbr
                                            = Some (External (EF_external get_smmu_cfg_hw_ttbr
                                                             (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tulong cc_default))
                                                   (Tcons tuint (Tcons tuint Tnil)) tulong cc_default).
      Variable b___handle_smmu_write: block.
      Hypothesis h___handle_smmu_write_s : Genv.find_symbol ge __handle_smmu_write = Some b___handle_smmu_write.
      Hypothesis h___handle_smmu_write_p : Genv.find_funct_ptr ge b___handle_smmu_write
                                           = Some (External (EF_external __handle_smmu_write
                                                            (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong (Tcons tuint Tnil))))) tvoid cc_default))
                                                  (Tcons tuint (Tcons tulong (Tcons tuint (Tcons tulong (Tcons tuint Tnil))))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma handle_smmu_write_body_correct:
        forall m d d' env le hsr fault_ipa len index
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (HPTfault_ipa: PTree.get _fault_ipa le = Some (Vlong fault_ipa))
               (HPTlen: PTree.get _len le = Some (Vint len))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: handle_smmu_write_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) handle_smmu_write_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec handle_smmu_write_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End handle_smmu_write_proof.

  Section handle_smmu_read_proof.

    Let L : compatlayer (cdata RData) :=
      __handle_smmu_read ↦ gensem __handle_smmu_read_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b___handle_smmu_read: block.
      Hypothesis h___handle_smmu_read_s : Genv.find_symbol ge __handle_smmu_read = Some b___handle_smmu_read.
      Hypothesis h___handle_smmu_read_p : Genv.find_funct_ptr ge b___handle_smmu_read
                                          = Some (External (EF_external __handle_smmu_read
                                                           (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tvoid cc_default))
                                                 (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tvoid cc_default).

      Lemma handle_smmu_read_body_correct:
        forall m d d' env le hsr fault_ipa len
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (HPTfault_ipa: PTree.get _fault_ipa le = Some (Vlong fault_ipa))
               (HPTlen: PTree.get _len le = Some (Vint len))
               (Hinv: high_level_invariant d)
               (Hspec: handle_smmu_read_spec0 (Int.unsigned hsr) (VZ64 (Int64.unsigned fault_ipa)) (Int.unsigned len) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) handle_smmu_read_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec handle_smmu_read_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

  End handle_smmu_read_proof.

End MmioCoreProofLow.

```
