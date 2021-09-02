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
Require Import Ident.
Require Import MmioRaw.Code.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import BootOps.Layer.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MmioRawProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section host_get_mmio_data_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ host_dabt_get_rd ↦ gensem host_dabt_get_rd_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_cur_vcpuid: block.
      Hypothesis h_get_cur_vcpuid_s : Genv.find_symbol ge get_cur_vcpuid = Some b_get_cur_vcpuid.
      Hypothesis h_get_cur_vcpuid_p : Genv.find_funct_ptr ge b_get_cur_vcpuid
                                      = Some (External (EF_external get_cur_vcpuid
                                                       (signature_of_type Tnil tuint cc_default))
                                             Tnil tuint cc_default).
      Variable b_host_dabt_get_rd: block.
      Hypothesis h_host_dabt_get_rd_s : Genv.find_symbol ge host_dabt_get_rd = Some b_host_dabt_get_rd.
      Hypothesis h_host_dabt_get_rd_p : Genv.find_funct_ptr ge b_host_dabt_get_rd
                                        = Some (External (EF_external host_dabt_get_rd
                                                         (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                               (Tcons tuint Tnil) tuint cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).

      Lemma host_get_mmio_data_body_correct:
        forall m d env le hsr res
               (Henv: env = PTree.empty _)
               (HPThsr: PTree.get _hsr le = Some (Vint hsr))
               (Hinv: high_level_invariant d)
               (Hspec: host_get_mmio_data_spec0 (Int.unsigned hsr) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) host_get_mmio_data_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec host_get_mmio_data_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem host_get_mmio_data_code_correct:
      spec_le (host_get_mmio_data ↦ host_get_mmio_data_spec_low) (〚 host_get_mmio_data ↦ f_host_get_mmio_data 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_get_mmio_data_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_get_mmio_data ) (Vint hsr :: nil)
               (create_undef_temps (fn_temps f_host_get_mmio_data)))) hinv.
    Qed.

  End host_get_mmio_data_proof.

  Section smmu_init_pte_proof.

    Let L : compatlayer (cdata RData) :=
      ∅.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Lemma smmu_init_pte_body_correct:
        forall m d env le prot addr res
               (Henv: env = PTree.empty _)
               (HPTprot: PTree.get _prot le = Some (Vlong prot))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: smmu_init_pte_spec0 (VZ64 (Int64.unsigned prot)) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) smmu_init_pte_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec smmu_init_pte_body; eexists; solve_proof_low.
        unfold sem_binary_operation; simpl. unfold sem_or; simpl.
        unfold sem_binarith; simpl. solve_proof_low. rewrite H0.
        solve_proof_low.
      Qed.

    End BodyProof.

  End smmu_init_pte_proof.

  Section smmu_get_cbndx_proof.

    Let L : compatlayer (cdata RData) :=
      ∅.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Lemma smmu_get_cbndx_body_correct:
        forall m d env le offset res
               (Henv: env = PTree.empty _)
               (HPToffset: PTree.get _offset le = Some (Vlong offset))
               (Hinv: high_level_invariant d)
               (Hspec: smmu_get_cbndx_spec0 (VZ64 (Int64.unsigned offset)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) smmu_get_cbndx_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec smmu_get_cbndx_body; eexists; solve_proof_low.
        rewrite H0. solve_proof_low.
      Qed.

    End BodyProof.

  End smmu_get_cbndx_proof.

End MmioRawProofLow.

```
