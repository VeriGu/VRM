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

Require Import VMPower.Spec.
Require Import CtxtSwitch.Layer.
Require Import MemoryOps.Spec.
Require Import Ident.
Require Import MemHandler.Spec.
Require Import MemHandler.Code.
Require Import MmioOps.Spec.
Require Import RData.
Require Import MmioRaw.Spec.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemHandlerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section clear_vm_stage2_range_proof.

    Let L : compatlayer (cdata RData) :=
      get_vm_poweron ↦ gensem get_vm_poweron_spec
          ⊕ clear_vm_range ↦ gensem clear_vm_range_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_vm_poweron: block.
      Hypothesis h_get_vm_poweron_s : Genv.find_symbol ge get_vm_poweron = Some b_get_vm_poweron.
      Hypothesis h_get_vm_poweron_p : Genv.find_funct_ptr ge b_get_vm_poweron
                                      = Some (External (EF_external get_vm_poweron
                                                       (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                             (Tcons tuint Tnil) tuint cc_default).
      Variable b_clear_vm_range: block.
      Hypothesis h_clear_vm_range_s : Genv.find_symbol ge clear_vm_range = Some b_clear_vm_range.
      Hypothesis h_clear_vm_range_p : Genv.find_funct_ptr ge b_clear_vm_range
                                      = Some (External (EF_external clear_vm_range
                                                       (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma clear_vm_stage2_range_body_correct:
        forall m d d' env le vmid start size
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTstart: PTree.get _start le = Some (Vlong start))
               (HPTsize: PTree.get _size le = Some (Vlong size))
               (Hinv: high_level_invariant d)
               (Hspec: clear_vm_stage2_range_spec (Int.unsigned vmid) (VZ64 (Int64.unsigned start)) (VZ64 (Int64.unsigned size)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) clear_vm_stage2_range_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec clear_vm_stage2_range_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem clear_vm_stage2_range_code_correct:
      spec_le (clear_vm_stage2_range ↦ clear_vm_stage2_range_spec_low) (〚 clear_vm_stage2_range ↦ f_clear_vm_stage2_range 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (clear_vm_stage2_range_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_clear_vm_stage2_range ) (Vint vmid :: Vlong start :: Vlong size :: nil)
               (create_undef_temps (fn_temps f_clear_vm_stage2_range)))) hinv.
    Qed.
  End clear_vm_stage2_range_proof.

  Section el2_arm_lpae_map_proof.

    Let L : compatlayer (cdata RData) :=
      smmu_init_pte ↦ gensem smmu_init_pte_spec
          ⊕ smmu_assign_page ↦ gensem smmu_assign_page_spec
          ⊕ smmu_map_page ↦ gensem smmu_map_page_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_smmu_init_pte: block.
      Hypothesis h_smmu_init_pte_s : Genv.find_symbol ge smmu_init_pte = Some b_smmu_init_pte.
      Hypothesis h_smmu_init_pte_p : Genv.find_funct_ptr ge b_smmu_init_pte
                                     = Some (External (EF_external smmu_init_pte
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
      Variable b_smmu_assign_page: block.
      Hypothesis h_smmu_assign_page_s : Genv.find_symbol ge smmu_assign_page = Some b_smmu_assign_page.
      Hypothesis h_smmu_assign_page_p : Genv.find_funct_ptr ge b_smmu_assign_page
                                        = Some (External (EF_external smmu_assign_page
                                                         (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                               (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_smmu_map_page: block.
      Hypothesis h_smmu_map_page_s : Genv.find_symbol ge smmu_map_page = Some b_smmu_map_page.
      Hypothesis h_smmu_map_page_p : Genv.find_funct_ptr ge b_smmu_map_page
                                     = Some (External (EF_external smmu_map_page
                                                      (signature_of_type (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).

      Lemma el2_arm_lpae_map_body_correct:
        forall m d d' env le iova paddr prot cbndx index
               (Henv: env = PTree.empty _)
               (HPTiova: PTree.get _iova le = Some (Vlong iova))
               (HPTpaddr: PTree.get _paddr le = Some (Vlong paddr))
               (HPTprot: PTree.get _prot le = Some (Vlong prot))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: el2_arm_lpae_map_spec (VZ64 (Int64.unsigned iova)) (VZ64 (Int64.unsigned paddr)) (VZ64 (Int64.unsigned prot)) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) el2_arm_lpae_map_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec el2_arm_lpae_map_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem el2_arm_lpae_map_code_correct:
      spec_le (el2_arm_lpae_map ↦ el2_arm_lpae_map_spec_low) (〚 el2_arm_lpae_map ↦ f_el2_arm_lpae_map 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (el2_arm_lpae_map_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_el2_arm_lpae_map ) (Vlong iova :: Vlong paddr :: Vlong prot :: Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_el2_arm_lpae_map)))) hinv.
    Qed.

  End el2_arm_lpae_map_proof.

End MemHandlerProofLow.

```
