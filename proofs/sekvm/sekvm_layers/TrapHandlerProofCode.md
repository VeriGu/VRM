# TrapHandlerProofCode

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
Require Import NPTWalk.Spec.
Require Import TrapHandlerRaw.Layer.
Require Import TrapHandler.Code.
Require Import Ident.
Require Import TrapHandler.Spec.
Require Import RData.
Require Import MmioSPTWalk.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TrapHandlerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section host_hvc_handler_proof.

    Let L : compatlayer (cdata RData) :=
      host_hvc_handler_raw ↦ gensem host_hvc_handler_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_hvc_handler_raw: block.
      Hypothesis h_host_hvc_handler_raw_s : Genv.find_symbol ge host_hvc_handler_raw = Some b_host_hvc_handler_raw.
      Hypothesis h_host_hvc_handler_raw_p : Genv.find_funct_ptr ge b_host_hvc_handler_raw
                                            = Some (External (EF_external host_hvc_handler_raw
                                                             (signature_of_type Tnil tvoid cc_default))
                                                   Tnil tvoid cc_default).

      Lemma host_hvc_handler_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_hvc_handler_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_hvc_handler_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_hvc_handler_body; admit
      Qed.
    End BodyProof.

    Theorem host_hvc_handler_code_correct:
      spec_le (host_hvc_handler ↦ host_hvc_handler_spec_low) (〚 host_hvc_handler ↦ f_host_hvc_handler 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_hvc_handler_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_hvc_handler ) ( :: nil)
               (create_undef_temps (fn_temps f_host_hvc_handler)))) hinv.
    Qed.
  End host_hvc_handler_proof.

  Section host_npt_handler_proof.

    Let L : compatlayer (cdata RData) :=
      host_npt_handler_raw ↦ gensem host_npt_handler_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_npt_handler_raw: block.
      Hypothesis h_host_npt_handler_raw_s : Genv.find_symbol ge host_npt_handler_raw = Some b_host_npt_handler_raw.
      Hypothesis h_host_npt_handler_raw_p : Genv.find_funct_ptr ge b_host_npt_handler_raw
                                            = Some (External (EF_external host_npt_handler_raw
                                                             (signature_of_type Tnil tvoid cc_default))
                                                   Tnil tvoid cc_default).

      Lemma host_npt_handler_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_npt_handler_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_npt_handler_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_npt_handler_body; admit
      Qed.
    End BodyProof.

    Theorem host_npt_handler_code_correct:
      spec_le (host_npt_handler ↦ host_npt_handler_spec_low) (〚 host_npt_handler ↦ f_host_npt_handler 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_npt_handler_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_npt_handler ) ( :: nil)
               (create_undef_temps (fn_temps f_host_npt_handler)))) hinv.
    Qed.
  End host_npt_handler_proof.

  Section host_vcpu_run_handler_proof.

    Let L : compatlayer (cdata RData) :=
      host_vcpu_run_handler_raw ↦ gensem host_vcpu_run_handler_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_host_vcpu_run_handler_raw: block.
      Hypothesis h_host_vcpu_run_handler_raw_s : Genv.find_symbol ge host_vcpu_run_handler_raw = Some b_host_vcpu_run_handler_raw.
      Hypothesis h_host_vcpu_run_handler_raw_p : Genv.find_funct_ptr ge b_host_vcpu_run_handler_raw
                                                 = Some (External (EF_external host_vcpu_run_handler_raw
                                                                  (signature_of_type Tnil tvoid cc_default))
                                                        Tnil tvoid cc_default).

      Lemma host_vcpu_run_handler_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_vcpu_run_handler_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_vcpu_run_handler_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_vcpu_run_handler_body; admit
      Qed.
    End BodyProof.

    Theorem host_vcpu_run_handler_code_correct:
      spec_le (host_vcpu_run_handler ↦ host_vcpu_run_handler_spec_low) (〚 host_vcpu_run_handler ↦ f_host_vcpu_run_handler 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_vcpu_run_handler_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_vcpu_run_handler ) ( :: nil)
               (create_undef_temps (fn_temps f_host_vcpu_run_handler)))) hinv.
    Qed.
  End host_vcpu_run_handler_proof.

  Section vm_exit_handler_proof.

    Let L : compatlayer (cdata RData) :=
      vm_exit_handler_raw ↦ gensem vm_exit_handler_raw_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_vm_exit_handler_raw: block.
      Hypothesis h_vm_exit_handler_raw_s : Genv.find_symbol ge vm_exit_handler_raw = Some b_vm_exit_handler_raw.
      Hypothesis h_vm_exit_handler_raw_p : Genv.find_funct_ptr ge b_vm_exit_handler_raw
                                           = Some (External (EF_external vm_exit_handler_raw
                                                            (signature_of_type Tnil tvoid cc_default))
                                                  Tnil tvoid cc_default).

      Lemma vm_exit_handler_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: vm_exit_handler_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) vm_exit_handler_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec vm_exit_handler_body; admit
      Qed.
    End BodyProof.

    Theorem vm_exit_handler_code_correct:
      spec_le (vm_exit_handler ↦ vm_exit_handler_spec_low) (〚 vm_exit_handler ↦ f_vm_exit_handler 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (vm_exit_handler_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_vm_exit_handler ) ( :: nil)
               (create_undef_temps (fn_temps f_vm_exit_handler)))) hinv.
    Qed.
  End vm_exit_handler_proof.

  Section mem_load_proof.

    Let L : compatlayer (cdata RData) :=
      mem_load_ref ↦ gensem mem_load_ref_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_mem_load_ref: block.
      Hypothesis h_mem_load_ref_s : Genv.find_symbol ge mem_load_ref = Some b_mem_load_ref.
      Hypothesis h_mem_load_ref_p : Genv.find_funct_ptr ge b_mem_load_ref
                                    = Some (External (EF_external mem_load_ref
                                                     (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                           (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).

      Lemma mem_load_body_correct:
        forall m d d' env le gfn reg
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (Hinv: high_level_invariant d)
               (Hspec: mem_load_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) mem_load_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec mem_load_body; admit
      Qed.
    End BodyProof.

    Theorem mem_load_code_correct:
      spec_le (mem_load ↦ mem_load_spec_low) (〚 mem_load ↦ f_mem_load 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (mem_load_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_mem_load ) (Vlong gfn :: Vint reg :: nil)
               (create_undef_temps (fn_temps f_mem_load)))) hinv.
    Qed.
  End mem_load_proof.

  Section mem_store_proof.

    Let L : compatlayer (cdata RData) :=
      mem_store_ref ↦ gensem mem_store_ref_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_mem_store_ref: block.
      Hypothesis h_mem_store_ref_s : Genv.find_symbol ge mem_store_ref = Some b_mem_store_ref.
      Hypothesis h_mem_store_ref_p : Genv.find_funct_ptr ge b_mem_store_ref
                                     = Some (External (EF_external mem_store_ref
                                                      (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).

      Lemma mem_store_body_correct:
        forall m d d' env le gfn reg
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (Hinv: high_level_invariant d)
               (Hspec: mem_store_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) mem_store_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec mem_store_body; admit
      Qed.
    End BodyProof.

    Theorem mem_store_code_correct:
      spec_le (mem_store ↦ mem_store_spec_low) (〚 mem_store ↦ f_mem_store 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (mem_store_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_mem_store ) (Vlong gfn :: Vint reg :: nil)
               (create_undef_temps (fn_temps f_mem_store)))) hinv.
    Qed.
  End mem_store_proof.

  Section dev_load_proof.

    Let L : compatlayer (cdata RData) :=
      dev_load_ref ↦ gensem dev_load_ref_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_dev_load_ref: block.
      Hypothesis h_dev_load_ref_s : Genv.find_symbol ge dev_load_ref = Some b_dev_load_ref.
      Hypothesis h_dev_load_ref_p : Genv.find_funct_ptr ge b_dev_load_ref
                                    = Some (External (EF_external dev_load_ref
                                                     (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default))
                                           (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma dev_load_body_correct:
        forall m d d' env le gfn reg cbndx index
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: dev_load_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) dev_load_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec dev_load_body; admit
      Qed.
    End BodyProof.

    Theorem dev_load_code_correct:
      spec_le (dev_load ↦ dev_load_spec_low) (〚 dev_load ↦ f_dev_load 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (dev_load_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_dev_load ) (Vlong gfn :: Vint reg :: Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_dev_load)))) hinv.
    Qed.
  End dev_load_proof.

  Section dev_store_proof.

    Let L : compatlayer (cdata RData) :=
      dev_store_ref ↦ gensem dev_store_ref_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_dev_store_ref: block.
      Hypothesis h_dev_store_ref_s : Genv.find_symbol ge dev_store_ref = Some b_dev_store_ref.
      Hypothesis h_dev_store_ref_p : Genv.find_funct_ptr ge b_dev_store_ref
                                     = Some (External (EF_external dev_store_ref
                                                      (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default))
                                            (Tcons tulong (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) tvoid cc_default).

      Lemma dev_store_body_correct:
        forall m d d' env le gfn reg cbndx index
               (Henv: env = PTree.empty _)
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (HPTreg: PTree.get _reg le = Some (Vint reg))
               (HPTcbndx: PTree.get _cbndx le = Some (Vint cbndx))
               (HPTindex: PTree.get _index le = Some (Vint index))
               (Hinv: high_level_invariant d)
               (Hspec: dev_store_spec0 (VZ64 (Int64.unsigned gfn)) (Int.unsigned reg) (Int.unsigned cbndx) (Int.unsigned index) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) dev_store_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec dev_store_body; admit
      Qed.
    End BodyProof.

    Theorem dev_store_code_correct:
      spec_le (dev_store ↦ dev_store_spec_low) (〚 dev_store ↦ f_dev_store 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (dev_store_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_dev_store ) (Vlong gfn :: Vint reg :: Vint cbndx :: Vint index :: nil)
               (create_undef_temps (fn_temps f_dev_store)))) hinv.
    Qed.
  End dev_store_proof.

End TrapHandlerProofLow.

```
