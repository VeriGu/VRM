# LocksProofCode

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

Require Import RData.
Require Import Constants.
Require Import Ident.
Require Import HypsecCommLib.
Require Import LockOpsH.Spec.
Require Import Locks.Spec.
Require Import LockOpsH.Layer.
Require Import Locks.Code.
Require Import AbstractMachine.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LocksProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section acquire_lock_pt_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_pt_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_pt_spec0 (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_pt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_pt_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem acquire_lock_pt_code_correct:
      spec_le (acquire_lock_pt ↦ acquire_lock_pt_spec_low) (〚 acquire_lock_pt ↦ f_acquire_lock_pt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_pt ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_acquire_lock_pt)))) hinv.
    Qed.

  End acquire_lock_pt_proof.

  Section acquire_lock_spt_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_spt_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_spt_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_spt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_spt_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem acquire_lock_spt_code_correct:
      spec_le (acquire_lock_spt ↦ acquire_lock_spt_spec_low) (〚 acquire_lock_spt ↦ f_acquire_lock_spt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_spt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_spt ) nil
               (create_undef_temps (fn_temps f_acquire_lock_spt)))) hinv.
    Qed.

  End acquire_lock_spt_proof.

  Section acquire_lock_s2page_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_s2page_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_s2page_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_s2page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_s2page_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem acquire_lock_s2page_code_correct:
      spec_le (acquire_lock_s2page ↦ acquire_lock_s2page_spec_low) (〚 acquire_lock_s2page ↦ f_acquire_lock_s2page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_s2page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_s2page ) nil
               (create_undef_temps (fn_temps f_acquire_lock_s2page)))) hinv.
    Qed.

  End acquire_lock_s2page_proof.

  Section acquire_lock_core_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_core_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_core_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_core_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_core_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem acquire_lock_core_code_correct:
      spec_le (acquire_lock_core ↦ acquire_lock_core_spec_low) (〚 acquire_lock_core ↦ f_acquire_lock_core 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_core_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_core ) nil
               (create_undef_temps (fn_temps f_acquire_lock_core)))) hinv.
    Qed.

  End acquire_lock_core_proof.

  Section acquire_lock_vm_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_vm_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_vm_spec0 (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_vm_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_vm_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem acquire_lock_vm_code_correct:
      spec_le (acquire_lock_vm ↦ acquire_lock_vm_spec_low) (〚 acquire_lock_vm ↦ f_acquire_lock_vm 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_vm_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_vm ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_acquire_lock_vm)))) hinv.
    Qed.

  End acquire_lock_vm_proof.

  Section acquire_lock_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      wait_hlock ↦ gensem wait_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_hlock: block.
      Hypothesis h_wait_hlock_s : Genv.find_symbol ge wait_hlock = Some b_wait_hlock.
      Hypothesis h_wait_hlock_p : Genv.find_funct_ptr ge b_wait_hlock
                                  = Some (External (EF_external wait_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma acquire_lock_smmu_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: acquire_lock_smmu_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) acquire_lock_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec acquire_lock_smmu_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem acquire_lock_smmu_code_correct:
      spec_le (acquire_lock_smmu ↦ acquire_lock_smmu_spec_low) (〚 acquire_lock_smmu ↦ f_acquire_lock_smmu 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (acquire_lock_smmu_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_acquire_lock_smmu ) nil
               (create_undef_temps (fn_temps f_acquire_lock_smmu)))) hinv.
    Qed.

  End acquire_lock_smmu_proof.

  Section release_lock_pt_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_pt_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_pt_spec0 (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_pt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_pt_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_pt_code_correct:
      spec_le (release_lock_pt ↦ release_lock_pt_spec_low) (〚 release_lock_pt ↦ f_release_lock_pt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_pt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_pt ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_release_lock_pt)))) hinv.
    Qed.

  End release_lock_pt_proof.

  Section release_lock_spt_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_spt_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_spt_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_spt_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_spt_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_spt_code_correct:
      spec_le (release_lock_spt ↦ release_lock_spt_spec_low) (〚 release_lock_spt ↦ f_release_lock_spt 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_spt_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_spt ) nil
               (create_undef_temps (fn_temps f_release_lock_spt)))) hinv.
    Qed.

  End release_lock_spt_proof.

  Section release_lock_s2page_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_s2page_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_s2page_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_s2page_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_s2page_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_s2page_code_correct:
      spec_le (release_lock_s2page ↦ release_lock_s2page_spec_low) (〚 release_lock_s2page ↦ f_release_lock_s2page 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_s2page_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_s2page ) nil
               (create_undef_temps (fn_temps f_release_lock_s2page)))) hinv.
    Qed.

  End release_lock_s2page_proof.

  Section release_lock_core_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_core_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_core_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_core_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_core_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_core_code_correct:
      spec_le (release_lock_core ↦ release_lock_core_spec_low) (〚 release_lock_core ↦ f_release_lock_core 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_core_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_core ) nil
               (create_undef_temps (fn_temps f_release_lock_core)))) hinv.
    Qed.

  End release_lock_core_proof.

  Section release_lock_vm_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_vm_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_vm_spec0 (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_vm_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_vm_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_vm_code_correct:
      spec_le (release_lock_vm ↦ release_lock_vm_spec_low) (〚 release_lock_vm ↦ f_release_lock_vm 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_vm_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_vm ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_release_lock_vm)))) hinv.
    Qed.

  End release_lock_vm_proof.

  Section release_lock_smmu_proof.

    Let L : compatlayer (cdata RData) :=
      pass_hlock ↦ gensem pass_hlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_hlock: block.
      Hypothesis h_pass_hlock_s : Genv.find_symbol ge pass_hlock = Some b_pass_hlock.
      Hypothesis h_pass_hlock_p : Genv.find_funct_ptr ge b_pass_hlock
                                  = Some (External (EF_external pass_hlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma release_lock_smmu_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: release_lock_smmu_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) release_lock_smmu_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec release_lock_smmu_body; eexists; solve_proof_low.
      Admitted.

    End BodyProof.

    Theorem release_lock_smmu_code_correct:
      spec_le (release_lock_smmu ↦ release_lock_smmu_spec_low) (〚 release_lock_smmu ↦ f_release_lock_smmu 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (release_lock_smmu_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_release_lock_smmu ) nil
               (create_undef_temps (fn_temps f_release_lock_smmu)))) hinv.
    Qed.

  End release_lock_smmu_proof.

End LocksProofLow.

```
