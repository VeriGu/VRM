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
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import MemoryOps.Layer.
Require Import Ident.
Require Import VMPower.Code.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section VMPowerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section set_vm_poweroff_proof.

    Let L : compatlayer (cdata RData) :=
      set_vm_state ↦ gensem set_vm_state_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ acquire_lock_vm ↦ gensem acquire_lock_vm_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_vm_state: block.
      Hypothesis h_set_vm_state_s : Genv.find_symbol ge set_vm_state = Some b_set_vm_state.
      Hypothesis h_set_vm_state_p : Genv.find_funct_ptr ge b_set_vm_state
                                    = Some (External (EF_external set_vm_state
                                                     (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).

      Lemma set_vm_poweroff_body_correct:
        forall m d d' env le vmid
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: set_vm_poweroff_spec0 (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_vm_poweroff_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_vm_poweroff_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_vm_poweroff_code_correct:
      spec_le (set_vm_poweroff ↦ set_vm_poweroff_spec_low) (〚 set_vm_poweroff ↦ f_set_vm_poweroff 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_vm_poweroff_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_vm_poweroff ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_set_vm_poweroff)))) hinv.
    Qed.

  End set_vm_poweroff_proof.

  Section get_vm_poweron_proof.

    Let L : compatlayer (cdata RData) :=
      acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_acquire_lock_vm: block.
      Hypothesis h_acquire_lock_vm_s : Genv.find_symbol ge acquire_lock_vm = Some b_acquire_lock_vm.
      Hypothesis h_acquire_lock_vm_p : Genv.find_funct_ptr ge b_acquire_lock_vm
                                       = Some (External (EF_external acquire_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_get_vm_state: block.
      Hypothesis h_get_vm_state_s : Genv.find_symbol ge get_vm_state = Some b_get_vm_state.
      Hypothesis h_get_vm_state_p : Genv.find_funct_ptr ge b_get_vm_state
                                    = Some (External (EF_external get_vm_state
                                                     (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                           (Tcons tuint Tnil) tuint cc_default).
      Variable b_release_lock_vm: block.
      Hypothesis h_release_lock_vm_s : Genv.find_symbol ge release_lock_vm = Some b_release_lock_vm.
      Hypothesis h_release_lock_vm_p : Genv.find_funct_ptr ge b_release_lock_vm
                                       = Some (External (EF_external release_lock_vm
                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                              (Tcons tuint Tnil) tvoid cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma get_vm_poweron_body_correct:
        forall m d d' env le vmid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: get_vm_poweron_spec0 (Int.unsigned vmid) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) get_vm_poweron_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec get_vm_poweron_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem get_vm_poweron_code_correct:
      spec_le (get_vm_poweron ↦ get_vm_poweron_spec_low) (〚 get_vm_poweron ↦ f_get_vm_poweron 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (get_vm_poweron_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_get_vm_poweron ) (Vint vmid :: nil)
               (create_undef_temps (fn_temps f_get_vm_poweron)))) hinv.
    Qed.

  End get_vm_poweron_proof.

End VMPowerProofLow.

```
