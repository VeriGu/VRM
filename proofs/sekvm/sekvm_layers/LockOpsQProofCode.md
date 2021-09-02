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

Require Import RData.
Require Import CalLock.
Require Import Constants.
Require Import Ident.
Require Import LockOpsQ.Spec.
Require Import HypsecCommLib.
Require Import LockOpsQ.Code.
Require Import LockOps.Spec.
Require Import LockOps.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsQProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section wait_qlock_proof.

    Let L : compatlayer (cdata RData) :=
      wait_lock ↦ gensem wait_lock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_lock: block.
      Hypothesis h_wait_lock_s : Genv.find_symbol ge wait_lock = Some b_wait_lock.
      Hypothesis h_wait_lock_p : Genv.find_funct_ptr ge b_wait_lock
                                 = Some (External (EF_external wait_lock
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).

      Lemma wait_qlock_body_correct:
        forall m d d' env le lk
               (Henv: env = PTree.empty _)
               (HPTlk: PTree.get _lk le = Some (Vint lk))
               (Hinv: high_level_invariant d)
               (Hspec: wait_qlock_spec0 (Int.unsigned lk) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) wait_qlock_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec wait_qlock_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem wait_qlock_code_correct:
      spec_le (wait_qlock ↦ wait_qlock_spec_low) (〚 wait_qlock ↦ f_wait_qlock 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (wait_qlock_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_wait_qlock ) (Vint lk :: nil)
               (create_undef_temps (fn_temps f_wait_qlock)))) hinv.
    Qed.

  End wait_qlock_proof.

  Section pass_qlock_proof.

    Let L : compatlayer (cdata RData) :=
      pass_lock ↦ gensem pass_lock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_lock: block.
      Hypothesis h_pass_lock_s : Genv.find_symbol ge pass_lock = Some b_pass_lock.
      Hypothesis h_pass_lock_p : Genv.find_funct_ptr ge b_pass_lock
                                 = Some (External (EF_external pass_lock
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).

      Lemma pass_qlock_body_correct:
        forall m d d' env le lk
               (Henv: env = PTree.empty _)
               (HPTlk: PTree.get _lk le = Some (Vint lk))
               (Hinv: high_level_invariant d)
               (Hspec: pass_qlock_spec0 (Int.unsigned lk) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) pass_qlock_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec pass_qlock_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem pass_qlock_code_correct:
      spec_le (pass_qlock ↦ pass_qlock_spec_low) (〚 pass_qlock ↦ f_pass_qlock 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (pass_qlock_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_pass_qlock ) (Vint lk :: nil)
               (create_undef_temps (fn_temps f_pass_qlock)))) hinv.
    Qed.

  End pass_qlock_proof.

End LockOpsQProofLow.

```
