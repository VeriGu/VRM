# LockOpsHProofCode

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

Require Import LockOpsH.Code.
Require Import CalLock.
Require Import RData.
Require Import Constants.
Require Import Ident.
Require Import LockOpsQ.Spec.
Require Import HypsecCommLib.
Require Import LockOpsH.Spec.
Require Import LockOpsQ.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsHProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section wait_hlock_proof.

    Let L : compatlayer (cdata RData) :=
      wait_qlock ↦ gensem wait_qlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_wait_qlock: block.
      Hypothesis h_wait_qlock_s : Genv.find_symbol ge wait_qlock = Some b_wait_qlock.
      Hypothesis h_wait_qlock_p : Genv.find_funct_ptr ge b_wait_qlock
                                  = Some (External (EF_external wait_qlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma wait_hlock_body_correct:
        forall m d d' env le lk
               (Henv: env = PTree.empty _)
               (HPTlk: PTree.get _lk le = Some (Vint lk))
               (Hinv: high_level_invariant d)
               (Hspec: wait_hlock_spec0 (Int.unsigned lk) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) wait_hlock_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec wait_hlock_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem wait_hlock_code_correct:
      spec_le (wait_hlock ↦ wait_hlock_spec_low) (〚 wait_hlock ↦ f_wait_hlock 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (wait_hlock_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_wait_hlock ) (Vint lk :: nil)
               (create_undef_temps (fn_temps f_wait_hlock)))) hinv.
    Qed.

  End wait_hlock_proof.

  Section pass_hlock_proof.

    Let L : compatlayer (cdata RData) :=
      pass_qlock ↦ gensem pass_qlock_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pass_qlock: block.
      Hypothesis h_pass_qlock_s : Genv.find_symbol ge pass_qlock = Some b_pass_qlock.
      Hypothesis h_pass_qlock_p : Genv.find_funct_ptr ge b_pass_qlock
                                  = Some (External (EF_external pass_qlock
                                                   (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                         (Tcons tuint Tnil) tvoid cc_default).

      Lemma pass_hlock_body_correct:
        forall m d d' env le lk
               (Henv: env = PTree.empty _)
               (HPTlk: PTree.get _lk le = Some (Vint lk))
               (Hinv: high_level_invariant d)
               (Hspec: pass_hlock_spec0 (Int.unsigned lk) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) pass_hlock_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec pass_hlock_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem pass_hlock_code_correct:
      spec_le (pass_hlock ↦ pass_hlock_spec_low) (〚 pass_hlock ↦ f_pass_hlock 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (pass_hlock_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_pass_hlock ) (Vint lk :: nil)
               (create_undef_temps (fn_temps f_pass_hlock)))) hinv.
    Qed.

  End pass_hlock_proof.

End LockOpsHProofLow.
```
