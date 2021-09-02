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
Require Import FaultHandler.Layer.
Require Import FaultHandler.Spec.
Require Import TrapDispatcher.Spec.
Require Import TrapDispatcher.Code.
Require Import Ident.
Require Import MemHandler.Spec.
Require Import MmioOps.Spec.
Require Import RData.
Require Import BootOps.Spec.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TrapDispatcherProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section vm_exit_dispatcher_proof.

    Let L : compatlayer (cdata RData) :=
      get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ core_handle_sys64 ↦ gensem core_handle_sys64_spec
          ⊕ core_handle_pvops ↦ gensem core_handle_pvops_spec
          ⊕ check ↦ gensem check_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_core_handle_sys64: block.
      Hypothesis h_core_handle_sys64_s : Genv.find_symbol ge core_handle_sys64 = Some b_core_handle_sys64.
      Hypothesis h_core_handle_sys64_p : Genv.find_funct_ptr ge b_core_handle_sys64
                                         = Some (External (EF_external core_handle_sys64
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_core_handle_pvops: block.
      Hypothesis h_core_handle_pvops_s : Genv.find_symbol ge core_handle_pvops = Some b_core_handle_pvops.
      Hypothesis h_core_handle_pvops_p : Genv.find_funct_ptr ge b_core_handle_pvops
                                         = Some (External (EF_external core_handle_pvops
                                                          (signature_of_type Tnil tuint cc_default))
                                                Tnil tuint cc_default).
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

      Lemma vm_exit_dispatcher_body_correct:
        forall m d d' env le vmid vcpuid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: vm_exit_dispatcher_spec (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) vm_exit_dispatcher_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec vm_exit_dispatcher_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem vm_exit_dispatcher_code_correct:
      spec_le (vm_exit_dispatcher ↦ vm_exit_dispatcher_spec_low) (〚 vm_exit_dispatcher ↦ f_vm_exit_dispatcher 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (vm_exit_dispatcher_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b4 Hb4fs Hb4fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_vm_exit_dispatcher ) (Vint vmid :: Vint vcpuid :: nil)
               (create_undef_temps (fn_temps f_vm_exit_dispatcher)))) hinv.
    Qed.

  End vm_exit_dispatcher_proof.

End TrapDispatcherProofLow.

```
