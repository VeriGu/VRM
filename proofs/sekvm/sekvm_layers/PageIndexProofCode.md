# PageIndexProofCode

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
Require Import PageIndex.Code.
Require Import PageIndex.Spec.
Require Import Ident.
Require Import MemRegion.Spec.
Require Import MemRegion.Layer.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PageIndexProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section get_s2_page_index_proof.

    Let L : compatlayer (cdata RData) :=
      get_mem_region_base ↦ gensem get_mem_region_base_spec
          ⊕ get_mem_region_index ↦ gensem get_mem_region_index_spec
          ⊕ mem_region_search ↦ gensem mem_region_search_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_mem_region_base: block.
      Hypothesis h_get_mem_region_base_s : Genv.find_symbol ge get_mem_region_base = Some b_get_mem_region_base.
      Hypothesis h_get_mem_region_base_p : Genv.find_funct_ptr ge b_get_mem_region_base
                                           = Some (External (EF_external get_mem_region_base
                                                            (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                  (Tcons tuint Tnil) tulong cc_default).
      Variable b_get_mem_region_index: block.
      Hypothesis h_get_mem_region_index_s : Genv.find_symbol ge get_mem_region_index = Some b_get_mem_region_index.
      Hypothesis h_get_mem_region_index_p : Genv.find_funct_ptr ge b_get_mem_region_index
                                            = Some (External (EF_external get_mem_region_index
                                                             (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                   (Tcons tuint Tnil) tulong cc_default).
      Variable b_mem_region_search: block.
      Hypothesis h_mem_region_search_s : Genv.find_symbol ge mem_region_search = Some b_mem_region_search.
      Hypothesis h_mem_region_search_p : Genv.find_funct_ptr ge b_mem_region_search
                                         = Some (External (EF_external mem_region_search
                                                          (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                (Tcons tulong Tnil) tuint cc_default).

      Lemma get_s2_page_index_body_correct:
        forall m d env le addr res
               (Henv: env = PTree.empty _)
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: get_s2_page_index_spec0 (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) get_s2_page_index_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec get_s2_page_index_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem get_s2_page_index_code_correct:
      spec_le (get_s2_page_index ↦ get_s2_page_index_spec_low) (〚 get_s2_page_index ↦ f_get_s2_page_index 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (get_s2_page_index_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_get_s2_page_index ) (Vlong addr :: nil)
               (create_undef_temps (fn_temps f_get_s2_page_index)))) hinv.
    Qed.

  End get_s2_page_index_proof.

End PageIndexProofLow.
```
