# PageManagerProofCode

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

Require Import PageManager.Spec.
Require Import AbstractMachine.Spec.
Require Import PageManager.Code.
Require Import PageIndex.Layer.
Require Import PageIndex.Spec.
Require Import Ident.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section PageManagerProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section get_pfn_owner_proof.

    Let L : compatlayer (cdata RData) :=
      get_s2_page_vmid ↦ gensem get_s2_page_vmid_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_s2_page_vmid: block.
      Hypothesis h_get_s2_page_vmid_s : Genv.find_symbol ge get_s2_page_vmid = Some b_get_s2_page_vmid.
      Hypothesis h_get_s2_page_vmid_p : Genv.find_funct_ptr ge b_get_s2_page_vmid
                                        = Some (External (EF_external get_s2_page_vmid
                                                         (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                               (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma get_pfn_owner_body_correct:
        forall m d env le pfn res
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: get_pfn_owner_spec0 (VZ64 (Int64.unsigned pfn)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) get_pfn_owner_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec get_pfn_owner_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem get_pfn_owner_code_correct:
      spec_le (get_pfn_owner ↦ get_pfn_owner_spec_low) (〚 get_pfn_owner ↦ f_get_pfn_owner 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (get_pfn_owner_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_get_pfn_owner ) (Vlong pfn :: nil)
               (create_undef_temps (fn_temps f_get_pfn_owner)))) hinv.
    Qed.

  End get_pfn_owner_proof.

  Section set_pfn_owner_proof.

    Let L : compatlayer (cdata RData) :=
      set_s2_page_vmid ↦ gensem set_s2_page_vmid_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_s2_page_vmid: block.
      Hypothesis h_set_s2_page_vmid_s : Genv.find_symbol ge set_s2_page_vmid = Some b_set_s2_page_vmid.
      Hypothesis h_set_s2_page_vmid_p : Genv.find_funct_ptr ge b_set_s2_page_vmid
                                        = Some (External (EF_external set_s2_page_vmid
                                                         (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                               (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).

      Lemma set_pfn_owner_body_correct:
        forall m d d' env le pfn vmid
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (Hinv: high_level_invariant d)
               (Hspec: set_pfn_owner_spec0 (VZ64 (Int64.unsigned pfn)) (Int.unsigned vmid) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pfn_owner_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pfn_owner_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_pfn_owner_code_correct:
      spec_le (set_pfn_owner ↦ set_pfn_owner_spec_low) (〚 set_pfn_owner ↦ f_set_pfn_owner 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_pfn_owner_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_pfn_owner ) (Vlong pfn :: Vint vmid :: nil)
               (create_undef_temps (fn_temps f_set_pfn_owner)))) hinv.
    Qed.

  End set_pfn_owner_proof.

  Section get_pfn_count_proof.

    Let L : compatlayer (cdata RData) :=
      get_s2_page_count ↦ gensem get_s2_page_count_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec
          ⊕ check ↦ gensem check_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_s2_page_count: block.
      Hypothesis h_get_s2_page_count_s : Genv.find_symbol ge get_s2_page_count = Some b_get_s2_page_count.
      Hypothesis h_get_s2_page_count_p : Genv.find_funct_ptr ge b_get_s2_page_count
                                         = Some (External (EF_external get_s2_page_count
                                                          (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                (Tcons tulong Tnil) tuint cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).
      Variable b_check: block.
      Hypothesis h_check_s : Genv.find_symbol ge check = Some b_check.
      Hypothesis h_check_p : Genv.find_funct_ptr ge b_check
                             = Some (External (EF_external check
                                              (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                    (Tcons tuint Tnil) tuint cc_default).

      Lemma get_pfn_count_body_correct:
        forall m d env le pfn res
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: get_pfn_count_spec0 (VZ64 (Int64.unsigned pfn)) d = Some (Int.unsigned res)),
             exists le', (exec_stmt ge env le ((m, d): mem) get_pfn_count_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec get_pfn_count_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem get_pfn_count_code_correct:
      spec_le (get_pfn_count ↦ get_pfn_count_spec_low) (〚 get_pfn_count ↦ f_get_pfn_count 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (get_pfn_count_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_get_pfn_count ) (Vlong pfn :: nil)
               (create_undef_temps (fn_temps f_get_pfn_count)))) hinv.
    Qed.

  End get_pfn_count_proof.

  Section set_pfn_count_proof.

    Let L : compatlayer (cdata RData) :=
      set_s2_page_count ↦ gensem set_s2_page_count_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_s2_page_count: block.
      Hypothesis h_set_s2_page_count_s : Genv.find_symbol ge set_s2_page_count = Some b_set_s2_page_count.
      Hypothesis h_set_s2_page_count_p : Genv.find_funct_ptr ge b_set_s2_page_count
                                         = Some (External (EF_external set_s2_page_count
                                                          (signature_of_type (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default))
                                                (Tcons tulong (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).

      Lemma set_pfn_count_body_correct:
        forall m d d' env le pfn count
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTcount: PTree.get _count le = Some (Vint count))
               (Hinv: high_level_invariant d)
               (Hspec: set_pfn_count_spec0 (VZ64 (Int64.unsigned pfn)) (Int.unsigned count) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pfn_count_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pfn_count_body; eexists; solve_proof_low.
      Qed.
    End BodyProof.

    Theorem set_pfn_count_code_correct:
      spec_le (set_pfn_count ↦ set_pfn_count_spec_low) (〚 set_pfn_count ↦ f_set_pfn_count 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_pfn_count_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_pfn_count ) (Vlong pfn :: Vint count :: nil)
               (create_undef_temps (fn_temps f_set_pfn_count)))) hinv.
    Qed.

  End set_pfn_count_proof.

  Section get_pfn_map_proof.

    Let L : compatlayer (cdata RData) :=
      get_s2_page_gfn ↦ gensem get_s2_page_gfn_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_s2_page_gfn: block.
      Hypothesis h_get_s2_page_gfn_s : Genv.find_symbol ge get_s2_page_gfn = Some b_get_s2_page_gfn.
      Hypothesis h_get_s2_page_gfn_p : Genv.find_funct_ptr ge b_get_s2_page_gfn
                                       = Some (External (EF_external get_s2_page_gfn
                                                        (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                              (Tcons tulong Tnil) tulong cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma get_pfn_map_body_correct:
        forall m d env le pfn res
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (Hinv: high_level_invariant d)
               (Hspec: get_pfn_map_spec0 (VZ64 (Int64.unsigned pfn)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) get_pfn_map_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec get_pfn_map_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem get_pfn_map_code_correct:
      spec_le (get_pfn_map ↦ get_pfn_map_spec_low) (〚 get_pfn_map ↦ f_get_pfn_map 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (get_pfn_map_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_get_pfn_map ) (Vlong pfn :: nil)
               (create_undef_temps (fn_temps f_get_pfn_map)))) hinv.
    Qed.

  End get_pfn_map_proof.

  Section set_pfn_map_proof.

    Let L : compatlayer (cdata RData) :=
      set_s2_page_gfn ↦ gensem set_s2_page_gfn_spec
          ⊕ get_s2_page_index ↦ gensem get_s2_page_index_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_set_s2_page_gfn: block.
      Hypothesis h_set_s2_page_gfn_s : Genv.find_symbol ge set_s2_page_gfn = Some b_set_s2_page_gfn.
      Hypothesis h_set_s2_page_gfn_p : Genv.find_funct_ptr ge b_set_s2_page_gfn
                                       = Some (External (EF_external set_s2_page_gfn
                                                        (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                              (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
      Variable b_get_s2_page_index: block.
      Hypothesis h_get_s2_page_index_s : Genv.find_symbol ge get_s2_page_index = Some b_get_s2_page_index.
      Hypothesis h_get_s2_page_index_p : Genv.find_funct_ptr ge b_get_s2_page_index
                                         = Some (External (EF_external get_s2_page_index
                                                          (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                (Tcons tulong Tnil) tulong cc_default).

      Lemma set_pfn_map_body_correct:
        forall m d d' env le pfn gfn
               (Henv: env = PTree.empty _)
               (HPTpfn: PTree.get _pfn le = Some (Vlong pfn))
               (HPTgfn: PTree.get _gfn le = Some (Vlong gfn))
               (Hinv: high_level_invariant d)
               (Hspec: set_pfn_map_spec0 (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pfn_map_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pfn_map_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_pfn_map_code_correct:
      spec_le (set_pfn_map ↦ set_pfn_map_spec_low) (〚 set_pfn_map ↦ f_set_pfn_map 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_pfn_map_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_pfn_map ) (Vlong pfn :: Vlong gfn :: nil)
               (create_undef_temps (fn_temps f_set_pfn_map)))) hinv.
    Qed.

  End set_pfn_map_proof.

End PageManagerProofLow.

```
