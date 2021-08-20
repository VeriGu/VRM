# CodeProof

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

Definition tschar := Tint I8 Signed noattr.

Definition _i := 1.
Definition _t'2 := 2.
Definition _t'1 := 3.
Definition _csrc := 4.
Definition _cdest := 5.
Definition _len := 6.
Definition _src := 7.
Definition _dest := 8.

Locate tvoid.

Print mcertikos.clib.CDataTypes.

Definition code_body :=
(Ssequence
  (Sset _cdest (Etempvar _dest (tptr tvoid)))
  (Ssequence
    (Sset _csrc (Etempvar _src (tptr tvoid)))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Swhile
        (Ebinop Olt (Etempvar _i tint) (Etempvar _len tulong) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Etempvar _cdest (tptr tschar)))
                  (Sset _cdest
                    (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar))))
                (Sset _t'2 (Etempvar _csrc (tptr tschar))))
              (Sset _csrc
                (Ebinop Oadd (Etempvar _t'2 (tptr tschar))
                  (Econst_int (Int.repr 1) tint) (tptr tschar))))
            (Sassign (Ederef (Etempvar _t'1 (tptr tschar)) tschar)
              (Ederef (Etempvar _t'2 (tptr tschar)) tschar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tuint)
              tuint))))))).

Variables (ge: genv).

Locate exec_stmt.


Lemma code_correct:
  forall m m' d d' env le src dest len
          (Henv: env = PTree.empty _)
          (HPTsrc: PTree.get _src le = Some (Vlong src))
          (HPTdest: PTree.get _dest le = Some (Vlong dest))
          (HPTlen: PTree.get _len le = Some (Vlong len)),
        exists le', (ClightBigstep.exec_stmt ge (fun _ => function_entry2) env le (m, d) code_body E0 le' (m', d') Out_normal).
Proof.
  solve_code_proof Hspec walk_pgd_body; eexists; solve_proof_low.
Qed.


  Variable b_pt_store: block.
  Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
  Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                            = Some (External (EF_external pt_store
                                              (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                    (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
  Variable b_pt_load: block.
  Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
  Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                            = Some (External (EF_external pt_load
                                            (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                  (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
  Variable b_alloc_pud_page: block.
  Hypothesis h_alloc_pud_page_s : Genv.find_symbol ge alloc_pud_page = Some b_alloc_pud_page.
  Hypothesis h_alloc_pud_page_p : Genv.find_funct_ptr ge b_alloc_pud_page
                                  = Some (External (EF_external alloc_pud_page
                                                    (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                          (Tcons tuint Tnil) tulong cc_default).
  Variable b_check64: block.
  Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
  Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                            = Some (External (EF_external check64
                                            (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                  (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pud_body_correct:
        forall m d d' env le vmid pgd addr alloc res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpgd: PTree.get _pgd le = Some (Vlong pgd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pud_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pgd)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pud_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pud_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_pud_code_correct:
      spec_le (walk_pud ↦ walk_pud_spec_low) (〚 walk_pud ↦ f_walk_pud 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_pud_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_pud ) (Vint vmid :: Vlong pgd :: Vlong addr :: Vint alloc :: nil)
               (create_undef_temps (fn_temps f_walk_pud)))) hinv.
    Qed.

  End walk_pud_proof.

  Section walk_pmd_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec
          ⊕ pt_load ↦ gensem pt_load_spec
          ⊕ alloc_pmd_page ↦ gensem alloc_pmd_page_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_alloc_pmd_page: block.
      Hypothesis h_alloc_pmd_page_s : Genv.find_symbol ge alloc_pmd_page = Some b_alloc_pmd_page.
      Hypothesis h_alloc_pmd_page_p : Genv.find_funct_ptr ge b_alloc_pmd_page
                                      = Some (External (EF_external alloc_pmd_page
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pmd_body_correct:
        forall m d d' env le vmid pud addr alloc res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpud: PTree.get _pud le = Some (Vlong pud))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTalloc: PTree.get _alloc le = Some (Vint alloc))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (Int.unsigned alloc) d = Some (d', (VZ64 (Int64.unsigned res)))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pmd_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pmd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_pmd_code_correct:
      spec_le (walk_pmd ↦ walk_pmd_spec_low) (〚 walk_pmd ↦ f_walk_pmd 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_pmd_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_pmd ) (Vint vmid :: Vlong pud :: Vlong addr :: Vint alloc :: nil)
               (create_undef_temps (fn_temps f_walk_pmd)))) hinv.
    Qed.

  End walk_pmd_proof.

  Section walk_pte_proof.

    Let L : compatlayer (cdata RData) :=
      pt_load ↦ gensem pt_load_spec
          ⊕ check64 ↦ gensem check64_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_load: block.
      Hypothesis h_pt_load_s : Genv.find_symbol ge pt_load = Some b_pt_load.
      Hypothesis h_pt_load_p : Genv.find_funct_ptr ge b_pt_load
                               = Some (External (EF_external pt_load
                                                (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons tuint (Tcons tulong Tnil)) tulong cc_default).
      Variable b_check64: block.
      Hypothesis h_check64_s : Genv.find_symbol ge check64 = Some b_check64.
      Hypothesis h_check64_p : Genv.find_funct_ptr ge b_check64
                               = Some (External (EF_external check64
                                                (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                      (Tcons tulong Tnil) tulong cc_default).

      Lemma walk_pte_body_correct:
        forall m d env le vmid pmd addr res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (Hinv: high_level_invariant d)
               (Hspec: walk_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) d = Some (VZ64 (Int64.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) walk_pte_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
      Proof.
        solve_code_proof Hspec walk_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem walk_pte_code_correct:
      spec_le (walk_pte ↦ walk_pte_spec_low) (〚 walk_pte ↦ f_walk_pte 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (walk_pte_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd
               (PTree.empty _) (bind_parameter_temps' (fn_params f_walk_pte ) (Vint vmid :: Vlong pmd :: Vlong addr :: nil)
               (create_undef_temps (fn_temps f_walk_pte)))) hinv.
    Qed.

  End walk_pte_proof.

  Section set_pmd_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma set_pmd_body_correct:
        forall m d d' env le vmid pud addr pmd
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpud: PTree.get _pud le = Some (Vlong pud))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (Hinv: high_level_invariant d)
               (Hspec: set_pmd_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pud)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pmd)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pmd_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pmd_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_pmd_code_correct:
      spec_le (set_pmd ↦ set_pmd_spec_low) (〚 set_pmd ↦ f_set_pmd 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_pmd_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_pmd ) (Vint vmid :: Vlong pud :: Vlong addr :: Vlong pmd :: nil)
               (create_undef_temps (fn_temps f_set_pmd)))) hinv.
    Qed.

  End set_pmd_proof.

  Section set_pte_proof.

    Let L : compatlayer (cdata RData) :=
      pt_store ↦ gensem pt_store_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_pt_store: block.
      Hypothesis h_pt_store_s : Genv.find_symbol ge pt_store = Some b_pt_store.
      Hypothesis h_pt_store_p : Genv.find_funct_ptr ge b_pt_store
                                = Some (External (EF_external pt_store
                                                 (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).

      Lemma set_pte_body_correct:
        forall m d d' env le vmid pmd addr pte
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTpmd: PTree.get _pmd le = Some (Vlong pmd))
               (HPTaddr: PTree.get _addr le = Some (Vlong addr))
               (HPTpte: PTree.get _pte le = Some (Vlong pte))
               (Hinv: high_level_invariant d)
               (Hspec: set_pte_spec0 (Int.unsigned vmid) (VZ64 (Int64.unsigned pmd)) (VZ64 (Int64.unsigned addr)) (VZ64 (Int64.unsigned pte)) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) set_pte_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec set_pte_body; eexists; solve_proof_low.
      Qed.

    End BodyProof.

    Theorem set_pte_code_correct:
      spec_le (set_pte ↦ set_pte_spec_low) (〚 set_pte ↦ f_set_pte 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (set_pte_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_set_pte ) (Vint vmid :: Vlong pmd :: Vlong addr :: Vlong pte :: nil)
               (create_undef_temps (fn_temps f_set_pte)))) hinv.
    Qed.

  End set_pte_proof.

End PTWalkProofLow.

```
