# MemManagerRefine

```coq
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import ZSet.
Require Import ListLemma2.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import RealParams.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import LayerCalculusLemma.
Require Import TacticsForTesting.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import RData.
Require Import MemManager.Layer.
Require Import Constants.
Require Import MemManager.Spec.
Require Import HypsecCommLib.
Require Import PageManager.Layer.
Require Import AbstractMachine.Spec.
Require Import PageManager.Spec.
Require Import NPTOps.Spec.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.
Require Import MmioSPTOps.Spec.
Require Import NPTWalk.ProofHighAux.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb.
Local Transparent H_CalLock. 

Section MemManagerProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MemManager_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := PageManager_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_rel: hadt = ladt
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    Section FreshPrim.

      Local Hint Unfold
            phys_page
            acquire_lock_s2page_spec
            assign_pfn_to_smmu_spec
            assign_pfn_to_smmu_spec0
            assign_pfn_to_vm_spec
            assign_pfn_to_vm_spec0
            clear_pfn_host_spec
            clear_phys_page_spec
            clear_vm_page_spec
            clear_vm_page_spec0
            fetch_from_doracle_spec
            get_pfn_count_spec
            get_pfn_map_spec
            get_pfn_owner_spec
            grant_vm_page_spec
            grant_vm_page_spec0
            map_page_host_spec
            map_page_host_spec0
            map_pfn_vm_spec
            map_pfn_vm_spec0
            map_s2pt_spec
            map_spt_spec
            map_vm_io_spec
            map_vm_io_spec0
            panic_spec
            release_lock_s2page_spec
            revoke_vm_page_spec
            revoke_vm_page_spec0
            set_pfn_count_spec
            set_pfn_map_spec
            set_pfn_owner_spec
            unmap_smmu_page_spec
            unmap_smmu_page_spec0
            unmap_spt_spec
            update_smmu_page_spec
            update_smmu_page_spec0.

      Lemma addr_range_gfn:
        forall n,  n < 281474976710656 -> n / 4096 < 68719476736.
      Proof.
        intros. assert(n <= 281474976710655) by omega.
        assert(n / 4096 <= 281474976710655 / 4096) by( apply Z_div_le; omega).
        assert(n / 4096 <= 68719476735) by apply H1; omega.
      Qed.

      Lemma map_page_host_spec_exists:
        forall habd habd' labd addr f
               (Hspec: map_page_host_spec addr habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', map_page_host_spec0 addr labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          Local Transparent Z.eqb.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          assert(NE52: 5 <> 2) by omega. assert(NE25: 2 <> 5) by omega.
          repeat simpl_hyp Hspec; contra.
          - extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            inv Hspec. repeat srewrite; simpl.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega. rewrite Cond0.
            srewrite. eexists; split. reflexivity. constructor; reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            srewrite. destruct_if.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond0.
            rewrite Z.add_0_r. rewrite (ZMap.gso _ _ NE52). srewrite.
            assert(NZ: Z.lor (z / 4096 * 4096) (Z.lor 18014398509483847 192) =? 0 = false).
            bool_rel. red; intro T. apply Z.lor_eq_0_iff in T.
            destruct T as [T1 T2]. inversion T2. rewrite NZ. rewrite (ZMap.gso _ _ NE52).
            repeat (srewrite; simpl; try rewrite ZMap.gss). destruct b.
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; reflexivity.
            repeat rewrite (ZMap.gso _ _ NE25). repeat rewrite ZMap.gss. simpl; srewrite.
            repeat (rewrite id_cpu; simpl).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; simpl. repeat (rewrite (zmap_comm _ _ NE52); rewrite ZMap.set2).
            reflexivity. simpl in C16; srewrite.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega. rewrite Cond0.
            rewrite Z.add_0_r. rewrite (ZMap.gso _ _ NE52). srewrite.
            assert(NZ: Z.lor (z / 4096 * 4096) 4095 =? 0 = false).
            bool_rel. red; intro T. apply Z.lor_eq_0_iff in T.
            destruct T as [T1 T2]. inversion T2. rewrite NZ. rewrite (ZMap.gso _ _ NE52).
            repeat (srewrite; simpl; try rewrite ZMap.gss). destruct b.
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; reflexivity.
            repeat rewrite (ZMap.gso _ _ NE25). repeat rewrite ZMap.gss. simpl; srewrite.
            repeat (rewrite id_cpu; simpl).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; simpl. repeat (rewrite (zmap_comm _ _ NE52); rewrite ZMap.set2).
            reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            srewrite. destruct_if. simpl in C16; contra. destruct_if. simpl in C16; contra.
            inv Hspec. eexists; split. reflexivity. constructor. reflexivity.
          Local Opaque Z.eqb.
        Qed.

      Lemma map_page_host_spec_ref:
        compatsim (crel RData RData) (gensem map_page_host_spec) map_page_host_spec_low.
      Proof.
        Opaque map_page_host_spec.
        compatsim_simpl (@match_RData).
        exploit map_page_host_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_page_host_spec.
      Qed.

      Lemma map_pfn_vm_spec_exists:
        forall habd habd' labd vmid addr pte level f
               (Hspec: map_pfn_vm_spec vmid addr pte level habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', map_pfn_vm_spec0 vmid addr pte level labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          Local Transparent Z.eqb.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. destruct_if.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
            eexists; split. reflexivity. constructor; reflexivity.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
            eexists; split. reflexivity. constructor; reflexivity.
          - simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
            destruct (level =? 2); srewrite.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
            extract_if. bool_rel; red; intro T. apply Z.bits_inj_iff' with (n:=0) in T.
            autorewrite with bitwise in T. simpl in T. rewrite orb_comm in T. inversion T. omega.
            rewrite Cond0. inv Hspec. eexists; split. reflexivity. constructor; reflexivity.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
            extract_if. bool_rel; red; intro T. apply Z.bits_inj_iff' with (n:=0) in T.
            autorewrite with bitwise in T. simpl in T. rewrite orb_comm in T. inversion T. omega.
            rewrite Cond0. inv Hspec. eexists; split. reflexivity. constructor; reflexivity.
          Local Opaque Z.eqb.
        Qed.

      Lemma map_pfn_vm_spec_ref:
        compatsim (crel RData RData) (gensem map_pfn_vm_spec) map_pfn_vm_spec_low.
      Proof.
        Opaque map_pfn_vm_spec.
        compatsim_simpl (@match_RData).
        exploit map_pfn_vm_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_pfn_vm_spec.
      Qed.

      Lemma grant_vm_page_spec_exists:
        forall habd habd' labd vmid pfn f
               (Hspec: grant_vm_page_spec vmid pfn habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', grant_vm_page_spec0 vmid pfn labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. srewrite. extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond0. srewrite; simpl.
            destruct vmid; simpl; eexists; (split; [reflexivity|constructor; reflexivity]).
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond0.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if. destruct_if. bool_rel_all0; omega.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *. reflexivity.
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *. reflexivity.
        Qed.

      Lemma grant_vm_page_spec_ref:
        compatsim (crel RData RData) (gensem grant_vm_page_spec) grant_vm_page_spec_low.
      Proof.
        Opaque grant_vm_page_spec.
        compatsim_simpl (@match_RData).
        exploit grant_vm_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent grant_vm_page_spec.
      Qed.

      Lemma revoke_vm_page_spec_exists:
        forall habd habd' labd vmid pfn f
               (Hspec: revoke_vm_page_spec vmid pfn habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', revoke_vm_page_spec0 vmid pfn labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. srewrite; simpl.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond0. srewrite; simpl.
            destruct vmid; simpl; eexists; (split; [reflexivity|constructor; reflexivity]).
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond0.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if. bool_rel_all0; omega. srewrite.
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq).
            rewrite Z.add_0_r. repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq0).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct b. repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            assert(T: 2<>5) by omega. repeat (rewrite (zmap_comm _ _ T); rewrite ZMap.set2). reflexivity.
            extract_if. apply andb_true_iff; split; bool_rel_all; omega. rewrite Cond1.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq1). repeat rewrite ZMap.gss.
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq2). rewrite (ZMap.gso _ _ Hneq1).
            rewrite ZMap.gss. repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq3).
            assert_gso. omega. repeat rewrite (ZMap.gso _ _ Hneq4).
            repeat rewrite (zmap_comm _ _ Hneq4); repeat rewrite (zmap_comm _ _ Hneq0).
            repeat rewrite ZMap.set2. reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond0.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if. bool_rel_all0; omega.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *. reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega; reflexivity. rewrite Cond0.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *. reflexivity.
        Qed.

      Lemma revoke_vm_page_spec_ref:
        compatsim (crel RData RData) (gensem revoke_vm_page_spec) revoke_vm_page_spec_low.
      Proof.
        Opaque revoke_vm_page_spec.
        compatsim_simpl (@match_RData).
        exploit revoke_vm_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent revoke_vm_page_spec.
      Qed.

      Lemma map_vm_io_spec_exists:
        forall habd habd' labd vmid gpa pa f
               (Hspec: map_vm_io_spec vmid gpa pa habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', map_vm_io_spec0 vmid gpa pa labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          Local Transparent Z.eqb.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. srewrite. extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            simpl. eexists; split. reflexivity. constructor; reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            srewrite. extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond0.
            assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq); srewrite.
            extract_if. bool_rel; red; intro T. apply Z.lor_eq_0_iff in T.
            destruct T as [T1 T2]. inversion T2. rewrite Cond1.
            assert_gso. bool_rel_all0; omega. repeat rewrite (ZMap.gso _ _ Hneq0).
            repeat (srewrite; simpl; try rewrite ZMap.gss). destruct b.
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; reflexivity.
            assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            rewrite (ZMap.gso _ _ Hneq1). rewrite ZMap.gss.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; simpl in *. repeat (rewrite (zmap_comm _ _ Hneq0); rewrite ZMap.set2).
            reflexivity.
          - simpl in *. repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn; assumption. rewrite Cond.
            srewrite. inv Hspec. eexists; split. reflexivity.
            repeat rewrite ZMap.set2. constructor; reflexivity.
          Local Opaque Z.eqb.
        Qed.

      Lemma map_vm_io_spec_ref:
        compatsim (crel RData RData) (gensem map_vm_io_spec) map_vm_io_spec_low.
      Proof.
        Opaque map_vm_io_spec.
        compatsim_simpl (@match_RData).
        exploit map_vm_io_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_vm_io_spec.
      Qed.

      Lemma update_smmu_page_spec_exists:
        forall habd habd' labd vmid cbndx index iova pte f
               (Hspec: update_smmu_page_spec vmid cbndx index iova pte habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', update_smmu_page_spec0 vmid cbndx index iova pte labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. srewrite; simpl.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            apply addr_range_gfn. pose proof (phys_page_upper_bound z0).
            autounfold in H. omega. rewrite Cond0. simpl.
            simpl_bool_eq; srewrite.
            destruct_if; eexists; (split; [reflexivity|constructor; try reflexivity]).
            destruct habd'; simpl in *; srewrite; reflexivity.
          - simpl in *. extract_if. apply andb_true_iff; split; bool_rel_all; somega. reflexivity. rewrite Cond.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn. pose proof (phys_page_upper_bound z0).
            autounfold in H. omega. rewrite Cond0. simpl.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). srewrite.
            rewrite (ZMap.gso _ _ Hneq). repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if; (inv Hspec; eexists; split; [reflexivity|constructor;reflexivity]).
          - simpl in *.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega. reflexivity. rewrite Cond.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn. pose proof (phys_page_upper_bound z0).
            autounfold in H. omega. rewrite Cond0. simpl.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq). srewrite.
            rewrite (ZMap.gso _ _ Hneq). repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq0).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if. destruct_if. simpl in *.
            destruct_if. bool_rel; omega.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
          - simpl in *.
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega; reflexivity. rewrite Cond.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. pose proof (phys_page_upper_bound z0). autounfold in H.
            apply andb_true_iff; split; bool_rel_all0; somega; apply addr_range_gfn; omega.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *. reflexivity.
        Qed.

      Lemma update_smmu_page_spec_ref:
        compatsim (crel RData RData) (gensem update_smmu_page_spec) update_smmu_page_spec_low.
      Proof.
        Opaque update_smmu_page_spec.
        compatsim_simpl (@match_RData).
        exploit update_smmu_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent update_smmu_page_spec.
      Qed.

      Lemma unmap_smmu_page_spec_exists:
        forall habd habd' labd cbndx index iova f
               (Hspec: unmap_smmu_page_spec cbndx index iova habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', unmap_smmu_page_spec0 cbndx index iova labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; repeat autounfold in *.
          assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
          destruct zeq. reflexivity. omega.
          repeat simpl_hyp Hspec; contra.
          - inv Hspec. srewrite; simpl.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega.
            reflexivity. rewrite Cond.
            Local Transparent Z.land Z.div Z.eqb. simpl.
            eexists; (split; [reflexivity|constructor; try reflexivity]).
          - simpl in *.
            extract_if. apply andb_true_iff; split; bool_rel_all; somega. reflexivity. rewrite Cond.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. repeat (rewrite (ZMap.gso _ _ Hneq); srewrite).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec; eexists; split; [reflexivity|constructor;reflexivity].
          - simpl. extract_if. apply andb_true_iff; split; bool_rel_all; somega. reflexivity. rewrite Cond.
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            assert_gso. omega. repeat (rewrite (ZMap.gso _ _ Hneq); srewrite).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            extract_if. apply andb_true_iff; split; bool_rel_all0; somega.
            apply addr_range_gfn. pose proof (phys_page_upper_bound z1).
            autounfold in H. omega. rewrite Cond0. simpl.
            assert_gso. omega. rewrite (ZMap.gso _ _ Hneq0).
            repeat (srewrite; simpl; try rewrite ZMap.gss).
            destruct_if. destruct_if. simpl in *.
            destruct_if. bool_rel; omega.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
            rewrite (ZMap.gso _ _ Hneq0). repeat (srewrite; simpl; try rewrite ZMap.gss).
            inv Hspec. eexists; split. reflexivity. constructor.
            destruct labd, shared; repeat rewrite ZMap.set2; simpl in *.
            repeat rewrite (zmap_comm _ _ Hneq); repeat rewrite ZMap.set2. reflexivity.
        Qed.

      Lemma unmap_smmu_page_spec_ref:
        compatsim (crel RData RData) (gensem unmap_smmu_page_spec) unmap_smmu_page_spec_low.
      Proof.
        Opaque unmap_smmu_page_spec.
        compatsim_simpl (@match_RData).
        exploit unmap_smmu_page_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent unmap_smmu_page_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MemManagerProofHigh.

```
