# BootOpsRefine

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
Require Import Constants.
Require Import BootAux.Layer.
Require Import HypsecCommLib.
Require Import BootOps.Spec.
Require Import BootOps.Layer.
Require Import AbstractMachine.Spec.
Require Import MemManager.Spec.
Require Import NPTOps.Spec.
Require Import MmioSPTOps.Spec.
Require Import BootCore.Spec.
Require Import BootAux.Spec.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
Local Transparent H_CalLock.

Section BootOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := BootOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := BootAux_ops) HDATA).

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

      Hint Unfold
           acquire_lock_vm_spec
           alloc_remap_addr_spec
           alloc_smmu_spec
           alloc_smmu_spec0
           assign_pfn_to_smmu_spec
           assign_smmu_spec
           assign_smmu_spec0
           check64_spec
           check_spec
           clear_smmu_spec
           clear_smmu_spec0
           gen_vmid_spec
           get_shared_kvm_spec
           get_shared_vcpu_spec
           get_vcpu_state_spec
           get_vm_load_addr_spec
           get_vm_load_size_spec
           get_vm_mapped_pages_spec
           get_vm_next_load_idx_spec
           get_vm_remap_addr_spec
           get_vm_state_spec
           init_spt_spec
           map_io_spec
           map_io_spec0
           map_s2pt_spec
           map_smmu_spec
           map_smmu_spec0
           map_vm_io_spec
           panic_spec
           register_kvm_spec
           register_kvm_spec0
           register_vcpu_spec
           register_vcpu_spec0
           release_lock_vm_spec
           remap_vm_image_spec
           remap_vm_image_spec0
           search_load_info_spec
           search_load_info_spec0
           set_boot_info_spec
           set_boot_info_spec0
           set_shadow_ctxt_spec
           set_vcpu_active_spec
           set_vcpu_active_spec0
           set_vcpu_inactive_spec
           set_vcpu_inactive_spec0
           set_vcpu_state_spec
           set_vm_kvm_spec
           set_vm_load_addr_spec
           set_vm_load_size_spec
           set_vm_mapped_pages_spec
           set_vm_next_load_idx_spec
           set_vm_remap_addr_spec
           set_vm_state_spec
           set_vm_vcpu_spec
           unmap_and_load_vm_image_spec
           unmap_smmu_page_spec
           update_smmu_page_spec
           verify_and_load_images_spec
           verify_image_spec.

      Lemma search_load_info_spec_exists:
        forall habd habd' labd vmid addr res f
          (Hspec: search_load_info_spec vmid addr habd = Some (habd', (VZ64 res)))
          (Hrel: relate_RData f habd labd),
        exists labd', search_load_info_spec0 vmid addr labd = Some (labd', (VZ64 res)) /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        eexists; split. reflexivity. constructor; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        match goal with
        | [H: search_load_info_loop _ 0 z 0 ?v = _ |- context[search_load_info_loop0 _ 0 vmid z 0 ?ad]] =>
          assert(forall n t r (nrange: 0 <= Z.of_nat n <= 5)
                   (loopH: search_load_info_loop n 0 z 0 v = Some (t, r)),
                    search_load_info_loop0 n 0 vmid z 0 ad = Some (t, r) /\ t = (Z.of_nat n) /\ valid_addr r)
        end.
        induction n0. intros. simpl in *.  inv loopH. split_and; try reflexivity. autounfold; omega.
        intros. rewrite Nat2Z.inj_succ, succ_plus_1 in nrange.
        assert(range: 0 <= Z.of_nat n0 <= 5) by omega.
        simpl in *. repeat autounfold in *. simpl_hyp loopH. destruct p2.
        exploit (IHn0 z2 z3 range). reflexivity. intros (loop0 & t0 & r0). rewrite loop0. srewrite.
        simpl in *. bool_rel_all.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        repeat simpl_hyp loopH; contra; inv loopH; split_and;
          first[reflexivity|rewrite Zpos_P_of_succ_nat; rewrite succ_plus_1; reflexivity|bool_rel_all; omega].
        bool_rel_all; clear_hyp.
        exploit H; try apply C10; rewrite Z2Nat.id; try omega. intros (H1 & H2 & H3). autounfold in *.
        rewrite H1. extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond.
        extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond0.
        inv Hspec. eexists; split. reflexivity. constructor.
        destruct labd, shared; repeat rewrite ZMap.set2; reflexivity.
      Qed.

      Lemma search_load_info_spec_ref:
        compatsim (crel RData RData) (gensem search_load_info_spec) search_load_info_spec_low.
      Proof.
        Opaque search_load_info_spec.
        compatsim_simpl (@match_RData).
        exploit search_load_info_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent search_load_info_spec.
      Qed.

      Lemma set_vcpu_active_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: set_vcpu_active_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_vcpu_active_spec0 vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor.
        destruct habd'; destruct shared; simpl in *; srewrite. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        inv Hspec. eexists; split. reflexivity. constructor.
        destruct labd, shared; repeat rewrite ZMap.set2; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat rewrite ZMap.set2; simpl in *; srewrite; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma set_vcpu_active_spec_ref:
        compatsim (crel RData RData) (gensem set_vcpu_active_spec) set_vcpu_active_spec_low.
      Proof.
        Opaque set_vcpu_active_spec.
        compatsim_simpl (@match_RData).
        exploit set_vcpu_active_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_vcpu_active_spec.
      Qed.

      Lemma set_vcpu_inactive_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: set_vcpu_inactive_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', set_vcpu_inactive_spec0 vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor.
        destruct habd'; destruct shared; simpl in *; srewrite. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        inv Hspec. eexists; split. reflexivity. constructor.
        destruct labd, shared; repeat rewrite ZMap.set2; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat rewrite ZMap.set2; simpl in *; srewrite; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma set_vcpu_inactive_spec_ref:
        compatsim (crel RData RData) (gensem set_vcpu_inactive_spec) set_vcpu_inactive_spec_low.
      Proof.
        Opaque set_vcpu_inactive_spec.
        compatsim_simpl (@match_RData).
        exploit set_vcpu_inactive_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_vcpu_inactive_spec.
      Qed.

      Lemma register_vcpu_spec_exists:
        forall habd habd' labd vmid vcpuid f
          (Hspec: register_vcpu_spec vmid vcpuid habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', register_vcpu_spec0 vmid vcpuid labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor.
        destruct habd'; destruct shared; simpl in *; srewrite. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        inv Hspec. eexists; split. reflexivity. constructor.
        destruct labd, shared; repeat rewrite ZMap.set2; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat rewrite ZMap.set2; simpl in *; srewrite; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma register_vcpu_spec_ref:
        compatsim (crel RData RData) (gensem register_vcpu_spec) register_vcpu_spec_low.
      Proof.
        Opaque register_vcpu_spec.
        compatsim_simpl (@match_RData).
        exploit register_vcpu_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent register_vcpu_spec.
      Qed.

      Lemma register_kvm_spec_exists:
        forall habd habd' labd  res f
          (Hspec: register_kvm_spec  habd = Some (habd', res))
          (Hrel: relate_RData f habd labd),
        exists labd', register_kvm_spec0  labd = Some (labd', res) /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        inv Hspec; simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat rewrite ZMap.set2; simpl in *; srewrite; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; simpl in *. repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat rewrite ZMap.set2; simpl in *; srewrite; reflexivity.
        inv Hspec; eexists; split. reflexivity. constructor; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma register_kvm_spec_ref:
        compatsim (crel RData RData) (gensem register_kvm_spec) register_kvm_spec_low.
      Proof.
        Opaque register_kvm_spec.
        compatsim_simpl (@match_RData).
        exploit register_kvm_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent register_kvm_spec.
      Qed.

      Lemma set_boot_info_spec_exists:
        forall habd habd' labd vmid load_addr size res f
          (Hspec: set_boot_info_spec vmid load_addr size habd = Some (habd', res))
          (Hrel: relate_RData f habd labd),
        exists labd', set_boot_info_spec0 vmid load_addr size labd = Some (labd', res) /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor.
        destruct habd'; destruct shared; simpl in *; srewrite; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        extract_if. apply andb_true_iff; split; bool_rel_all0; somega; reflexivity. rewrite Cond.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite ZMap.set2; simpl).
        reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat (srewrite; try rewrite ZMap.gss; try  rewrite ZMap.set2; simpl).
        reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; repeat (srewrite; try rewrite ZMap.gss; try  rewrite ZMap.set2; simpl).
        reflexivity.
      Qed.

      Lemma set_boot_info_spec_ref:
        compatsim (crel RData RData) (gensem set_boot_info_spec) set_boot_info_spec_low.
      Proof.
        Opaque set_boot_info_spec.
        compatsim_simpl (@match_RData).
        exploit set_boot_info_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent set_boot_info_spec.
      Qed.

      Lemma remap_vm_image_spec_exists:
        forall habd habd' labd vmid pfn load_idx f
          (Hspec: remap_vm_image_spec vmid pfn load_idx habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', remap_vm_image_spec0 vmid pfn load_idx labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; repeat srewrite; simpl in *.
        inv Hspec; eexists; split. reflexivity. constructor.
        destruct habd'; destruct shared; simpl in *; srewrite; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        destruct_if. bool_rel. apply Z.lor_eq_0_iff in Case. destruct Case. inversion H0.
        eexists; split. reflexivity. constructor. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        extract_if. apply andb_true_iff; split; bool_rel_all0; somega. rewrite Cond.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        destruct_if. bool_rel. apply Z.lor_eq_0_iff in Case. destruct Case. inversion H0.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; srewrite; repeat rewrite ZMap.set2; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; srewrite; repeat rewrite ZMap.set2; reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        inv Hspec; repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; srewrite; repeat rewrite ZMap.set2; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma remap_vm_image_spec_ref:
        compatsim (crel RData RData) (gensem remap_vm_image_spec) remap_vm_image_spec_low.
      Proof.
        Opaque remap_vm_image_spec.
        compatsim_simpl (@match_RData).
        exploit remap_vm_image_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent remap_vm_image_spec.
      Qed.

      Lemma verify_and_load_images_spec_exists:
        forall habd habd' labd vmid f
               (Hspec: verify_and_load_images_spec vmid habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', verify_and_load_images_spec vmid labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma verify_and_load_images_spec_ref:
        compatsim (crel RData RData) (gensem verify_and_load_images_spec) verify_and_load_images_spec_low.
      Proof.
        Opaque verify_and_load_images_spec.
        compatsim_simpl (@match_RData).
        exploit verify_and_load_images_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent verify_and_load_images_spec.
      Qed.

      Lemma alloc_smmu_spec_exists:
        forall habd habd' labd vmid cbndx index f
          (Hspec: alloc_smmu_spec vmid cbndx index habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', alloc_smmu_spec0 vmid cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; repeat srewrite; simpl in *.
        destruct_if; srewrite; eexists; (split; [reflexivity|constructor;reflexivity]).
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. eexists; (split; [reflexivity|constructor;reflexivity]).
        inversion C16. inversion C16.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C16.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma alloc_smmu_spec_ref:
        compatsim (crel RData RData) (gensem alloc_smmu_spec) alloc_smmu_spec_low.
      Proof.
        Opaque alloc_smmu_spec.
        compatsim_simpl (@match_RData).
        exploit alloc_smmu_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent alloc_smmu_spec.
      Qed.

      Lemma map_smmu_spec_exists:
        forall habd habd' labd vmid cbndx index iova pte f
          (Hspec: map_smmu_spec vmid cbndx index iova pte habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', map_smmu_spec0 vmid cbndx index iova pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; repeat srewrite; simpl in *.
        destruct_if; srewrite; eexists; (split; [reflexivity|constructor;reflexivity]).
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. eexists; (split; [reflexivity|constructor;reflexivity]).
        inversion C26. inversion C26.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C26.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2.
        reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C26.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq2).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq2).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C26.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; repeat rewrite ZMap.set2; reflexivity.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; repeat rewrite ZMap.set2; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma map_smmu_spec_ref:
        compatsim (crel RData RData) (gensem map_smmu_spec) map_smmu_spec_low.
      Proof.
        Opaque map_smmu_spec.
        compatsim_simpl (@match_RData).
        exploit map_smmu_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_smmu_spec.
      Qed.

      Lemma clear_smmu_spec_exists:
        forall habd habd' labd vmid cbndx index iova f
          (Hspec: clear_smmu_spec vmid cbndx index iova habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', clear_smmu_spec0 vmid cbndx index iova labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; repeat srewrite; simpl in *.
        destruct_if; srewrite; eexists; (split; [reflexivity|constructor;reflexivity]).
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. eexists; (split; [reflexivity|constructor;reflexivity]).
        inversion C24. inversion C24.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C24.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2. reflexivity.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite ZMap.set2; simpl).
        repeat rewrite (zmap_comm _ _ Hneq0); repeat rewrite ZMap.set2. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        destruct_if. destruct_if. inversion C24.
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq2).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq2).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma clear_smmu_spec_ref:
        compatsim (crel RData RData) (gensem clear_smmu_spec) clear_smmu_spec_low.
      Proof.
        Opaque clear_smmu_spec.
        compatsim_simpl (@match_RData).
        exploit clear_smmu_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent clear_smmu_spec.
      Qed.

      Lemma map_io_spec_exists:
        forall habd habd' labd vmid gpa pa f
          (Hspec: map_io_spec vmid gpa pa habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', map_io_spec0 vmid gpa pa labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Local Transparent Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
        intros; inv Hrel; repeat autounfold in *; repeat simpl_hyp Hspec; contra; inv Hspec; repeat srewrite; simpl in *.
        srewrite; eexists; (split; [reflexivity|constructor; destruct habd'; simpl in *; srewrite; reflexivity]).
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq2).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);
                try rewrite (ZMap.gso _ _ Hneq2);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); simpl).
        assert_gso. bool_rel_all0; omega.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq); try rewrite (ZMap.gso _ _ Hneq0); simpl).
        assert_gso. bool_rel_all0; omega. rewrite (ZMap.gso _ _ Hneq1).
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1); simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *.
        repeat (srewrite; try rewrite ZMap.gss; try rewrite (ZMap.gso _ _ Hneq);
                try rewrite (ZMap.gso _ _ Hneq0); try rewrite (ZMap.gso _ _ Hneq1);  simpl).
        repeat (try rewrite (zmap_comm _ _ Hneq0); try rewrite (zmap_comm _ _ Hneq)).
        repeat rewrite ZMap.set2. reflexivity.
        assert(id_cpu: negb (zeq (curid labd) (curid labd)) = false).
        destruct zeq. reflexivity. omega.
        repeat (srewrite; try rewrite ZMap.gss; simpl).
        eexists; split. reflexivity. constructor.
        destruct labd; destruct shared; simpl in *; reflexivity.
        Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.
      Qed.

      Lemma map_io_spec_ref:
        compatsim (crel RData RData) (gensem map_io_spec) map_io_spec_low.
      Proof.
        Opaque map_io_spec.
        compatsim_simpl (@match_RData).
        exploit map_io_spec_exists; eauto 1;
          intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent map_io_spec.
      Qed.

    End FreshPrim.

  End WITHMEM.

End BootOpsProofHigh.

```
