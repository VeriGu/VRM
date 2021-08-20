# MmioOpsRefine

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
Require Import MmioOpsAux.Layer.
Require Import Constants.
Require Import HypsecCommLib.
Require Import MmioOps.Layer.
Require Import MmioOps.Spec.
Require Import AbstractMachine.Spec.
Require Import MmioOpsAux.Spec.
Require Import BootOps.Spec.
Require Import MmioSPTOps.Spec.
Require Import VMPower.Spec.
Require Import NPTWalk.Spec.
Require Import MmioSPTWalk.Spec.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Transparent H_CalLock.
Local Opaque Z.eqb Z.leb Z.geb Z.ltb Z.gtb.

Section MmioOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MmioOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MmioOpsAux_ops) HDATA).

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
           emulate_mmio_spec
           init_spt_spec
           smmu_assign_page_spec
           check64_spec
           assign_smmu_spec
           el2_free_smmu_pgd_spec
           smmu_map_page_spec
           el2_arm_lpae_clear_spec
           get_vm_poweron_spec
           el2_alloc_smmu_pgd_spec0
           smmu_map_page_spec0
           get_smmu_cfg_vmid_spec
           clear_smmu_spec
           handle_host_mmio_spec
           el2_arm_lpae_clear_spec0
           el2_arm_lpae_iova_to_phys_spec0
           release_lock_smmu_spec
           is_smmu_range_spec
           smmu_assign_page_spec0
           get_smmu_num_context_banks_spec
           walk_spt_spec
           el2_free_smmu_pgd_spec0
           acquire_lock_smmu_spec
           check_spec
           map_smmu_spec
           el2_arm_lpae_iova_to_phys_spec
           el2_alloc_smmu_pgd_spec
           emulate_mmio_spec0
           panic_spec
           set_smmu_cfg_vmid_spec.

      Lemma emulate_mmio_spec_exists:
        forall habd habd' labd addr hsr res f
          (Hspec: emulate_mmio_spec addr hsr habd = Some (habd', res))
          (Hrel: relate_RData f habd labd),
        exists labd', emulate_mmio_spec addr hsr labd = Some (labd', res) /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

      Lemma el2_free_smmu_pgd_spec_exists:
        forall habd habd' labd cbndx index f
          (Hspec: el2_free_smmu_pgd_spec cbndx index habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', el2_free_smmu_pgd_spec cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

      Lemma el2_alloc_smmu_pgd_spec_exists:
        forall habd habd' labd cbndx vmid index f
          (Hspec: el2_alloc_smmu_pgd_spec cbndx vmid index habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', el2_alloc_smmu_pgd_spec cbndx vmid index labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

      Lemma smmu_assign_page_spec_exists:
        forall habd habd' labd cbndx index pfn gfn f
          (Hspec: smmu_assign_page_spec cbndx index pfn gfn habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', smmu_assign_page_spec cbndx index pfn gfn labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

      Lemma smmu_map_page_spec_exists:
        forall habd habd' labd cbndx index iova pte f
          (Hspec: smmu_map_page_spec cbndx index iova pte habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', smmu_map_page_spec cbndx index iova pte labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

      Lemma el2_arm_lpae_clear_spec_exists:
        forall habd habd' labd iova cbndx index f
          (Hspec: el2_arm_lpae_clear_spec iova cbndx index habd = Some habd')
          (Hrel: relate_RData f habd labd),
        exists labd', el2_arm_lpae_clear_spec iova cbndx index labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel. eexists; split.
        eassumption. constructor; reflexivity.
      Qed.

    End FreshPrim.

  End WITHMEM.

End MmioOpsProofHigh.

```
