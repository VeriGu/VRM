# PTWalk

```coq
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import XOmega.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractMachine.Spec.
Require Import RData.
Require Import HypsecCommLib.
Require Import Constants.
Require Import Ident.
Require Import PTWalk.Spec.

Local Open Scope Z_scope.

Section PTWalkLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance PTWalk_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance PTWalk_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance set_pmd_inv: PreservesInvariants set_pmd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance walk_pte_inv: PreservesInvariants walk_pte_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance walk_pmd_inv: PreservesInvariants walk_pmd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance walk_pgd_inv: PreservesInvariants walk_pgd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_pte_inv: PreservesInvariants set_pte_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance walk_pud_inv: PreservesInvariants walk_pud_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_inc_exe_inv: PreservesInvariants set_vm_inc_exe_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_sys_reg_desc_val_inv: PreservesInvariants get_sys_reg_desc_val_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_dabt_is_write_inv: PreservesInvariants host_dabt_is_write_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_kvm_inv: PreservesInvariants set_vm_kvm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_get_fault_ipa_inv: PreservesInvariants host_get_fault_ipa_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_next_vmid_inv: PreservesInvariants get_next_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance exit_populate_fault_inv: PreservesInvariants exit_populate_fault_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_cfg_vmid_inv: PreservesInvariants get_smmu_cfg_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_num_inv: PreservesInvariants get_smmu_num_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_smmu_pmd_next_inv: PreservesInvariants set_smmu_pmd_next_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance decrypt_mem_buf_inv: PreservesInvariants decrypt_mem_buf_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_spt_inv: PreservesInvariants acquire_lock_spt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_mem_region_cnt_inv: PreservesInvariants get_mem_region_cnt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_load_size_inv: PreservesInvariants get_vm_load_size_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance fetch_from_doracle_inv: PreservesInvariants fetch_from_doracle_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance reset_fp_regs_inv: PreservesInvariants reset_fp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_load_raw_inv: PreservesInvariants dev_load_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance timer_set_cntvoff_inv: PreservesInvariants timer_set_cntvoff_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance encrypt_gp_regs_inv: PreservesInvariants encrypt_gp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_vm_inv: PreservesInvariants acquire_lock_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_pstate_inv: PreservesInvariants get_int_pstate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_inc_exe_inv: PreservesInvariants get_vm_inc_exe_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_s2page_inv: PreservesInvariants release_lock_s2page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_vcpu_inv: PreservesInvariants set_vm_vcpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_dabt_get_rd_inv: PreservesInvariants host_dabt_get_rd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_s2page_inv: PreservesInvariants acquire_lock_s2page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance writel_relaxed_inv: PreservesInvariants writel_relaxed_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_shadow_ctxt_inv: PreservesInvariants set_shadow_ctxt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_skip_instr_inv: PreservesInvariants host_skip_instr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_to_core_inv: PreservesInvariants vm_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_num_context_banks_inv: PreservesInvariants get_smmu_num_context_banks_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_pt_vttbr_inv: PreservesInvariants get_pt_vttbr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_next_remap_ptr_inv: PreservesInvariants set_next_remap_ptr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_fault_addr_inv: PreservesInvariants get_vm_fault_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_dabt_get_as_inv: PreservesInvariants host_dabt_get_as_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_esr_inv: PreservesInvariants get_shadow_esr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vcpu_state_inv: PreservesInvariants set_vcpu_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_size_inv: PreservesInvariants get_smmu_size_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_per_cpu_inv: PreservesInvariants set_per_cpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_smmu_inv: PreservesInvariants acquire_lock_smmu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vcpuid_inv: PreservesInvariants get_cur_vcpuid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_core_inv: PreservesInvariants acquire_lock_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance writeq_relaxed_inv: PreservesInvariants writeq_relaxed_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_actlr_el1_inv: PreservesInvariants read_actlr_el1_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_mem_region_base_inv: PreservesInvariants get_mem_region_base_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_smmu_inv: PreservesInvariants release_lock_smmu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_s2_page_gfn_inv: PreservesInvariants set_s2_page_gfn_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance decrypt_sys_regs_inv: PreservesInvariants decrypt_sys_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_el2_restore_state_inv: PreservesInvariants vm_el2_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_smmu_cfg_vmid_inv: PreservesInvariants set_smmu_cfg_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_exception_vector_inv: PreservesInvariants get_exception_vector_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_ctxt_inv: PreservesInvariants get_shadow_ctxt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_smmu_pgd_next_inv: PreservesInvariants set_smmu_pgd_next_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_pc_inv: PreservesInvariants get_int_pc_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vmid_inv: PreservesInvariants get_cur_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance deactivate_traps_inv: PreservesInvariants deactivate_traps_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_s2_page_count_inv: PreservesInvariants get_s2_page_count_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_next_vmid_inv: PreservesInvariants set_next_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance encrypt_sys_regs_inv: PreservesInvariants encrypt_sys_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smmu_pt_clear_inv: PreservesInvariants smmu_pt_clear_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_load_addr_inv: PreservesInvariants set_vm_load_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shared_kvm_inv: PreservesInvariants get_shared_kvm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance check64_inv: PreservesInvariants check64_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance readq_relaxed_inv: PreservesInvariants readq_relaxed_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_s2_page_gfn_inv: PreservesInvariants get_s2_page_gfn_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_base_inv: PreservesInvariants get_smmu_base_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_to_vm_inv: PreservesInvariants core_to_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_remap_addr_inv: PreservesInvariants set_vm_remap_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance readl_relaxed_inv: PreservesInvariants readl_relaxed_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_spt_inv: PreservesInvariants release_lock_spt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance restore_sysregs_inv: PreservesInvariants restore_sysregs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance timer_enable_traps_inv: PreservesInvariants timer_enable_traps_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance fpsimd_restore_state_inv: PreservesInvariants fpsimd_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_s2_page_count_inv: PreservesInvariants set_s2_page_count_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smmu_pt_store_inv: PreservesInvariants smmu_pt_store_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_store_raw_inv: PreservesInvariants mem_store_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_state_inv: PreservesInvariants set_vm_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance decrypt_gp_regs_inv: PreservesInvariants decrypt_gp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_esr_el2_inv: PreservesInvariants read_esr_el2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_hpfar_el2_inv: PreservesInvariants read_hpfar_el2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance acquire_lock_pt_inv: PreservesInvariants acquire_lock_pt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_el2_restore_state_inv: PreservesInvariants host_el2_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_store_raw_inv: PreservesInvariants dev_store_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_next_load_idx_inv: PreservesInvariants get_vm_next_load_idx_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_mapped_pages_inv: PreservesInvariants set_vm_mapped_pages_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_s2_page_vmid_inv: PreservesInvariants get_s2_page_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_cfg_hw_ttbr_inv: PreservesInvariants get_smmu_cfg_hw_ttbr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_core_inv: PreservesInvariants release_lock_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_sysregs_inv: PreservesInvariants save_sysregs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_pt_inv: PreservesInvariants release_lock_pt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_next_remap_ptr_inv: PreservesInvariants get_next_remap_ptr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance check_inv: PreservesInvariants check_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance clear_shadow_gp_regs_inv: PreservesInvariants clear_shadow_gp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance verify_image_inv: PreservesInvariants verify_image_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_load_size_inv: PreservesInvariants set_vm_load_size_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_s2_page_vmid_inv: PreservesInvariants set_s2_page_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_remap_addr_inv: PreservesInvariants get_vm_remap_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance release_lock_vm_inv: PreservesInvariants release_lock_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_new_pte_inv: PreservesInvariants get_int_new_pte_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_mem_region_index_inv: PreservesInvariants get_mem_region_index_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance activate_traps_inv: PreservesInvariants activate_traps_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_mem_region_size_inv: PreservesInvariants get_mem_region_size_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance fpsimd_save_state_inv: PreservesInvariants fpsimd_save_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_pmd_next_inv: PreservesInvariants get_smmu_pmd_next_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_esr_inv: PreservesInvariants get_int_esr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance panic_inv: PreservesInvariants panic_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_to_host_inv: PreservesInvariants core_to_host_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_shadow_dirty_bit_inv: PreservesInvariants set_shadow_dirty_bit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance encrypt_mem_buf_inv: PreservesInvariants encrypt_mem_buf_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_to_core_inv: PreservesInvariants host_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smmu_pt_load_inv: PreservesInvariants smmu_pt_load_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_vm_next_load_idx_inv: PreservesInvariants set_vm_next_load_idx_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_dirty_bit_inv: PreservesInvariants get_shadow_dirty_bit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_load_raw_inv: PreservesInvariants mem_load_raw_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_gpr_inv: PreservesInvariants get_int_gpr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_int_gpr_inv: PreservesInvariants set_int_gpr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_state_inv: PreservesInvariants get_vm_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance clear_phys_page_inv: PreservesInvariants clear_phys_page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_smmu_pgd_next_inv: PreservesInvariants get_smmu_pgd_next_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_handle_sys64_inv: PreservesInvariants core_handle_sys64_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_mapped_pages_inv: PreservesInvariants get_vm_mapped_pages_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shared_vcpu_inv: PreservesInvariants get_shared_vcpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vcpu_state_inv: PreservesInvariants get_vcpu_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_load_addr_inv: PreservesInvariants get_vm_load_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition PTWalk_fresh : compatlayer (cdata RData) :=
      set_pmd ↦ gensem set_pmd_spec
          ⊕ walk_pte ↦ gensem walk_pte_spec
          ⊕ walk_pmd ↦ gensem walk_pmd_spec
          ⊕ walk_pgd ↦ gensem walk_pgd_spec
          ⊕ set_pte ↦ gensem set_pte_spec
          ⊕ walk_pud ↦ gensem walk_pud_spec.

    Definition PTWalk_passthrough : compatlayer (cdata RData) :=
      set_vm_inc_exe ↦ gensem set_vm_inc_exe_spec
          ⊕ get_sys_reg_desc_val ↦ gensem get_sys_reg_desc_val_spec
          ⊕ host_dabt_is_write ↦ gensem host_dabt_is_write_spec
          ⊕ set_vm_kvm ↦ gensem set_vm_kvm_spec
          ⊕ host_get_fault_ipa ↦ gensem host_get_fault_ipa_spec
          ⊕ get_next_vmid ↦ gensem get_next_vmid_spec
          ⊕ exit_populate_fault ↦ gensem exit_populate_fault_spec
          ⊕ get_smmu_cfg_vmid ↦ gensem get_smmu_cfg_vmid_spec
          ⊕ get_smmu_num ↦ gensem get_smmu_num_spec
          ⊕ set_smmu_pmd_next ↦ gensem set_smmu_pmd_next_spec
          ⊕ decrypt_mem_buf ↦ gensem decrypt_mem_buf_spec
          ⊕ acquire_lock_spt ↦ gensem acquire_lock_spt_spec
          ⊕ get_mem_region_cnt ↦ gensem get_mem_region_cnt_spec
          ⊕ get_vm_load_size ↦ gensem get_vm_load_size_spec
          ⊕ fetch_from_doracle ↦ gensem fetch_from_doracle_spec
          ⊕ reset_fp_regs ↦ gensem reset_fp_regs_spec
          ⊕ dev_load_raw ↦ gensem dev_load_raw_spec
          ⊕ timer_set_cntvoff ↦ gensem timer_set_cntvoff_spec
          ⊕ encrypt_gp_regs ↦ gensem encrypt_gp_regs_spec
          ⊕ acquire_lock_vm ↦ gensem acquire_lock_vm_spec
          ⊕ get_int_pstate ↦ gensem get_int_pstate_spec
          ⊕ get_vm_inc_exe ↦ gensem get_vm_inc_exe_spec
          ⊕ release_lock_s2page ↦ gensem release_lock_s2page_spec
          ⊕ set_vm_vcpu ↦ gensem set_vm_vcpu_spec
          ⊕ host_dabt_get_rd ↦ gensem host_dabt_get_rd_spec
          ⊕ acquire_lock_s2page ↦ gensem acquire_lock_s2page_spec
          ⊕ writel_relaxed ↦ gensem writel_relaxed_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ host_skip_instr ↦ gensem host_skip_instr_spec
          ⊕ vm_to_core ↦ gensem vm_to_core_spec
          ⊕ get_smmu_num_context_banks ↦ gensem get_smmu_num_context_banks_spec
          ⊕ get_pt_vttbr ↦ gensem get_pt_vttbr_spec
          ⊕ set_next_remap_ptr ↦ gensem set_next_remap_ptr_spec
          ⊕ get_vm_fault_addr ↦ gensem get_vm_fault_addr_spec
          ⊕ host_dabt_get_as ↦ gensem host_dabt_get_as_spec
          ⊕ get_shadow_esr ↦ gensem get_shadow_esr_spec
          ⊕ set_vcpu_state ↦ gensem set_vcpu_state_spec
          ⊕ get_smmu_size ↦ gensem get_smmu_size_spec
          ⊕ set_per_cpu ↦ gensem set_per_cpu_spec
          ⊕ acquire_lock_smmu ↦ gensem acquire_lock_smmu_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ acquire_lock_core ↦ gensem acquire_lock_core_spec
          ⊕ writeq_relaxed ↦ gensem writeq_relaxed_spec
          ⊕ read_actlr_el1 ↦ gensem read_actlr_el1_spec
          ⊕ get_mem_region_base ↦ gensem get_mem_region_base_spec
          ⊕ release_lock_smmu ↦ gensem release_lock_smmu_spec
          ⊕ set_s2_page_gfn ↦ gensem set_s2_page_gfn_spec
          ⊕ decrypt_sys_regs ↦ gensem decrypt_sys_regs_spec
          ⊕ vm_el2_restore_state ↦ gensem vm_el2_restore_state_spec
          ⊕ set_smmu_cfg_vmid ↦ gensem set_smmu_cfg_vmid_spec
          ⊕ get_exception_vector ↦ gensem get_exception_vector_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ set_smmu_pgd_next ↦ gensem set_smmu_pgd_next_spec
          ⊕ get_int_pc ↦ gensem get_int_pc_spec
          ⊕ get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ deactivate_traps ↦ gensem deactivate_traps_spec
          ⊕ get_s2_page_count ↦ gensem get_s2_page_count_spec
          ⊕ set_next_vmid ↦ gensem set_next_vmid_spec
          ⊕ encrypt_sys_regs ↦ gensem encrypt_sys_regs_spec
          ⊕ smmu_pt_clear ↦ gensem smmu_pt_clear_spec
          ⊕ set_vm_load_addr ↦ gensem set_vm_load_addr_spec
          ⊕ get_shared_kvm ↦ gensem get_shared_kvm_spec
          ⊕ check64 ↦ gensem check64_spec
          ⊕ readq_relaxed ↦ gensem readq_relaxed_spec
          ⊕ get_s2_page_gfn ↦ gensem get_s2_page_gfn_spec
          ⊕ get_smmu_base ↦ gensem get_smmu_base_spec
          ⊕ core_to_vm ↦ gensem core_to_vm_spec
          ⊕ set_vm_remap_addr ↦ gensem set_vm_remap_addr_spec
          ⊕ readl_relaxed ↦ gensem readl_relaxed_spec
          ⊕ release_lock_spt ↦ gensem release_lock_spt_spec
          ⊕ restore_sysregs ↦ gensem restore_sysregs_spec
          ⊕ timer_enable_traps ↦ gensem timer_enable_traps_spec
          ⊕ fpsimd_restore_state ↦ gensem fpsimd_restore_state_spec
          ⊕ set_s2_page_count ↦ gensem set_s2_page_count_spec
          ⊕ smmu_pt_store ↦ gensem smmu_pt_store_spec
          ⊕ mem_store_raw ↦ gensem mem_store_raw_spec
          ⊕ set_vm_state ↦ gensem set_vm_state_spec
          ⊕ decrypt_gp_regs ↦ gensem decrypt_gp_regs_spec
          ⊕ read_esr_el2 ↦ gensem read_esr_el2_spec
          ⊕ read_hpfar_el2 ↦ gensem read_hpfar_el2_spec
          ⊕ acquire_lock_pt ↦ gensem acquire_lock_pt_spec
          ⊕ host_el2_restore_state ↦ gensem host_el2_restore_state_spec
          ⊕ dev_store_raw ↦ gensem dev_store_raw_spec
          ⊕ get_vm_next_load_idx ↦ gensem get_vm_next_load_idx_spec
          ⊕ set_vm_mapped_pages ↦ gensem set_vm_mapped_pages_spec
          ⊕ get_s2_page_vmid ↦ gensem get_s2_page_vmid_spec
          ⊕ get_smmu_cfg_hw_ttbr ↦ gensem get_smmu_cfg_hw_ttbr_spec
          ⊕ release_lock_core ↦ gensem release_lock_core_spec
          ⊕ save_sysregs ↦ gensem save_sysregs_spec
          ⊕ release_lock_pt ↦ gensem release_lock_pt_spec
          ⊕ get_next_remap_ptr ↦ gensem get_next_remap_ptr_spec
          ⊕ check ↦ gensem check_spec
          ⊕ clear_shadow_gp_regs ↦ gensem clear_shadow_gp_regs_spec
          ⊕ verify_image ↦ gensem verify_image_spec
          ⊕ set_vm_load_size ↦ gensem set_vm_load_size_spec
          ⊕ set_s2_page_vmid ↦ gensem set_s2_page_vmid_spec
          ⊕ get_vm_remap_addr ↦ gensem get_vm_remap_addr_spec
          ⊕ release_lock_vm ↦ gensem release_lock_vm_spec
          ⊕ get_int_new_pte ↦ gensem get_int_new_pte_spec
          ⊕ get_mem_region_index ↦ gensem get_mem_region_index_spec
          ⊕ activate_traps ↦ gensem activate_traps_spec
          ⊕ get_mem_region_size ↦ gensem get_mem_region_size_spec
          ⊕ fpsimd_save_state ↦ gensem fpsimd_save_state_spec
          ⊕ get_smmu_pmd_next ↦ gensem get_smmu_pmd_next_spec
          ⊕ get_int_esr ↦ gensem get_int_esr_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ core_to_host ↦ gensem core_to_host_spec
          ⊕ set_shadow_dirty_bit ↦ gensem set_shadow_dirty_bit_spec
          ⊕ encrypt_mem_buf ↦ gensem encrypt_mem_buf_spec
          ⊕ host_to_core ↦ gensem host_to_core_spec
          ⊕ smmu_pt_load ↦ gensem smmu_pt_load_spec
          ⊕ set_vm_next_load_idx ↦ gensem set_vm_next_load_idx_spec
          ⊕ get_shadow_dirty_bit ↦ gensem get_shadow_dirty_bit_spec
          ⊕ mem_load_raw ↦ gensem mem_load_raw_spec
          ⊕ get_int_gpr ↦ gensem get_int_gpr_spec
          ⊕ set_int_gpr ↦ gensem set_int_gpr_spec
          ⊕ get_vm_state ↦ gensem get_vm_state_spec
          ⊕ clear_phys_page ↦ gensem clear_phys_page_spec
          ⊕ get_smmu_pgd_next ↦ gensem get_smmu_pgd_next_spec
          ⊕ core_handle_sys64 ↦ gensem core_handle_sys64_spec
          ⊕ get_vm_mapped_pages ↦ gensem get_vm_mapped_pages_spec
          ⊕ get_shared_vcpu ↦ gensem get_shared_vcpu_spec
          ⊕ get_vcpu_state ↦ gensem get_vcpu_state_spec
          ⊕ get_vm_load_addr ↦ gensem get_vm_load_addr_spec.

    Definition PTWalk := PTWalk_fresh ⊕ PTWalk_passthrough.

  End LayerDef.

End PTWalkLayer.
```
