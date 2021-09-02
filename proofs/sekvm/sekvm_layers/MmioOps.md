# Layer

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

Require Import MemoryOps.Spec.
Require Import AbstractMachine.Spec.
Require Import Locks.Spec.
Require Import MmioSPTWalk.Spec.
Require Import BootOps.Spec.
Require Import MmioOps.Spec.
Require Import RData.
Require Import HypsecCommLib.
Require Import NPTWalk.Spec.
Require Import MmioRaw.Spec.
Require Import Constants.
Require Import Ident.
Require Import MemManager.Spec.
Require Import VMPower.Spec.

Local Open Scope Z_scope.

Section MmioOpsLayer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance MmioOps_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance MmioOps_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance smmu_map_page_inv: PreservesInvariants smmu_map_page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el2_free_smmu_pgd_inv: PreservesInvariants el2_free_smmu_pgd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el2_arm_lpae_clear_inv: PreservesInvariants el2_arm_lpae_clear_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el2_alloc_smmu_pgd_inv: PreservesInvariants el2_alloc_smmu_pgd_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el2_arm_lpae_iova_to_phys_inv: PreservesInvariants el2_arm_lpae_iova_to_phys_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance emulate_mmio_inv: PreservesInvariants emulate_mmio_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smmu_assign_page_inv: PreservesInvariants smmu_assign_page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_store_ref_inv: PreservesInvariants mem_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_pc_inv: PreservesInvariants get_int_pc_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_sys_reg_desc_val_inv: PreservesInvariants get_sys_reg_desc_val_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vmid_inv: PreservesInvariants get_cur_vmid_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smmu_init_pte_inv: PreservesInvariants smmu_init_pte_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance deactivate_traps_inv: PreservesInvariants deactivate_traps_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_load_ref_inv: PreservesInvariants dev_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_boot_info_inv: PreservesInvariants set_boot_info_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance load_encrypted_vcpu_inv: PreservesInvariants load_encrypted_vcpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance revoke_stage2_sg_gpa_inv: PreservesInvariants revoke_stage2_sg_gpa_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance clear_vm_range_inv: PreservesInvariants clear_vm_range_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance register_kvm_inv: PreservesInvariants register_kvm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance exit_populate_fault_inv: PreservesInvariants exit_populate_fault_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance remap_vm_image_inv: PreservesInvariants remap_vm_image_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance mem_load_ref_inv: PreservesInvariants mem_load_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_to_vm_inv: PreservesInvariants core_to_vm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance search_load_info_inv: PreservesInvariants search_load_info_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance map_page_host_inv: PreservesInvariants map_page_host_spec.
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

    Global Instance set_vm_poweroff_inv: PreservesInvariants set_vm_poweroff_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance fpsimd_restore_state_inv: PreservesInvariants fpsimd_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance reset_fp_regs_inv: PreservesInvariants reset_fp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance grant_stage2_sg_gpa_inv: PreservesInvariants grant_stage2_sg_gpa_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_hpfar_el2_inv: PreservesInvariants read_hpfar_el2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_esr_el2_inv: PreservesInvariants read_esr_el2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance timer_set_cntvoff_inv: PreservesInvariants timer_set_cntvoff_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_pstate_inv: PreservesInvariants get_int_pstate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_el2_restore_state_inv: PreservesInvariants host_el2_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_encrypt_buf_inv: PreservesInvariants save_encrypt_buf_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance map_io_inv: PreservesInvariants map_io_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_poweron_inv: PreservesInvariants get_vm_poweron_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_shadow_ctxt_inv: PreservesInvariants set_shadow_ctxt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance verify_and_load_images_inv: PreservesInvariants verify_and_load_images_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance dev_store_ref_inv: PreservesInvariants dev_store_ref_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_to_core_inv: PreservesInvariants vm_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_sysregs_inv: PreservesInvariants save_sysregs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance load_decrypt_buf_inv: PreservesInvariants load_decrypt_buf_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance check_inv: PreservesInvariants check_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_vm_fault_addr_inv: PreservesInvariants get_vm_fault_addr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_new_pte_inv: PreservesInvariants get_int_new_pte_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance activate_traps_inv: PreservesInvariants activate_traps_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_esr_inv: PreservesInvariants get_shadow_esr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance register_vcpu_inv: PreservesInvariants register_vcpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance fpsimd_save_state_inv: PreservesInvariants fpsimd_save_state_spec.
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

    Global Instance set_per_cpu_inv: PreservesInvariants set_per_cpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_vcpuid_inv: PreservesInvariants get_cur_vcpuid_spec.
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

    Global Instance prot_and_map_vm_s2pt_inv: PreservesInvariants prot_and_map_vm_s2pt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance host_to_core_inv: PreservesInvariants host_to_core_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_actlr_el1_inv: PreservesInvariants read_actlr_el1_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_dirty_bit_inv: PreservesInvariants get_shadow_dirty_bit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_int_gpr_inv: PreservesInvariants get_int_gpr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance vm_el2_restore_state_inv: PreservesInvariants vm_el2_restore_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_int_gpr_inv: PreservesInvariants set_int_gpr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_exception_vector_inv: PreservesInvariants get_exception_vector_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_encrypted_vcpu_inv: PreservesInvariants save_encrypted_vcpu_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance core_handle_sys64_inv: PreservesInvariants core_handle_sys64_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_shadow_ctxt_inv: PreservesInvariants get_shadow_ctxt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance clear_shadow_gp_regs_inv: PreservesInvariants clear_shadow_gp_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition MmioOps_fresh : compatlayer (cdata RData) :=
      smmu_map_page ↦ gensem smmu_map_page_spec
          ⊕ el2_free_smmu_pgd ↦ gensem el2_free_smmu_pgd_spec
          ⊕ el2_arm_lpae_clear ↦ gensem el2_arm_lpae_clear_spec
          ⊕ el2_alloc_smmu_pgd ↦ gensem el2_alloc_smmu_pgd_spec
          ⊕ el2_arm_lpae_iova_to_phys ↦ gensem el2_arm_lpae_iova_to_phys_spec
          ⊕ emulate_mmio ↦ gensem emulate_mmio_spec
          ⊕ smmu_assign_page ↦ gensem smmu_assign_page_spec.

    Definition MmioOps_passthrough : compatlayer (cdata RData) :=
      mem_store_ref ↦ gensem mem_store_ref_spec
          ⊕ get_int_pc ↦ gensem get_int_pc_spec
          ⊕ get_sys_reg_desc_val ↦ gensem get_sys_reg_desc_val_spec
          ⊕ get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ smmu_init_pte ↦ gensem smmu_init_pte_spec
          ⊕ deactivate_traps ↦ gensem deactivate_traps_spec
          ⊕ dev_load_ref ↦ gensem dev_load_ref_spec
          ⊕ set_boot_info ↦ gensem set_boot_info_spec
          ⊕ load_encrypted_vcpu ↦ gensem load_encrypted_vcpu_spec
          ⊕ revoke_stage2_sg_gpa ↦ gensem revoke_stage2_sg_gpa_spec
          ⊕ clear_vm_range ↦ gensem clear_vm_range_spec
          ⊕ register_kvm ↦ gensem register_kvm_spec
          ⊕ exit_populate_fault ↦ gensem exit_populate_fault_spec
          ⊕ remap_vm_image ↦ gensem remap_vm_image_spec
          ⊕ mem_load_ref ↦ gensem mem_load_ref_spec
          ⊕ core_to_vm ↦ gensem core_to_vm_spec
          ⊕ search_load_info ↦ gensem search_load_info_spec
          ⊕ map_page_host ↦ gensem map_page_host_spec
          ⊕ restore_sysregs ↦ gensem restore_sysregs_spec
          ⊕ timer_enable_traps ↦ gensem timer_enable_traps_spec
          ⊕ set_vm_poweroff ↦ gensem set_vm_poweroff_spec
          ⊕ fpsimd_restore_state ↦ gensem fpsimd_restore_state_spec
          ⊕ reset_fp_regs ↦ gensem reset_fp_regs_spec
          ⊕ grant_stage2_sg_gpa ↦ gensem grant_stage2_sg_gpa_spec
          ⊕ read_hpfar_el2 ↦ gensem read_hpfar_el2_spec
          ⊕ read_esr_el2 ↦ gensem read_esr_el2_spec
          ⊕ timer_set_cntvoff ↦ gensem timer_set_cntvoff_spec
          ⊕ get_int_pstate ↦ gensem get_int_pstate_spec
          ⊕ host_el2_restore_state ↦ gensem host_el2_restore_state_spec
          ⊕ save_encrypt_buf ↦ gensem save_encrypt_buf_spec
          ⊕ map_io ↦ gensem map_io_spec
          ⊕ get_vm_poweron ↦ gensem get_vm_poweron_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ verify_and_load_images ↦ gensem verify_and_load_images_spec
          ⊕ dev_store_ref ↦ gensem dev_store_ref_spec
          ⊕ vm_to_core ↦ gensem vm_to_core_spec
          ⊕ save_sysregs ↦ gensem save_sysregs_spec
          ⊕ load_decrypt_buf ↦ gensem load_decrypt_buf_spec
          ⊕ check ↦ gensem check_spec
          ⊕ get_vm_fault_addr ↦ gensem get_vm_fault_addr_spec
          ⊕ get_int_new_pte ↦ gensem get_int_new_pte_spec
          ⊕ activate_traps ↦ gensem activate_traps_spec
          ⊕ get_shadow_esr ↦ gensem get_shadow_esr_spec
          ⊕ register_vcpu ↦ gensem register_vcpu_spec
          ⊕ fpsimd_save_state ↦ gensem fpsimd_save_state_spec
          ⊕ get_int_esr ↦ gensem get_int_esr_spec
          ⊕ panic ↦ gensem panic_spec
          ⊕ set_per_cpu ↦ gensem set_per_cpu_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ core_to_host ↦ gensem core_to_host_spec
          ⊕ set_shadow_dirty_bit ↦ gensem set_shadow_dirty_bit_spec
          ⊕ prot_and_map_vm_s2pt ↦ gensem prot_and_map_vm_s2pt_spec
          ⊕ host_to_core ↦ gensem host_to_core_spec
          ⊕ read_actlr_el1 ↦ gensem read_actlr_el1_spec
          ⊕ get_shadow_dirty_bit ↦ gensem get_shadow_dirty_bit_spec
          ⊕ get_int_gpr ↦ gensem get_int_gpr_spec
          ⊕ vm_el2_restore_state ↦ gensem vm_el2_restore_state_spec
          ⊕ set_int_gpr ↦ gensem set_int_gpr_spec
          ⊕ get_exception_vector ↦ gensem get_exception_vector_spec
          ⊕ save_encrypted_vcpu ↦ gensem save_encrypted_vcpu_spec
          ⊕ core_handle_sys64 ↦ gensem core_handle_sys64_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ clear_shadow_gp_regs ↦ gensem clear_shadow_gp_regs_spec.

    Definition MmioOps := MmioOps_fresh ⊕ MmioOps_passthrough.

  End LayerDef.

End MmioOpsLayer.
```
