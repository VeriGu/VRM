# TrapDispatcherProofCode

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

  Section host_hvc_dispatcher_proof.

    Let L : compatlayer (cdata RData) :=
      get_cur_vmid ↦ gensem get_cur_vmid_spec
          ⊕ get_cur_vcpuid ↦ gensem get_cur_vcpuid_spec
          ⊕ get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ set_shadow_ctxt ↦ gensem set_shadow_ctxt_spec
          ⊕ timer_set_cntvoff ↦ gensem timer_set_cntvoff_spec
          ⊕ clear_vm_stage2_range ↦ gensem clear_vm_stage2_range_spec
          ⊕ set_boot_info ↦ gensem set_boot_info_spec
          ⊕ remap_vm_image ↦ gensem remap_vm_image_spec
          ⊕ verify_and_load_images ↦ gensem verify_and_load_images_spec
          ⊕ el2_arm_lpae_map ↦ gensem el2_arm_lpae_map_spec
          ⊕ el2_arm_lpae_iova_to_phys ↦ gensem el2_arm_lpae_iova_to_phys_spec
          ⊕ el2_arm_lpae_clear ↦ gensem el2_arm_lpae_clear_spec
          ⊕ el2_free_smmu_pgd ↦ gensem el2_free_smmu_pgd_spec
          ⊕ el2_alloc_smmu_pgd ↦ gensem el2_alloc_smmu_pgd_spec
          ⊕ register_kvm ↦ gensem register_kvm_spec
          ⊕ register_vcpu ↦ gensem register_vcpu_spec
          ⊕ kvm_phys_addr_ioremap ↦ gensem kvm_phys_addr_ioremap_spec
          ⊕ panic ↦ gensem panic_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_get_cur_vmid: block.
      Hypothesis h_get_cur_vmid_s : Genv.find_symbol ge get_cur_vmid = Some b_get_cur_vmid.
      Hypothesis h_get_cur_vmid_p : Genv.find_funct_ptr ge b_get_cur_vmid
                                    = Some (External (EF_external get_cur_vmid
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
      Variable b_get_cur_vcpuid: block.
      Hypothesis h_get_cur_vcpuid_s : Genv.find_symbol ge get_cur_vcpuid = Some b_get_cur_vcpuid.
      Hypothesis h_get_cur_vcpuid_p : Genv.find_funct_ptr ge b_get_cur_vcpuid
                                      = Some (External (EF_external get_cur_vcpuid
                                                       (signature_of_type Tnil tuint cc_default))
                                             Tnil tuint cc_default).
      Variable b_get_shadow_ctxt: block.
      Hypothesis h_get_shadow_ctxt_s : Genv.find_symbol ge get_shadow_ctxt = Some b_get_shadow_ctxt.
      Hypothesis h_get_shadow_ctxt_p : Genv.find_funct_ptr ge b_get_shadow_ctxt
                                       = Some (External (EF_external get_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tulong cc_default).
      Variable b_set_shadow_ctxt: block.
      Hypothesis h_set_shadow_ctxt_s : Genv.find_symbol ge set_shadow_ctxt = Some b_set_shadow_ctxt.
      Hypothesis h_set_shadow_ctxt_p : Genv.find_funct_ptr ge b_set_shadow_ctxt
                                       = Some (External (EF_external set_shadow_ctxt
                                                        (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default))
                                              (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_timer_set_cntvoff: block.
      Hypothesis h_timer_set_cntvoff_s : Genv.find_symbol ge timer_set_cntvoff = Some b_timer_set_cntvoff.
      Hypothesis h_timer_set_cntvoff_p : Genv.find_funct_ptr ge b_timer_set_cntvoff
                                         = Some (External (EF_external timer_set_cntvoff
                                                          (signature_of_type Tnil tvoid cc_default))
                                                Tnil tvoid cc_default).
      Variable b_clear_vm_stage2_range: block.
      Hypothesis h_clear_vm_stage2_range_s : Genv.find_symbol ge clear_vm_stage2_range = Some b_clear_vm_stage2_range.
      Hypothesis h_clear_vm_stage2_range_p : Genv.find_funct_ptr ge b_clear_vm_stage2_range
                                             = Some (External (EF_external clear_vm_stage2_range
                                                              (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                    (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_set_boot_info: block.
      Hypothesis h_set_boot_info_s : Genv.find_symbol ge set_boot_info = Some b_set_boot_info.
      Hypothesis h_set_boot_info_p : Genv.find_funct_ptr ge b_set_boot_info
                                     = Some (External (EF_external set_boot_info
                                                      (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                            (Tcons tuint (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
      Variable b_remap_vm_image: block.
      Hypothesis h_remap_vm_image_s : Genv.find_symbol ge remap_vm_image = Some b_remap_vm_image.
      Hypothesis h_remap_vm_image_p : Genv.find_funct_ptr ge b_remap_vm_image
                                      = Some (External (EF_external remap_vm_image
                                                       (signature_of_type (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_verify_and_load_images: block.
      Hypothesis h_verify_and_load_images_s : Genv.find_symbol ge verify_and_load_images = Some b_verify_and_load_images.
      Hypothesis h_verify_and_load_images_p : Genv.find_funct_ptr ge b_verify_and_load_images
                                              = Some (External (EF_external verify_and_load_images
                                                               (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                     (Tcons tuint Tnil) tvoid cc_default).
      Variable b_el2_arm_lpae_map: block.
      Hypothesis h_el2_arm_lpae_map_s : Genv.find_symbol ge el2_arm_lpae_map = Some b_el2_arm_lpae_map.
      Hypothesis h_el2_arm_lpae_map_p : Genv.find_funct_ptr ge b_el2_arm_lpae_map
                                        = Some (External (EF_external el2_arm_lpae_map
                                                         (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tuint (Tcons tuint Tnil))))) tvoid cc_default))
                                               (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tuint (Tcons tuint Tnil))))) tvoid cc_default).
      Variable b_el2_arm_lpae_iova_to_phys: block.
      Hypothesis h_el2_arm_lpae_iova_to_phys_s : Genv.find_symbol ge el2_arm_lpae_iova_to_phys = Some b_el2_arm_lpae_iova_to_phys.
      Hypothesis h_el2_arm_lpae_iova_to_phys_p : Genv.find_funct_ptr ge b_el2_arm_lpae_iova_to_phys
                                                 = Some (External (EF_external el2_arm_lpae_iova_to_phys
                                                                  (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                                        (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_el2_arm_lpae_clear: block.
      Hypothesis h_el2_arm_lpae_clear_s : Genv.find_symbol ge el2_arm_lpae_clear = Some b_el2_arm_lpae_clear.
      Hypothesis h_el2_arm_lpae_clear_p : Genv.find_funct_ptr ge b_el2_arm_lpae_clear
                                          = Some (External (EF_external el2_arm_lpae_clear
                                                           (signature_of_type (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                                 (Tcons tulong (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_el2_free_smmu_pgd: block.
      Hypothesis h_el2_free_smmu_pgd_s : Genv.find_symbol ge el2_free_smmu_pgd = Some b_el2_free_smmu_pgd.
      Hypothesis h_el2_free_smmu_pgd_p : Genv.find_funct_ptr ge b_el2_free_smmu_pgd
                                         = Some (External (EF_external el2_free_smmu_pgd
                                                          (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                                (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_el2_alloc_smmu_pgd: block.
      Hypothesis h_el2_alloc_smmu_pgd_s : Genv.find_symbol ge el2_alloc_smmu_pgd = Some b_el2_alloc_smmu_pgd.
      Hypothesis h_el2_alloc_smmu_pgd_p : Genv.find_funct_ptr ge b_el2_alloc_smmu_pgd
                                          = Some (External (EF_external el2_alloc_smmu_pgd
                                                           (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
                                                 (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).
      Variable b_register_kvm: block.
      Hypothesis h_register_kvm_s : Genv.find_symbol ge register_kvm = Some b_register_kvm.
      Hypothesis h_register_kvm_p : Genv.find_funct_ptr ge b_register_kvm
                                    = Some (External (EF_external register_kvm
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
      Variable b_register_vcpu: block.
      Hypothesis h_register_vcpu_s : Genv.find_symbol ge register_vcpu = Some b_register_vcpu.
      Hypothesis h_register_vcpu_p : Genv.find_funct_ptr ge b_register_vcpu
                                     = Some (External (EF_external register_vcpu
                                                      (signature_of_type (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons tuint (Tcons tuint Tnil)) tvoid cc_default).
      Variable b_kvm_phys_addr_ioremap: block.
      Hypothesis h_kvm_phys_addr_ioremap_s : Genv.find_symbol ge kvm_phys_addr_ioremap = Some b_kvm_phys_addr_ioremap.
      Hypothesis h_kvm_phys_addr_ioremap_p : Genv.find_funct_ptr ge b_kvm_phys_addr_ioremap
                                             = Some (External (EF_external kvm_phys_addr_ioremap
                                                              (signature_of_type (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                                    (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
      Variable b_panic: block.
      Hypothesis h_panic_s : Genv.find_symbol ge panic = Some b_panic.
      Hypothesis h_panic_p : Genv.find_funct_ptr ge b_panic
                             = Some (External (EF_external panic
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).

      Lemma host_hvc_dispatcher_body_correct:
        forall m d d' env le 
               (Henv: env = PTree.empty _)
               (Hinv: high_level_invariant d)
               (Hspec: host_hvc_dispatcher_spec0  d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) host_hvc_dispatcher_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec host_hvc_dispatcher_body; admit
      Qed.
    End BodyProof.

    Theorem host_hvc_dispatcher_code_correct:
      spec_le (host_hvc_dispatcher ↦ host_hvc_dispatcher_spec_low) (〚 host_hvc_dispatcher ↦ f_host_hvc_dispatcher 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (host_hvc_dispatcher_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp b8 Hb8fs Hb8fp b9 Hb9fs Hb9fp b10 Hb10fs Hb10fp b11 Hb11fs Hb11fp b12 Hb12fs Hb12fp b13 Hb13fs Hb13fp b14 Hb14fs Hb14fp b15 Hb15fs Hb15fp b16 Hb16fs Hb16fp b17 Hb17fs Hb17fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_host_hvc_dispatcher ) ( :: nil)
               (create_undef_temps (fn_temps f_host_hvc_dispatcher)))) hinv.
    Qed.
  End host_hvc_dispatcher_proof.

  Section vm_exit_dispatcher_proof.

    Let L : compatlayer (cdata RData) :=
      get_shadow_ctxt ↦ gensem get_shadow_ctxt_spec
          ⊕ core_handle_sys64 ↦ gensem core_handle_sys64_spec
          ⊕ core_handle_pvops ↦ gensem core_handle_pvops_spec
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

      Lemma vm_exit_dispatcher_body_correct:
        forall m d d' env le vmid vcpuid res
               (Henv: env = PTree.empty _)
               (HPTvmid: PTree.get _vmid le = Some (Vint vmid))
               (HPTvcpuid: PTree.get _vcpuid le = Some (Vint vcpuid))
               (Hinv: high_level_invariant d)
               (Hspec: vm_exit_dispatcher_spec0 (Int.unsigned vmid) (Int.unsigned vcpuid) d = Some (d', (Int.unsigned res))),
             exists le', (exec_stmt ge env le ((m, d): mem) vm_exit_dispatcher_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
      Proof.
        solve_code_proof Hspec vm_exit_dispatcher_body; admit
      Qed.
    End BodyProof.

    Theorem vm_exit_dispatcher_code_correct:
      spec_le (vm_exit_dispatcher ↦ vm_exit_dispatcher_spec_low) (〚 vm_exit_dispatcher ↦ f_vm_exit_dispatcher 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (vm_exit_dispatcher_body_correct s (Genv.globalenv p) makeglobalenv
               b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_vm_exit_dispatcher ) (Vint vmid :: Vint vcpuid :: nil)
               (create_undef_temps (fn_temps f_vm_exit_dispatcher)))) hinv.
    Qed.
  End vm_exit_dispatcher_proof.

End TrapDispatcherProofLow.

```
