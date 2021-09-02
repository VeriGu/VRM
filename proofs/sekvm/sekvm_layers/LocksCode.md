# Code

```coq
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Cop.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.

Require Import Ident.
Require Import Constants.
Require Import RData.

Local Open Scope Z_scope.

Definition _Rd : ident := 999%positive.
Definition _activate_traps := 1%positive.
Definition _addr := 2%positive.
Definition _alloc_remap_addr := 3%positive.
Definition _alloc_smmu := 4%positive.
Definition _arg := 5%positive.
Definition _assign_pfn_to_smmu := 6%positive.
Definition _assign_smmu := 7%positive.
Definition _base := 8%positive.
Definition _cbndx := 9%positive.
Definition _check := 10%positive.
Definition _check64 := 11%positive.
Definition _clear_smmu := 12%positive.
Definition _core_handle_pvops := 13%positive.
Definition _cur_ticket := 14%positive.
Definition _cur_vcpuid := 15%positive.
Definition _cur_vmid := 16%positive.
Definition _deactivate_traps := 17%positive.
Definition _emulate_mmio := 18%positive.
Definition _end := 19%positive.
Definition _esr := 20%positive.
Definition _fpsimd_restore_state := 21%positive.
Definition _fpsimd_save_state := 22%positive.
Definition _gen_vmid := 23%positive.
Definition _get_cur_vcpuid := 24%positive.
Definition _get_cur_vmid := 25%positive.
Definition _get_int_run_vcpuid := 26%positive.
Definition _get_next_remap_ptr := 27%positive.
Definition _get_next_vmid := 28%positive.
Definition _get_shadow_ctxt := 29%positive.
Definition _get_shared_kvm := 30%positive.
Definition _get_shared_vcpu := 31%positive.
Definition _get_vcpu_state := 32%positive.
Definition _get_vm_load_addr := 33%positive.
Definition _get_vm_load_size := 34%positive.
Definition _get_vm_mapped_pages := 35%positive.
Definition _get_vm_next_load_idx := 36%positive.
Definition _get_vm_remap_addr := 37%positive.
Definition _get_vm_state := 38%positive.
Definition _gfn := 39%positive.
Definition _gpa := 40%positive.
Definition _grant_stage2_sg_gpa := 41%positive.
Definition _handle_host_stage2_fault := 42%positive.
Definition _host_el2_restore_state := 43%positive.
Definition _index := 44%positive.
Definition _init_spt := 45%positive.
Definition _iova := 46%positive.
Definition _kvm := 47%positive.
Definition _lk := 48%positive.
Definition _load_addr := 49%positive.
Definition _load_idx := 50%positive.
Definition _load_info_cnt := 51%positive.
Definition _main := 52%positive.
Definition _map_io := 53%positive.
Definition _map_page_host := 54%positive.
Definition _map_s2pt := 55%positive.
Definition _map_smmu := 56%positive.
Definition _map_vm_io := 57%positive.
Definition _mapped := 58%positive.
Definition _my_ticket := 59%positive.
Definition _num := 60%positive.
Definition _pa := 61%positive.
Definition _page_count := 62%positive.
Definition _pfn := 63%positive.
Definition _pgnum := 64%positive.
Definition _prot_and_map_vm_s2pt := 65%positive.
Definition _pte := 66%positive.
Definition _read_esr_el2 := 67%positive.
Definition _read_hpfar_el2 := 68%positive.
Definition _register_kvm := 69%positive.
Definition _register_vcpu := 70%positive.
Definition _remap := 71%positive.
Definition _remap_addr := 72%positive.
Definition _remap_vm_image := 73%positive.
Definition _restore_host := 74%positive.
Definition _restore_shadow_kvm_regs := 75%positive.
Definition _restore_sysregs := 76%positive.
Definition _restore_vm := 77%positive.
Definition _ret := 78%positive.
Definition _revoke_stage2_sg_gpa := 79%positive.
Definition _save_host := 80%positive.
Definition _save_shadow_kvm_regs := 81%positive.
Definition _save_sysregs := 82%positive.
Definition _save_vm := 83%positive.
Definition _search_load_info := 84%positive.
Definition _set_boot_info := 85%positive.
Definition _set_next_remap_ptr := 86%positive.
Definition _set_next_vmid := 87%positive.
Definition _set_per_cpu := 88%positive.
Definition _set_shadow_ctxt := 89%positive.
Definition _set_vcpu_active := 90%positive.
Definition _set_vcpu_inactive := 91%positive.
Definition _set_vcpu_state := 92%positive.
Definition _set_vm_kvm := 93%positive.
Definition _set_vm_load_addr := 94%positive.
Definition _set_vm_load_size := 95%positive.
Definition _set_vm_mapped_pages := 96%positive.
Definition _set_vm_next_load_idx := 97%positive.
Definition _set_vm_remap_addr := 98%positive.
Definition _set_vm_state := 99%positive.
Definition _set_vm_vcpu := 100%positive.
Definition _size := 101%positive.
Definition _start := 102%positive.
Definition _state := 103%positive.
Definition _target := 104%positive.
Definition _target_addr := 105%positive.
Definition _timer_enable_traps := 106%positive.
Definition _unmap_and_load_vm_image := 107%positive.
Definition _unmap_smmu_page := 108%positive.
Definition _update_smmu_page := 109%positive.
Definition _valid := 110%positive.
Definition _vcpu := 111%positive.
Definition _vcpu_state := 112%positive.
Definition _vcpuid := 113%positive.
Definition _verify_and_load_images := 114%positive.
Definition _verify_image := 115%positive.
Definition _vm_el2_restore_state := 116%positive.
Definition _vm_state := 117%positive.
Definition _vmid := 118%positive.
Definition _walk_s2pt := 119%positive.


Definition acquire_lock_body lk_expr :=
  (Ssequence
    (Scall None
      (Evar wait_hlock (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      (lk_expr :: nil)
    )
    (Scall None
      (Evar acquire_shared (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      (lk_expr :: nil)
    )
  ).

Definition release_lock_body lk_expr :=
  (Ssequence
    (Scall None
      (Evar release_shared (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      (lk_expr :: nil)
    )
    (Scall None
      (Evar pass_hlock (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      (lk_expr :: nil)
    )
  ).

Definition lock_idx_constant lk := (Econst_int (Int.repr lk) tuint).

Definition lock_idx_offset base lk:=
  (Ebinop Oadd (Econst_int (Int.repr base) tuint) (Etempvar lk tuint) tuint).

Definition acquire_lock_pt_body :=
  acquire_lock_body (lock_idx_offset lock_idx_pt_base _vmid).

Definition f_acquire_lock_pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_pt_body
|}.

Definition acquire_lock_s2page_body :=
  acquire_lock_body (lock_idx_constant lock_idx_s2page).

Definition f_acquire_lock_s2page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_s2page_body
|}.


Definition acquire_lock_core_body :=
  acquire_lock_body (lock_idx_constant lock_idx_core).

Definition f_acquire_lock_core := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_core_body
|}.

Definition acquire_lock_spt_body :=
  acquire_lock_body (lock_idx_constant lock_idx_spt).

Definition f_acquire_lock_spt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_spt_body
|}.

Definition acquire_lock_smmu_body :=
  acquire_lock_body (lock_idx_constant lock_idx_smmu).

Definition f_acquire_lock_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_smmu_body
|}.

Definition acquire_lock_vm_body :=
  acquire_lock_body (lock_idx_offset lock_idx_vm_base _vmid).

Definition f_acquire_lock_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := acquire_lock_vm_body
|}.

Definition release_lock_pt_body :=
  release_lock_body (lock_idx_offset lock_idx_pt_base _vmid).

Definition f_release_lock_pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_pt_body
|}.

Definition release_lock_s2page_body :=
  release_lock_body (lock_idx_constant lock_idx_s2page).

Definition f_release_lock_s2page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_s2page_body
|}.

Definition release_lock_core_body :=
  release_lock_body (lock_idx_constant lock_idx_core).

Definition f_release_lock_core := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_core_body
|}.

Definition release_lock_spt_body :=
  release_lock_body (lock_idx_constant lock_idx_spt).

Definition f_release_lock_spt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_spt_body
|}.

Definition release_lock_smmu_body :=
  release_lock_body (lock_idx_constant lock_idx_smmu).

Definition f_release_lock_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_smmu_body
|}.

Definition release_lock_vm_body :=
  release_lock_body (lock_idx_offset lock_idx_vm_base _vmid).

Definition f_release_lock_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := release_lock_vm_body
|}.
```
