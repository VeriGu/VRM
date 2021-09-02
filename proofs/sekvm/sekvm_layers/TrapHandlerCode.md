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

Local Open Scope Z_scope.

Definition _Rd : ident := 999%positive.
Definition _addr := 1%positive.
Definition _alloc := 2%positive.
Definition _arg := 3%positive.
Definition _arg1 := 4%positive.
Definition _arg2 := 5%positive.
Definition _arg3 := 6%positive.
Definition _arg4 := 7%positive.
Definition _arg5 := 8%positive.
Definition _base := 9%positive.
Definition _cb_offset := 10%positive.
Definition _cbndx := 11%positive.
Definition _cnt := 12%positive.
Definition _count := 13%positive.
Definition _cur_ticket := 14%positive.
Definition _cur_vcpuid := 15%positive.
Definition _cur_vmid := 16%positive.
Definition _data := 17%positive.
Definition _end := 18%positive.
Definition _esr := 19%positive.
Definition _esr_el2 := 20%positive.
Definition _exit_type := 21%positive.
Definition _fault_ipa := 22%positive.
Definition _get_now := 23%positive.
Definition _gfn := 24%positive.
Definition _gpa := 25%positive.
Definition _hsr := 26%positive.
Definition _i := 27%positive.
Definition _inbuf := 28%positive.
Definition _inc_exe := 29%positive.
Definition _incr_now := 30%positive.
Definition _incr_ticket := 31%positive.
Definition _index := 32%positive.
Definition _inowner := 33%positive.
Definition _inpfn := 34%positive.
Definition _iova := 35%positive.
Definition _is_write := 36%positive.
Definition _kvm := 37%positive.
Definition _len := 38%positive.
Definition _level := 39%positive.
Definition _lk := 40%positive.
Definition _load_addr := 41%positive.
Definition _load_idx := 42%positive.
Definition _load_info_cnt := 43%positive.
Definition _log_hold := 44%positive.
Definition _log_incr := 45%positive.
Definition _main := 46%positive.
Definition _map := 47%positive.
Definition _mapped := 48%positive.
Definition _my_ticket := 49%positive.
Definition _n := 50%positive.
Definition _next := 51%positive.
Definition _num := 52%positive.
Definition _num_context_banks := 53%positive.
Definition _offset := 54%positive.
Definition _outbuf := 55%positive.
Definition _outowner := 56%positive.
Definition _outpfn := 57%positive.
Definition _owner := 58%positive.
Definition _p_index := 59%positive.
Definition _pa := 60%positive.
Definition _paddr := 61%positive.
Definition _page_count := 62%positive.
Definition _pass_hlock := 63%positive.
Definition _pass_lock := 64%positive.
Definition _pass_qlock := 65%positive.
Definition _perm := 66%positive.
Definition _pfn := 67%positive.
Definition _pgd := 68%positive.
Definition _pgd_idx := 69%positive.
Definition _pgd_pa := 70%positive.
Definition _pgnum := 71%positive.
Definition _pmd := 72%positive.
Definition _pmd_idx := 73%positive.
Definition _pmd_pa := 74%positive.
Definition _power := 75%positive.
Definition _prot := 76%positive.
Definition _pte := 77%positive.
Definition _pte_idx := 78%positive.
Definition _pte_pa := 79%positive.
Definition _pud := 80%positive.
Definition _pud_idx := 81%positive.
Definition _pud_pa := 82%positive.
Definition _r_index := 83%positive.
Definition _reg := 84%positive.
Definition _remap := 85%positive.
Definition _remap_addr := 86%positive.
Definition _res := 87%positive.
Definition _ret := 88%positive.
Definition _ret64 := 89%positive.
Definition _rt := 90%positive.
Definition _size := 91%positive.
Definition _smmu_enable := 92%positive.
Definition _smmu_index := 93%positive.
Definition _start := 94%positive.
Definition _state := 95%positive.
Definition _t_vmid := 96%positive.
Definition _target := 97%positive.
Definition _target_addr := 98%positive.
Definition _target_vmid := 99%positive.
Definition _total_smmu := 100%positive.
Definition _ttbr := 101%positive.
Definition _ttbr_pa := 102%positive.
Definition _type := 103%positive.
Definition _val := 104%positive.
Definition _valid := 105%positive.
Definition _vcpu := 106%positive.
Definition _vcpu_state := 107%positive.
Definition _vcpuid := 108%positive.
Definition _vm_state := 109%positive.
Definition _vmid := 110%positive.
Definition _vttbr := 111%positive.
Definition _vttbr_pa := 112%positive.
Definition _wait_hlock := 113%positive.
Definition _wait_lock := 114%positive.
Definition _wait_qlock := 115%positive.
Definition _write_val := 116%positive.

Definition host_hvc_handler_body :=
  (Scall None (Evar host_hvc_handler_raw (Tfunction Tnil tvoid cc_default))
    nil).

Definition f_host_hvc_handler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_hvc_handler_body
|}.

Definition host_npt_handler_body :=
  (Scall None (Evar host_npt_handler_raw (Tfunction Tnil tvoid cc_default))
    nil).

Definition f_host_npt_handler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_npt_handler_body
|}.

Definition host_vcpu_run_handler_body :=
  (Scall None
    (Evar host_vcpu_run_handler_raw (Tfunction Tnil tvoid cc_default)) nil).

Definition f_host_vcpu_run_handler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_vcpu_run_handler_body
|}.

Definition vm_exit_handler_body :=
  (Scall None (Evar vm_exit_handler_raw (Tfunction Tnil tvoid cc_default))
    nil).

Definition f_vm_exit_handler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := vm_exit_handler_body
|}.

Definition mem_load_body :=
  (Scall None
    (Evar mem_load_ref (Tfunction (Tcons tulong (Tcons tuint Tnil)) tvoid
                          cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) :: nil)).

Definition f_mem_load := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := mem_load_body
|}.

Definition mem_store_body :=
  (Scall None
    (Evar mem_store_ref (Tfunction (Tcons tulong (Tcons tuint Tnil)) tvoid
                           cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) :: nil)).

Definition f_mem_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := mem_store_body
|}.

Definition dev_load_body :=
  (Scall None
    (Evar dev_load_ref (Tfunction
                          (Tcons tulong
                            (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                          tvoid cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) ::
     (Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil)).

Definition f_dev_load := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: (_cbndx, tuint) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := dev_load_body
|}.

Definition dev_store_body :=
  (Scall None
    (Evar dev_store_ref (Tfunction
                           (Tcons tulong
                             (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                           tvoid cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) ::
     (Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil)).

Definition f_dev_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: (_cbndx, tuint) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := dev_store_body
|}.
```
