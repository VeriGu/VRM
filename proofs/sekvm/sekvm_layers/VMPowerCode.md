# VMPowerCode

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
Definition ___compcert_va_int64 := 1%positive.
Definition _addr := 2%positive.
Definition _alloc := 3%positive.
Definition _arg := 4%positive.
Definition _arg1 := 5%positive.
Definition _arg2 := 6%positive.
Definition _arg3 := 7%positive.
Definition _arg4 := 8%positive.
Definition _arg5 := 9%positive.
Definition _base := 10%positive.
Definition _cb_offset := 11%positive.
Definition _cbndx := 12%positive.
Definition _cnt := 13%positive.
Definition _count := 14%positive.
Definition _cur_ticket := 15%positive.
Definition _cur_vcpuid := 16%positive.
Definition _cur_vmid := 17%positive.
Definition _data := 18%positive.
Definition _dirty := 19%positive.
Definition _ec := 20%positive.
Definition _end := 21%positive.
Definition _esr := 22%positive.
Definition _esr_el2 := 23%positive.
Definition _exit_type := 24%positive.
Definition _fault_ipa := 25%positive.
Definition _get_now := 26%positive.
Definition _gfn := 27%positive.
Definition _gpa := 28%positive.
Definition _hsr := 29%positive.
Definition _hsr_ec := 30%positive.
Definition _i := 31%positive.
Definition _inbuf := 32%positive.
Definition _inc_exe := 33%positive.
Definition _incr_now := 34%positive.
Definition _incr_ticket := 35%positive.
Definition _index := 36%positive.
Definition _inowner := 37%positive.
Definition _inpfn := 38%positive.
Definition _iova := 39%positive.
Definition _is_write := 40%positive.
Definition _kvm := 41%positive.
Definition _len := 42%positive.
Definition _level := 43%positive.
Definition _lk := 44%positive.
Definition _load_addr := 45%positive.
Definition _load_idx := 46%positive.
Definition _load_info_cnt := 47%positive.
Definition _log_hold := 48%positive.
Definition _log_incr := 49%positive.
Definition _main := 50%positive.
Definition _map := 51%positive.
Definition _mapped := 52%positive.
Definition _mpidr := 53%positive.
Definition _my_ticket := 54%positive.
Definition _n := 55%positive.
Definition _new_pc := 56%positive.
Definition _next := 57%positive.
Definition _num := 58%positive.
Definition _num_context_banks := 59%positive.
Definition _offset := 60%positive.
Definition _outbuf := 61%positive.
Definition _outowner := 62%positive.
Definition _outpfn := 63%positive.
Definition _owner := 64%positive.
Definition _p_index := 65%positive.
Definition _pa := 66%positive.
Definition _paddr := 67%positive.
Definition _page_count := 68%positive.
Definition _pass_hlock := 69%positive.
Definition _pass_lock := 70%positive.
Definition _pass_qlock := 71%positive.
Definition _pc := 72%positive.
Definition _perm := 73%positive.
Definition _pfn := 74%positive.
Definition _pgd := 75%positive.
Definition _pgd_idx := 76%positive.
Definition _pgd_pa := 77%positive.
Definition _pgnum := 78%positive.
Definition _pmd := 79%positive.
Definition _pmd_idx := 80%positive.
Definition _pmd_pa := 81%positive.
Definition _power := 82%positive.
Definition _prot := 83%positive.
Definition _psci_fn := 84%positive.
Definition _pstate := 85%positive.
Definition _pte := 86%positive.
Definition _pte_idx := 87%positive.
Definition _pte_pa := 88%positive.
Definition _pud := 89%positive.
Definition _pud_idx := 90%positive.
Definition _pud_pa := 91%positive.
Definition _r_index := 92%positive.
Definition _reg := 93%positive.
Definition _remap := 94%positive.
Definition _remap_addr := 95%positive.
Definition _res := 96%positive.
Definition _ret := 97%positive.
Definition _ret64 := 98%positive.
Definition _rt := 99%positive.
Definition _size := 100%positive.
Definition _smmu_enable := 101%positive.
Definition _smmu_index := 102%positive.
Definition _start := 103%positive.
Definition _state := 104%positive.
Definition _t_vmid := 105%positive.
Definition _target := 106%positive.
Definition _target_addr := 107%positive.
Definition _target_vmid := 108%positive.
Definition _total_smmu := 109%positive.
Definition _ttbr := 110%positive.
Definition _ttbr_pa := 111%positive.
Definition _type := 112%positive.
Definition _val := 113%positive.
Definition _valid := 114%positive.
Definition _vcpu := 115%positive.
Definition _vcpu_state := 116%positive.
Definition _vcpuid := 117%positive.
Definition _vm_state := 118%positive.
Definition _vmid := 119%positive.
Definition _vttbr := 120%positive.
Definition _vttbr_pa := 121%positive.
Definition _wait_hlock := 122%positive.
Definition _wait_lock := 123%positive.
Definition _wait_qlock := 124%positive.
Definition _write_val := 125%positive.
Definition _t'1 := 126%positive.
Definition _t'2 := 127%positive.

Definition get_vm_poweron_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                       (Econst_int (Int.repr 4) tuint) tint)
          (Sset _ret (Econst_int (Int.repr 0) tuint))
          (Sset _ret (Econst_int (Int.repr 1) tuint)))
        (Ssequence
          (Scall None
            (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
            ((Etempvar _vmid tuint) :: nil))
          (Ssequence
            (Scall (Some _t'2)
              (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
              ((Etempvar _ret tuint) :: nil))
            (Sreturn (Some (Etempvar _t'2 tuint)))))))).

Definition f_get_vm_poweron := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_ret, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := get_vm_poweron_body
|}.

Definition set_vm_poweroff_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar set_vm_state (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                              cc_default))
        ((Etempvar _vmid tuint) :: (Econst_int (Int.repr 4) tuint) :: nil))
      (Scall None
        (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Etempvar _vmid tuint) :: nil)))).

Definition f_set_vm_poweroff := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_vm_poweroff_body
|}.
```
