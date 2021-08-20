# TrapHandlerRawCode

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
Definition _ec := 18%positive.
Definition _end := 19%positive.
Definition _esr := 20%positive.
Definition _esr_el2 := 21%positive.
Definition _exit_type := 22%positive.
Definition _fault_ipa := 23%positive.
Definition _get_now := 24%positive.
Definition _gfn := 25%positive.
Definition _gpa := 26%positive.
Definition _hsr := 27%positive.
Definition _i := 28%positive.
Definition _inbuf := 29%positive.
Definition _inc_exe := 30%positive.
Definition _incr_now := 31%positive.
Definition _incr_ticket := 32%positive.
Definition _index := 33%positive.
Definition _inowner := 34%positive.
Definition _inpfn := 35%positive.
Definition _iova := 36%positive.
Definition _is_write := 37%positive.
Definition _kvm := 38%positive.
Definition _len := 39%positive.
Definition _level := 40%positive.
Definition _lk := 41%positive.
Definition _load_addr := 42%positive.
Definition _load_idx := 43%positive.
Definition _load_info_cnt := 44%positive.
Definition _log_hold := 45%positive.
Definition _log_incr := 46%positive.
Definition _main := 47%positive.
Definition _map := 48%positive.
Definition _mapped := 49%positive.
Definition _my_ticket := 50%positive.
Definition _n := 51%positive.
Definition _next := 52%positive.
Definition _num := 53%positive.
Definition _num_context_banks := 54%positive.
Definition _offset := 55%positive.
Definition _outbuf := 56%positive.
Definition _outowner := 57%positive.
Definition _outpfn := 58%positive.
Definition _owner := 59%positive.
Definition _p_index := 60%positive.
Definition _pa := 61%positive.
Definition _paddr := 62%positive.
Definition _page_count := 63%positive.
Definition _pass_hlock := 64%positive.
Definition _pass_lock := 65%positive.
Definition _pass_qlock := 66%positive.
Definition _perm := 67%positive.
Definition _pfn := 68%positive.
Definition _pgd := 69%positive.
Definition _pgd_idx := 70%positive.
Definition _pgd_pa := 71%positive.
Definition _pgnum := 72%positive.
Definition _pmd := 73%positive.
Definition _pmd_idx := 74%positive.
Definition _pmd_pa := 75%positive.
Definition _power := 76%positive.
Definition _prot := 77%positive.
Definition _pte := 78%positive.
Definition _pte_idx := 79%positive.
Definition _pte_pa := 80%positive.
Definition _pud := 81%positive.
Definition _pud_idx := 82%positive.
Definition _pud_pa := 83%positive.
Definition _r_index := 84%positive.
Definition _reg := 85%positive.
Definition _remap := 86%positive.
Definition _remap_addr := 87%positive.
Definition _res := 88%positive.
Definition _ret := 89%positive.
Definition _ret64 := 90%positive.
Definition _rt := 91%positive.
Definition _size := 92%positive.
Definition _smmu_enable := 93%positive.
Definition _smmu_index := 94%positive.
Definition _start := 95%positive.
Definition _state := 96%positive.
Definition _t_vmid := 97%positive.
Definition _target := 98%positive.
Definition _target_addr := 99%positive.
Definition _target_vmid := 100%positive.
Definition _total_smmu := 101%positive.
Definition _ttbr := 102%positive.
Definition _ttbr_pa := 103%positive.
Definition _type := 104%positive.
Definition _val := 105%positive.
Definition _valid := 106%positive.
Definition _vcpu := 107%positive.
Definition _vcpu_state := 108%positive.
Definition _vcpuid := 109%positive.
Definition _vm_state := 110%positive.
Definition _vmid := 111%positive.
Definition _vttbr := 112%positive.
Definition _vttbr_pa := 113%positive.
Definition _wait_hlock := 114%positive.
Definition _wait_lock := 115%positive.
Definition _wait_qlock := 116%positive.
Definition _write_val := 117%positive.
Definition _t'1 := 118%positive.
Definition _t'2 := 119%positive.
Definition _t'3 := 120%positive.
Definition _t'4 := 121%positive.

Definition host_hvc_handler_raw_body :=
  (Ssequence
    (Scall None (Evar host_to_core (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None (Evar host_hvc_dispatcher (Tfunction Tnil tvoid cc_default))
        nil)
      (Scall None (Evar core_to_host (Tfunction Tnil tvoid cc_default)) nil))).

Definition f_host_hvc_handler_raw := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_hvc_handler_raw_body
|}.

Definition host_npt_handler_raw_body :=
  (Ssequence
    (Scall None (Evar host_to_core (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None
        (Evar handle_host_stage2_fault (Tfunction Tnil tvoid cc_default)) nil)
      (Scall None (Evar core_to_host (Tfunction Tnil tvoid cc_default)) nil))).

Definition f_host_npt_handler_raw := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_npt_handler_raw_body
|}.

Definition host_vcpu_run_handler_raw_body :=
  (Ssequence
    (Scall None (Evar host_to_core (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None (Evar save_host (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
        (Scall None (Evar restore_vm (Tfunction Tnil tvoid cc_default)) nil)
        (Scall None (Evar core_to_vm (Tfunction Tnil tvoid cc_default)) nil)))).

Definition f_host_vcpu_run_handler_raw := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := host_vcpu_run_handler_raw_body
|}.

Definition vm_exit_handler_raw_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar get_cur_vmid (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _vmid (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _vcpuid (Etempvar _t'2 tuint)))
      (Ssequence
        (Scall None (Evar vm_to_core (Tfunction Tnil tvoid cc_default)) nil)
        (Ssequence
          (Scall None
            (Evar exit_populate_fault (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar get_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tuint Tnil)))
                                         tulong cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 44) tuint) :: nil))
              (Sset _ec (Etempvar _t'3 tulong)))
            (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                           (Econst_long (Int64.repr 2) tulong) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar vm_exit_dispatcher (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)) tuint
                                                cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  (Sset _ret (Etempvar _t'4 tuint)))
                (Sifthenelse (Ebinop Oeq (Etempvar _ret tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar core_to_vm (Tfunction Tnil tvoid cc_default)) nil)
                  (Ssequence
                    (Scall None
                      (Evar save_vm (Tfunction Tnil tvoid cc_default)) nil)
                    (Ssequence
                      (Scall None
                        (Evar restore_host (Tfunction Tnil tvoid cc_default))
                        nil)
                      (Scall None
                        (Evar core_to_host (Tfunction Tnil tvoid cc_default))
                        nil)))))
              (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                             (Econst_int (Int.repr 24) tuint) tint)
                (Ssequence
                  (Scall None (Evar save_vm (Tfunction Tnil tvoid cc_default))
                    nil)
                  (Ssequence
                    (Scall None
                      (Evar restore_host (Tfunction Tnil tvoid cc_default))
                      nil)
                    (Scall None
                      (Evar core_to_host (Tfunction Tnil tvoid cc_default))
                      nil)))
                (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                  nil)))))))).

Definition f_vm_exit_handler_raw := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_ec, tulong) :: (_vmid, tuint) :: (_vcpuid, tuint) ::
               (_ret, tuint) :: (_t'4, tuint) :: (_t'3, tulong) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := vm_exit_handler_raw_body
|}.
```
