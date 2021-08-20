# MmioRawCode

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
Definition _base := 4%positive.
Definition _cb_offset := 5%positive.
Definition _cbndx := 6%positive.
Definition _cnt := 7%positive.
Definition _count := 8%positive.
Definition _cur_ticket := 9%positive.
Definition _cur_vcpuid := 10%positive.
Definition _cur_vmid := 11%positive.
Definition _data := 12%positive.
Definition _end := 13%positive.
Definition _esr := 14%positive.
Definition _fault_ipa := 15%positive.
Definition _get_now := 16%positive.
Definition _gfn := 17%positive.
Definition _gpa := 18%positive.
Definition _hsr := 19%positive.
Definition _i := 20%positive.
Definition _inbuf := 21%positive.
Definition _inc_exe := 22%positive.
Definition _incr_now := 23%positive.
Definition _incr_ticket := 24%positive.
Definition _index := 25%positive.
Definition _inowner := 26%positive.
Definition _inpfn := 27%positive.
Definition _iova := 28%positive.
Definition _is_write := 29%positive.
Definition _kvm := 30%positive.
Definition _len := 31%positive.
Definition _level := 32%positive.
Definition _lk := 33%positive.
Definition _load_addr := 34%positive.
Definition _load_idx := 35%positive.
Definition _load_info_cnt := 36%positive.
Definition _log_hold := 37%positive.
Definition _log_incr := 38%positive.
Definition _main := 39%positive.
Definition _map := 40%positive.
Definition _mapped := 41%positive.
Definition _my_ticket := 42%positive.
Definition _n := 43%positive.
Definition _next := 44%positive.
Definition _num := 45%positive.
Definition _num_context_banks := 46%positive.
Definition _offset := 47%positive.
Definition _outbuf := 48%positive.
Definition _outowner := 49%positive.
Definition _outpfn := 50%positive.
Definition _owner := 51%positive.
Definition _pa := 52%positive.
Definition _paddr := 53%positive.
Definition _page_count := 54%positive.
Definition _pass_hlock := 55%positive.
Definition _pass_lock := 56%positive.
Definition _pass_qlock := 57%positive.
Definition _perm := 58%positive.
Definition _pfn := 59%positive.
Definition _pgd := 60%positive.
Definition _pgd_idx := 61%positive.
Definition _pgd_pa := 62%positive.
Definition _pgnum := 63%positive.
Definition _pmd := 64%positive.
Definition _pmd_idx := 65%positive.
Definition _pmd_pa := 66%positive.
Definition _power := 67%positive.
Definition _prot := 68%positive.
Definition _pte := 69%positive.
Definition _pte_idx := 70%positive.
Definition _pte_pa := 71%positive.
Definition _remap := 72%positive.
Definition _remap_addr := 73%positive.
Definition _res := 74%positive.
Definition _ret := 75%positive.
Definition _rt := 76%positive.
Definition _size := 77%positive.
Definition _smmu_enable := 78%positive.
Definition _smmu_index := 79%positive.
Definition _start := 80%positive.
Definition _state := 81%positive.
Definition _t_vmid := 82%positive.
Definition _target := 83%positive.
Definition _target_addr := 84%positive.
Definition _target_vmid := 85%positive.
Definition _total_smmu := 86%positive.
Definition _ttbr := 87%positive.
Definition _ttbr_pa := 88%positive.
Definition _type := 89%positive.
Definition _val := 90%positive.
Definition _valid := 91%positive.
Definition _vcpu := 92%positive.
Definition _vcpu_state := 93%positive.
Definition _vcpuid := 94%positive.
Definition _vm_state := 95%positive.
Definition _vmid := 96%positive.
Definition _wait_hlock := 97%positive.
Definition _wait_lock := 98%positive.
Definition _wait_qlock := 99%positive.
Definition _write_val := 100%positive.
Definition _t'1 := 101%positive.
Definition _t'2 := 102%positive.
Definition _t'3 := 103%positive.

Definition host_get_mmio_data_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
      (Sset _vcpuid (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar host_dabt_get_rd (Tfunction (Tcons tuint Tnil) tuint
                                    cc_default))
          ((Etempvar _hsr tuint) :: nil))
        (Sset _rt (Etempvar _t'2 tuint)))
      (Ssequence
        (Scall (Some _t'3)
          (Evar get_shadow_ctxt (Tfunction
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tuint Tnil))) tulong
                                   cc_default))
          ((Econst_int (Int.repr 0) tuint) :: (Etempvar _vcpuid tuint) ::
           (Etempvar _rt tuint) :: nil))
        (Sreturn (Some (Etempvar _t'3 tulong)))))).

Definition f_host_get_mmio_data := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_vcpuid, tuint) :: (_t'3, tulong) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := host_get_mmio_data_body
|}.

Definition smmu_init_pte_body :=
  (Sreturn (Some (Ebinop Oor (Etempvar _addr tulong)
                   (Ebinop Oor (Etempvar _prot tulong)
                     (Econst_long (Int64.repr 65536) tulong) tulong) tulong))).

Definition f_smmu_init_pte := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_prot, tulong) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := smmu_init_pte_body
|}.

Definition smmu_get_cbndx_body :=
  (Ssequence
    (Sset _offset
      (Ebinop Osub (Etempvar _offset tulong)
        (Econst_int (Int.repr 32768) tuint) tulong))
    (Ssequence
      (Sset _cbndx
        (Ecast
          (Ebinop Oshr (Etempvar _offset tulong)
            (Econst_int (Int.repr 12) tuint) tulong) tuint))
      (Sreturn (Some (Etempvar _cbndx tuint))))).

Definition f_smmu_get_cbndx := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_offset, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_cbndx, tuint) :: nil);
  fn_body := smmu_get_cbndx_body
|}.
```
