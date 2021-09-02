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
Definition _p_index := 52%positive.
Definition _pa := 53%positive.
Definition _paddr := 54%positive.
Definition _page_count := 55%positive.
Definition _pass_hlock := 56%positive.
Definition _pass_lock := 57%positive.
Definition _pass_qlock := 58%positive.
Definition _perm := 59%positive.
Definition _pfn := 60%positive.
Definition _pgd := 61%positive.
Definition _pgd_idx := 62%positive.
Definition _pgd_pa := 63%positive.
Definition _pgnum := 64%positive.
Definition _pmd := 65%positive.
Definition _pmd_idx := 66%positive.
Definition _pmd_pa := 67%positive.
Definition _power := 68%positive.
Definition _prot := 69%positive.
Definition _pte := 70%positive.
Definition _pte_idx := 71%positive.
Definition _pte_pa := 72%positive.
Definition _pud := 73%positive.
Definition _pud_idx := 74%positive.
Definition _pud_pa := 75%positive.
Definition _r_index := 76%positive.
Definition _reg := 77%positive.
Definition _remap := 78%positive.
Definition _remap_addr := 79%positive.
Definition _res := 80%positive.
Definition _ret := 81%positive.
Definition _rt := 82%positive.
Definition _size := 83%positive.
Definition _smmu_enable := 84%positive.
Definition _smmu_index := 85%positive.
Definition _start := 86%positive.
Definition _state := 87%positive.
Definition _t_vmid := 88%positive.
Definition _target := 89%positive.
Definition _target_addr := 90%positive.
Definition _target_vmid := 91%positive.
Definition _total_smmu := 92%positive.
Definition _ttbr := 93%positive.
Definition _ttbr_pa := 94%positive.
Definition _type := 95%positive.
Definition _val := 96%positive.
Definition _valid := 97%positive.
Definition _vcpu := 98%positive.
Definition _vcpu_state := 99%positive.
Definition _vcpuid := 100%positive.
Definition _vm_state := 101%positive.
Definition _vmid := 102%positive.
Definition _vttbr := 103%positive.
Definition _vttbr_pa := 104%positive.
Definition _wait_hlock := 105%positive.
Definition _wait_lock := 106%positive.
Definition _wait_qlock := 107%positive.
Definition _write_val := 108%positive.
Definition _t'1 := 109%positive.
Definition _t'2 := 110%positive.
Definition _t'3 := 111%positive.

Definition get_s2_page_index_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar mem_region_search (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
        ((Etempvar _addr tulong) :: nil))
      (Sset _r_index (Etempvar _t'1 tuint)))
    (Ssequence
      (Sset _ret (Econst_long (Int64.repr (-1)) tulong))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _r_index tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_mem_region_index (Tfunction (Tcons tuint Tnil)
                                              tulong cc_default))
                ((Etempvar _r_index tuint) :: nil))
              (Sset _p_index (Etempvar _t'2 tulong)))
            (Sifthenelse (Ebinop One (Etempvar _p_index tulong)
                           (Econst_long (Int64.repr (-1)) tulong) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_mem_region_base (Tfunction (Tcons tuint Tnil)
                                                 tulong cc_default))
                    ((Etempvar _r_index tuint) :: nil))
                  (Sset _base (Etempvar _t'3 tulong)))
                (Sset _ret
                  (Ebinop Oadd (Etempvar _p_index tulong)
                    (Ebinop Odiv
                      (Ebinop Osub (Etempvar _addr tulong)
                        (Etempvar _base tulong) tulong)
                      (Econst_long (Int64.repr 4096) tulong) tulong) tulong)))
              Sskip))
          Sskip)
        (Sreturn (Some (Etempvar _ret tulong)))))).

Definition f_get_s2_page_index := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_p_index, tulong) :: (_base, tulong) ::
               (_r_index, tuint) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := get_s2_page_index_body
|}.
```
