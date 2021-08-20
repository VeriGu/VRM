# PTAllocCode

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
Definition _pud := 72%positive.
Definition _reg := 73%positive.
Definition _remap := 74%positive.
Definition _remap_addr := 75%positive.
Definition _res := 76%positive.
Definition _ret := 77%positive.
Definition _rt := 78%positive.
Definition _size := 79%positive.
Definition _smmu_enable := 80%positive.
Definition _smmu_index := 81%positive.
Definition _start := 82%positive.
Definition _state := 83%positive.
Definition _t_vmid := 84%positive.
Definition _target := 85%positive.
Definition _target_addr := 86%positive.
Definition _target_vmid := 87%positive.
Definition _total_smmu := 88%positive.
Definition _ttbr := 89%positive.
Definition _ttbr_pa := 90%positive.
Definition _type := 91%positive.
Definition _val := 92%positive.
Definition _valid := 93%positive.
Definition _vcpu := 94%positive.
Definition _vcpu_state := 95%positive.
Definition _vcpuid := 96%positive.
Definition _vm_state := 97%positive.
Definition _vmid := 98%positive.
Definition _vttbr := 99%positive.
Definition _wait_hlock := 100%positive.
Definition _wait_lock := 101%positive.
Definition _wait_qlock := 102%positive.
Definition _write_val := 103%positive.
Definition _t'1 := 104%positive.
Definition _t'2 := 105%positive.

Definition alloc_pgd_page_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_pgd_next (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Etempvar _vmid tuint) :: nil))
      (Sset _next (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _end
        (Ebinop Oadd
          (Ebinop Oadd (Econst_long (Int64.repr 65536) tulong)
            (Ebinop Omul (Econst_long (Int64.repr 33554432) tulong)
              (Etempvar _vmid tuint) tulong) tulong)
          (Econst_long (Int64.repr 1052672) tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _next tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong)
                       (Etempvar _end tulong) tint)
          (Scall None
            (Evar set_pgd_next (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Etempvar _vmid tuint) ::
             (Ebinop Oadd (Etempvar _next tulong)
               (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _next tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_alloc_pgd_page := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, tulong) :: (_end, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := alloc_pgd_page_body
|}.

Definition alloc_pud_page_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_pud_next (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Etempvar _vmid tuint) :: nil))
      (Sset _next (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _end
        (Ebinop Oadd
          (Ebinop Oadd (Econst_long (Int64.repr 65536) tulong)
            (Ebinop Omul (Econst_long (Int64.repr 33554432) tulong)
              (Etempvar _vmid tuint) tulong) tulong)
          (Econst_long (Int64.repr 9441280) tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _next tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong)
                       (Etempvar _end tulong) tint)
          (Scall None
            (Evar set_pud_next (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Etempvar _vmid tuint) ::
             (Ebinop Oadd (Etempvar _next tulong)
               (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _next tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_alloc_pud_page := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, tulong) :: (_end, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := alloc_pud_page_body
|}.

Definition alloc_pmd_page_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_pmd_next (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Etempvar _vmid tuint) :: nil))
      (Sset _next (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _end
        (Ebinop Oadd (Econst_long (Int64.repr 65536) tulong)
          (Ebinop Omul (Econst_long (Int64.repr 33554432) tulong)
            (Ebinop Oadd (Etempvar _vmid tuint) (Econst_int (Int.repr 1) tint)
              tuint) tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _next tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong)
                       (Etempvar _end tulong) tint)
          (Scall None
            (Evar set_pmd_next (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Etempvar _vmid tuint) ::
             (Ebinop Oadd (Etempvar _next tulong)
               (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _next tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_alloc_pmd_page := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, tulong) :: (_end, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := alloc_pmd_page_body
|}.
```
