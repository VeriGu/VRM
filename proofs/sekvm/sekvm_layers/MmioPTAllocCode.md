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
Definition _arg := 2%positive.
Definition _base := 3%positive.
Definition _cb_offset := 4%positive.
Definition _cbndx := 5%positive.
Definition _cnt := 6%positive.
Definition _count := 7%positive.
Definition _cur_ticket := 8%positive.
Definition _cur_vcpuid := 9%positive.
Definition _cur_vmid := 10%positive.
Definition _data := 11%positive.
Definition _end := 12%positive.
Definition _esr := 13%positive.
Definition _fault_ipa := 14%positive.
Definition _get_now := 15%positive.
Definition _gfn := 16%positive.
Definition _gpa := 17%positive.
Definition _hsr := 18%positive.
Definition _i := 19%positive.
Definition _inbuf := 20%positive.
Definition _inc_exe := 21%positive.
Definition _incr_now := 22%positive.
Definition _incr_ticket := 23%positive.
Definition _index := 24%positive.
Definition _inowner := 25%positive.
Definition _inpfn := 26%positive.
Definition _iova := 27%positive.
Definition _is_write := 28%positive.
Definition _kvm := 29%positive.
Definition _len := 30%positive.
Definition _level := 31%positive.
Definition _lk := 32%positive.
Definition _load_addr := 33%positive.
Definition _load_idx := 34%positive.
Definition _load_info_cnt := 35%positive.
Definition _log_hold := 36%positive.
Definition _log_incr := 37%positive.
Definition _main := 38%positive.
Definition _map := 39%positive.
Definition _mapped := 40%positive.
Definition _my_ticket := 41%positive.
Definition _n := 42%positive.
Definition _next := 43%positive.
Definition _num := 44%positive.
Definition _num_context_banks := 45%positive.
Definition _offset := 46%positive.
Definition _outbuf := 47%positive.
Definition _outowner := 48%positive.
Definition _outpfn := 49%positive.
Definition _owner := 50%positive.
Definition _pa := 51%positive.
Definition _paddr := 52%positive.
Definition _page_count := 53%positive.
Definition _pass_hlock := 54%positive.
Definition _pass_lock := 55%positive.
Definition _pass_qlock := 56%positive.
Definition _perm := 57%positive.
Definition _pfn := 58%positive.
Definition _pgnum := 59%positive.
Definition _power := 60%positive.
Definition _prot := 61%positive.
Definition _pte := 62%positive.
Definition _pte_pa := 63%positive.
Definition _remap := 64%positive.
Definition _remap_addr := 65%positive.
Definition _res := 66%positive.
Definition _ret := 67%positive.
Definition _rt := 68%positive.
Definition _size := 69%positive.
Definition _smmu_enable := 70%positive.
Definition _smmu_index := 71%positive.
Definition _start := 72%positive.
Definition _state := 73%positive.
Definition _t_vmid := 74%positive.
Definition _target := 75%positive.
Definition _target_addr := 76%positive.
Definition _target_vmid := 77%positive.
Definition _total_smmu := 78%positive.
Definition _type := 79%positive.
Definition _val := 80%positive.
Definition _valid := 81%positive.
Definition _vcpu := 82%positive.
Definition _vcpu_state := 83%positive.
Definition _vcpuid := 84%positive.
Definition _vm_state := 85%positive.
Definition _vmid := 86%positive.
Definition _wait_hlock := 87%positive.
Definition _wait_lock := 88%positive.
Definition _wait_qlock := 89%positive.
Definition _write_val := 90%positive.
Definition _t'1 := 91%positive.
Definition _t'2 := 92%positive.

Definition alloc_smmu_pgd_page_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_smmu_pgd_next (Tfunction Tnil tulong cc_default)) nil)
      (Sset _next (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _end (Econst_long (Int64.repr 2162688) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _next tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong)
                       (Etempvar _end tulong) tint)
          (Scall None
            (Evar set_smmu_pgd_next (Tfunction (Tcons tulong Tnil) tvoid
                                       cc_default))
            ((Ebinop Oadd (Etempvar _next tulong)
               (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _next tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_alloc_smmu_pgd_page := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_next, tulong) :: (_end, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := alloc_smmu_pgd_page_body
|}.

Definition alloc_smmu_pmd_page_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_smmu_pmd_next (Tfunction Tnil tulong cc_default)) nil)
      (Sset _next (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _end (Econst_long (Int64.repr 3211264) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _next tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong)
                       (Etempvar _end tulong) tint)
          (Scall None
            (Evar set_smmu_pmd_next (Tfunction (Tcons tulong Tnil) tvoid
                                       cc_default))
            ((Ebinop Oadd (Etempvar _next tulong)
               (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _next tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_alloc_smmu_pmd_page := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_next, tulong) :: (_end, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := alloc_smmu_pmd_page_body
|}.
```
