# NPTOpsCode

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
Definition _reg := 72%positive.
Definition _remap := 73%positive.
Definition _remap_addr := 74%positive.
Definition _res := 75%positive.
Definition _ret := 76%positive.
Definition _rt := 77%positive.
Definition _size := 78%positive.
Definition _smmu_enable := 79%positive.
Definition _smmu_index := 80%positive.
Definition _start := 81%positive.
Definition _state := 82%positive.
Definition _t_vmid := 83%positive.
Definition _target := 84%positive.
Definition _target_addr := 85%positive.
Definition _target_vmid := 86%positive.
Definition _total_smmu := 87%positive.
Definition _ttbr := 88%positive.
Definition _ttbr_pa := 89%positive.
Definition _type := 90%positive.
Definition _val := 91%positive.
Definition _valid := 92%positive.
Definition _vcpu := 93%positive.
Definition _vcpu_state := 94%positive.
Definition _vcpuid := 95%positive.
Definition _vm_state := 96%positive.
Definition _vmid := 97%positive.
Definition _wait_hlock := 98%positive.
Definition _wait_lock := 99%positive.
Definition _wait_qlock := 100%positive.
Definition _write_val := 101%positive.
Definition _t'1 := 102%positive.
Definition _t'2 := 103%positive.

Definition get_level_s2pt_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_pt (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_npt_level (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                 tuint cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
        (Sset _ret (Etempvar _t'1 tuint)))
      (Ssequence
        (Scall None
          (Evar release_lock_pt (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
            ((Etempvar _ret tuint) :: nil))
          (Sreturn (Some (Etempvar _t'2 tuint))))))).

Definition f_get_level_s2pt := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := get_level_s2pt_body
|}.

Definition walk_s2pt_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_pt (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar walk_npt (Tfunction (Tcons tuint (Tcons tulong Tnil)) tulong
                            cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
        (Sset _ret (Etempvar _t'1 tulong)))
      (Ssequence
        (Scall None
          (Evar release_lock_pt (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
            ((Etempvar _ret tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))))).

Definition f_walk_s2pt := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_s2pt_body
|}.

Definition map_s2pt_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_pt (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar set_npt (Tfunction
                         (Tcons tuint
                           (Tcons tulong (Tcons tuint (Tcons tulong Tnil))))
                         tvoid cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
         (Etempvar _level tuint) :: (Etempvar _pte tulong) :: nil))
      (Scall None
        (Evar release_lock_pt (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Etempvar _vmid tuint) :: nil)))).

Definition f_map_s2pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: (_level, tuint) ::
                (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := map_s2pt_body
|}.

Definition clear_pfn_host_body :=
(Ssequence
  (Scall None
    (Evar acquire_lock_pt (Tfunction (Tcons tuint Tnil) tvoid cc_default))
    ((Econst_int (Int.repr 0) tuint) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_npt_level (Tfunction (Tcons tuint (Tcons tulong Tnil))
                               tuint cc_default))
        ((Econst_int (Int.repr 0) tuint) ::
         (Ebinop Omul (Etempvar _pfn tulong)
           (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
      (Sset _level (Etempvar _t'1 tuint)))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _level tuint)
                     (Econst_int (Int.repr 0) tuint) tint)
        (Scall None
          (Evar set_npt (Tfunction
                           (Tcons tuint
                             (Tcons tulong (Tcons tuint (Tcons tulong Tnil))))
                           tvoid cc_default))
          ((Econst_int (Int.repr 0) tuint) ::
           (Ebinop Omul (Etempvar _pfn tulong)
             (Econst_long (Int64.repr 4096) tulong) tulong) ::
           (Econst_int (Int.repr 3) tuint) ::
           (Econst_long (Int64.repr 144115188075855872) tulong) :: nil))
        Sskip)
      (Scall None
        (Evar release_lock_pt (Tfunction (Tcons tuint Tnil) tvoid
                                 cc_default))
        ((Econst_int (Int.repr 0) tuint) :: nil))))).

Definition f_clear_pfn_host := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_level, tuint) :: (_t'1, tuint) :: nil);
  fn_body := clear_pfn_host_body
|}.
```
