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
Definition _t'3 := 104%positive.
Definition _t'4 := 105%positive.
Definition _t'5 := 106%positive.

Definition clear_smmu_pt_body :=
  (Scall None
    (Evar smmu_pt_clear (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                           cc_default))
    ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil)).

Definition f_clear_smmu_pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := clear_smmu_pt_body
|}.

Definition walk_smmu_pt_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_smmu_cfg_hw_ttbr (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                      tulong cc_default))
        ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
      (Sset _ttbr (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar walk_smmu_pgd (Tfunction
                                 (Tcons tulong
                                   (Tcons tulong (Tcons tuint Tnil))) tulong
                                 cc_default))
          ((Etempvar _ttbr tulong) :: (Etempvar _addr tulong) ::
           (Econst_int (Int.repr 0) tuint) :: nil))
        (Sset _pgd (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar walk_smmu_pmd (Tfunction
                                   (Tcons tulong
                                     (Tcons tulong (Tcons tuint Tnil))) tulong
                                   cc_default))
            ((Etempvar _pgd tulong) :: (Etempvar _addr tulong) ::
             (Econst_int (Int.repr 0) tuint) :: nil))
          (Sset _pmd (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar walk_smmu_pte (Tfunction
                                     (Tcons tulong (Tcons tulong Tnil)) tulong
                                     cc_default))
              ((Etempvar _pmd tulong) :: (Etempvar _addr tulong) :: nil))
            (Sset _ret (Etempvar _t'4 tulong)))
          (Ssequence
            (Scall (Some _t'5)
              (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
              ((Etempvar _ret tulong) :: nil))
            (Sreturn (Some (Etempvar _t'5 tulong)))))))).

Definition f_walk_smmu_pt := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ttbr, tulong) :: (_pgd, tulong) :: (_pmd, tulong) ::
               (_ret, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_smmu_pt_body
|}.

Definition set_smmu_pt_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_smmu_cfg_hw_ttbr (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                      tulong cc_default))
        ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
      (Sset _ttbr (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar walk_smmu_pgd (Tfunction
                                 (Tcons tulong
                                   (Tcons tulong (Tcons tuint Tnil))) tulong
                                 cc_default))
          ((Etempvar _ttbr tulong) :: (Etempvar _addr tulong) ::
           (Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _pgd (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar walk_smmu_pmd (Tfunction
                                   (Tcons tulong
                                     (Tcons tulong (Tcons tuint Tnil))) tulong
                                   cc_default))
            ((Etempvar _pgd tulong) :: (Etempvar _addr tulong) ::
             (Econst_int (Int.repr 1) tuint) :: nil))
          (Sset _pmd (Etempvar _t'3 tulong)))
        (Scall None
          (Evar set_smmu_pte (Tfunction
                                (Tcons tulong
                                  (Tcons tulong (Tcons tulong Tnil))) tvoid
                                cc_default))
          ((Etempvar _pmd tulong) :: (Etempvar _addr tulong) ::
           (Etempvar _pte tulong) :: nil))))).

Definition f_set_smmu_pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: (_addr, tulong) ::
                (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ttbr, tulong) :: (_pgd, tulong) :: (_pmd, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := set_smmu_pt_body
|}.

Definition dev_load_ref_body :=
  (Scall None
    (Evar dev_load_raw (Tfunction
                          (Tcons tulong
                            (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                          tvoid cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) ::
     (Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil)).

Definition f_dev_load_ref := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: (_cbndx, tuint) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := dev_load_ref_body
|}.

Definition dev_store_ref_body :=
  (Scall None
    (Evar dev_store_raw (Tfunction
                           (Tcons tulong
                             (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                           tvoid cc_default))
    ((Etempvar _gfn tulong) :: (Etempvar _reg tuint) ::
     (Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil)).

Definition f_dev_store_ref := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gfn, tulong) :: (_reg, tuint) :: (_cbndx, tuint) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := dev_store_ref_body
|}.
```
