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
Definition _pud := 72%positive.
Definition _pud_idx := 73%positive.
Definition _pud_pa := 74%positive.
Definition _reg := 75%positive.
Definition _remap := 76%positive.
Definition _remap_addr := 77%positive.
Definition _res := 78%positive.
Definition _ret := 79%positive.
Definition _rt := 80%positive.
Definition _size := 81%positive.
Definition _smmu_enable := 82%positive.
Definition _smmu_index := 83%positive.
Definition _start := 84%positive.
Definition _state := 85%positive.
Definition _t_vmid := 86%positive.
Definition _target := 87%positive.
Definition _target_addr := 88%positive.
Definition _target_vmid := 89%positive.
Definition _total_smmu := 90%positive.
Definition _ttbr := 91%positive.
Definition _ttbr_pa := 92%positive.
Definition _type := 93%positive.
Definition _val := 94%positive.
Definition _valid := 95%positive.
Definition _vcpu := 96%positive.
Definition _vcpu_state := 97%positive.
Definition _vcpuid := 98%positive.
Definition _vm_state := 99%positive.
Definition _vmid := 100%positive.
Definition _vttbr := 101%positive.
Definition _vttbr_pa := 102%positive.
Definition _wait_hlock := 103%positive.
Definition _wait_lock := 104%positive.
Definition _wait_qlock := 105%positive.
Definition _write_val := 106%positive.
Definition _t'1 := 107%positive.
Definition _t'2 := 108%positive.
Definition _t'3 := 109%positive.
Definition _t'4 := 110%positive.

Definition walk_pgd_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sset _vttbr_pa
        (Ebinop Oand
          (Ebinop Oand (Etempvar _vttbr tulong)
            (Econst_long (Int64.repr 281474976710655) tulong) tulong)
          (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
      (Ssequence
        (Sset _pgd_idx
          (Ebinop Oand
            (Ebinop Oshr (Etempvar _addr tulong)
              (Econst_long (Int64.repr 39) tulong) tulong)
            (Econst_int (Int.repr 511) tint) tulong))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar pt_load (Tfunction (Tcons tuint (Tcons tulong Tnil))
                               tulong cc_default))
              ((Etempvar _vmid tuint) ::
               (Ebinop Oor (Etempvar _vttbr_pa tulong)
                 (Ebinop Omul (Etempvar _pgd_idx tulong)
                   (Econst_long (Int64.repr 8) tulong) tulong) tulong) :: nil))
            (Sset _pgd (Etempvar _t'1 tulong)))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _pgd tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Sset _t'3
                  (Ecast
                    (Ebinop Oeq (Etempvar _alloc tuint)
                      (Econst_int (Int.repr 1) tuint) tint) tbool))
                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'3 tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar alloc_pgd_page (Tfunction (Tcons tuint Tnil)
                                              tulong cc_default))
                      ((Etempvar _vmid tuint) :: nil))
                    (Sset _pgd_pa (Etempvar _t'2 tulong)))
                  (Ssequence
                    (Sset _pgd
                      (Ebinop Oor (Etempvar _pgd_pa tulong)
                        (Econst_long (Int64.repr 3) tulong) tulong))
                    (Scall None
                      (Evar pt_store (Tfunction
                                        (Tcons tuint
                                          (Tcons tulong (Tcons tulong Tnil)))
                                        tvoid cc_default))
                      ((Etempvar _vmid tuint) ::
                       (Ebinop Oor (Etempvar _vttbr_pa tulong)
                         (Ebinop Omul (Etempvar _pgd_idx tulong)
                           (Econst_long (Int64.repr 8) tulong) tulong) tulong) ::
                       (Etempvar _pgd tulong) :: nil))))
                Sskip))
            (Ssequence
              (Sset _ret (Etempvar _pgd tulong))
              (Ssequence
                (Scall (Some _t'4)
                  (Evar check64 (Tfunction (Tcons tulong Tnil) tulong
                                   cc_default))
                  ((Etempvar _ret tulong) :: nil))
                (Sreturn (Some (Etempvar _t'4 tulong)))))))))).

Definition f_walk_pgd := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vttbr, tulong) :: (_addr, tulong) ::
                (_alloc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vttbr_pa, tulong) :: (_ret, tulong) :: (_pgd_idx, tulong) ::
               (_pgd, tulong) :: (_pgd_pa, tulong) :: (_t'4, tulong) ::
               (_t'3, tint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_pgd_body
|}.

Definition walk_pud_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _pgd tulong)
                     (Econst_long (Int64.repr 0) tulong) tint)
        (Ssequence
          (Sset _pgd_pa
            (Ebinop Oand
              (Ebinop Oand (Etempvar _pgd tulong)
                (Econst_long (Int64.repr 281474976710655) tulong) tulong)
              (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
          (Ssequence
            (Sset _pud_idx
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _addr tulong)
                  (Econst_long (Int64.repr 30) tulong) tulong)
                (Econst_int (Int.repr 511) tint) tulong))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar pt_load (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                   tulong cc_default))
                  ((Etempvar _vmid tuint) ::
                   (Ebinop Oor (Etempvar _pgd_pa tulong)
                     (Ebinop Omul (Etempvar _pud_idx tulong)
                       (Econst_long (Int64.repr 8) tulong) tulong) tulong) ::
                   nil))
                (Sset _pud (Etempvar _t'1 tulong)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _pud tulong)
                                 (Econst_long (Int64.repr 0) tulong) tint)
                    (Sset _t'3
                      (Ecast
                        (Ebinop Oeq (Etempvar _alloc tuint)
                          (Econst_int (Int.repr 1) tuint) tint) tbool))
                    (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar alloc_pud_page (Tfunction (Tcons tuint Tnil)
                                                  tulong cc_default))
                          ((Etempvar _vmid tuint) :: nil))
                        (Sset _pud_pa (Etempvar _t'2 tulong)))
                      (Ssequence
                        (Sset _pud
                          (Ebinop Oor (Etempvar _pud_pa tulong)
                            (Econst_long (Int64.repr 3) tulong) tulong))
                        (Scall None
                          (Evar pt_store (Tfunction
                                            (Tcons tuint
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Ebinop Oor (Etempvar _pgd_pa tulong)
                             (Ebinop Omul (Etempvar _pud_idx tulong)
                               (Econst_long (Int64.repr 8) tulong) tulong)
                             tulong) :: (Etempvar _pud tulong) :: nil))))
                    Sskip))
                (Sset _ret (Etempvar _pud tulong))))))
        Sskip)
      (Ssequence
        (Scall (Some _t'4)
          (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _ret tulong) :: nil))
        (Sreturn (Some (Etempvar _t'4 tulong)))))).

Definition f_walk_pud := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pgd, tulong) :: (_addr, tulong) ::
                (_alloc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pgd_pa, tulong) :: (_ret, tulong) :: (_pud_idx, tulong) ::
               (_pud, tulong) :: (_pud_pa, tulong) :: (_t'4, tulong) ::
               (_t'3, tint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_pud_body
|}.

Definition walk_pmd_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _pud tulong)
                     (Econst_long (Int64.repr 0) tulong) tint)
        (Ssequence
          (Sset _pud_pa
            (Ebinop Oand
              (Ebinop Oand (Etempvar _pud tulong)
                (Econst_long (Int64.repr 281474976710655) tulong) tulong)
              (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
          (Ssequence
            (Sset _pmd_idx
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _addr tulong)
                  (Econst_long (Int64.repr 21) tulong) tulong)
                (Econst_int (Int.repr 511) tint) tulong))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar pt_load (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                   tulong cc_default))
                  ((Etempvar _vmid tuint) ::
                   (Ebinop Oor (Etempvar _pud_pa tulong)
                     (Ebinop Omul (Etempvar _pmd_idx tulong)
                       (Econst_int (Int.repr 8) tint) tulong) tulong) :: nil))
                (Sset _pmd (Etempvar _t'1 tulong)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _pmd tulong)
                                 (Econst_long (Int64.repr 0) tulong) tint)
                    (Sset _t'3
                      (Ecast
                        (Ebinop Oeq (Etempvar _alloc tuint)
                          (Econst_int (Int.repr 1) tuint) tint) tbool))
                    (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar alloc_pmd_page (Tfunction (Tcons tuint Tnil)
                                                  tulong cc_default))
                          ((Etempvar _vmid tuint) :: nil))
                        (Sset _pmd_pa (Etempvar _t'2 tulong)))
                      (Ssequence
                        (Sset _pmd
                          (Ebinop Oor (Etempvar _pmd_pa tulong)
                            (Econst_long (Int64.repr 3) tulong) tulong))
                        (Scall None
                          (Evar pt_store (Tfunction
                                            (Tcons tuint
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Ebinop Oor (Etempvar _pud_pa tulong)
                             (Ebinop Omul (Etempvar _pmd_idx tulong)
                               (Econst_long (Int64.repr 8) tulong) tulong)
                             tulong) :: (Etempvar _pmd tulong) :: nil))))
                    Sskip))
                (Sset _ret (Etempvar _pmd tulong))))))
        Sskip)
      (Ssequence
        (Scall (Some _t'4)
          (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _ret tulong) :: nil))
        (Sreturn (Some (Etempvar _t'4 tulong)))))).

Definition f_walk_pmd := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pud, tulong) :: (_addr, tulong) ::
                (_alloc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pud_pa, tulong) :: (_ret, tulong) :: (_pmd_idx, tulong) ::
               (_pmd, tulong) :: (_pmd_pa, tulong) :: (_t'4, tulong) ::
               (_t'3, tint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_pmd_body
|}.

Definition walk_pte_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _pmd tulong)
                     (Econst_long (Int64.repr 0) tulong) tint)
        (Ssequence
          (Sset _pmd_pa
            (Ebinop Oand
              (Ebinop Oand (Etempvar _pmd tulong)
                (Econst_long (Int64.repr 281474976710655) tulong) tulong)
              (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
          (Ssequence
            (Sset _pte_idx
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _addr tulong)
                  (Econst_long (Int64.repr 12) tulong) tulong)
                (Econst_int (Int.repr 511) tint) tulong))
            (Ssequence
              (Scall (Some _t'1)
                (Evar pt_load (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                 tulong cc_default))
                ((Etempvar _vmid tuint) ::
                 (Ebinop Oor (Etempvar _pmd_pa tulong)
                   (Ebinop Omul (Etempvar _pte_idx tulong)
                     (Econst_long (Int64.repr 8) tulong) tulong) tulong) ::
                 nil))
              (Sset _ret (Etempvar _t'1 tulong)))))
        Sskip)
      (Ssequence
        (Scall (Some _t'2)
          (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _ret tulong) :: nil))
        (Sreturn (Some (Etempvar _t'2 tulong)))))).

Definition f_walk_pte := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pmd, tulong) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pmd_pa, tulong) :: (_ret, tulong) :: (_pte_idx, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := walk_pte_body
|}.

Definition set_pmd_body :=
  (Ssequence
    (Sset _pud_pa
      (Ebinop Oand
        (Ebinop Oand (Etempvar _pud tulong)
          (Econst_long (Int64.repr 281474976710655) tulong) tulong)
        (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
    (Ssequence
      (Sset _pmd_idx
        (Ebinop Oand
          (Ebinop Oshr (Etempvar _addr tulong)
            (Econst_long (Int64.repr 21) tulong) tulong)
          (Econst_int (Int.repr 511) tint) tulong))
      (Scall None
        (Evar pt_store (Tfunction
                          (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))
                          tvoid cc_default))
        ((Etempvar _vmid tuint) ::
         (Ebinop Oor (Etempvar _pud_pa tulong)
           (Ebinop Omul (Etempvar _pmd_idx tulong)
             (Econst_long (Int64.repr 8) tulong) tulong) tulong) ::
         (Etempvar _pmd tulong) :: nil)))).

Definition f_set_pmd := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pud, tulong) :: (_addr, tulong) ::
                (_pmd, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pud_pa, tulong) :: (_pmd_idx, tulong) :: nil);
  fn_body := set_pmd_body
|}.

Definition set_pte_body :=
  (Ssequence
    (Sset _pmd_pa
      (Ebinop Oand
        (Ebinop Oand (Etempvar _pmd tulong)
          (Econst_long (Int64.repr 281474976710655) tulong) tulong)
        (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
    (Ssequence
      (Sset _pte_idx
        (Ebinop Oand
          (Ebinop Oshr (Etempvar _addr tulong)
            (Econst_long (Int64.repr 12) tulong) tulong)
          (Econst_int (Int.repr 511) tint) tulong))
      (Scall None
        (Evar pt_store (Tfunction
                          (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))
                          tvoid cc_default))
        ((Etempvar _vmid tuint) ::
         (Ebinop Oor (Etempvar _pmd_pa tulong)
           (Ebinop Omul (Etempvar _pte_idx tulong)
             (Econst_long (Int64.repr 8) tulong) tulong) tulong) ::
         (Etempvar _pte tulong) :: nil)))).

Definition f_set_pte := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pmd, tulong) :: (_addr, tulong) ::
                (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pmd_pa, tulong) :: (_pte_idx, tulong) :: nil);
  fn_body := set_pte_body
|}.
```
