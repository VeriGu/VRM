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
Definition _cbndx := 4%positive.
Definition _cnt := 5%positive.
Definition _count := 6%positive.
Definition _cur_ticket := 7%positive.
Definition _cur_vcpuid := 8%positive.
Definition _cur_vmid := 9%positive.
Definition _end := 10%positive.
Definition _esr := 11%positive.
Definition _get_now := 12%positive.
Definition _gfn := 13%positive.
Definition _gpa := 14%positive.
Definition _i := 15%positive.
Definition _inbuf := 16%positive.
Definition _inc_exe := 17%positive.
Definition _incr_now := 18%positive.
Definition _incr_ticket := 19%positive.
Definition _index := 20%positive.
Definition _inowner := 21%positive.
Definition _inpfn := 22%positive.
Definition _iova := 23%positive.
Definition _kvm := 24%positive.
Definition _level := 25%positive.
Definition _lk := 26%positive.
Definition _load_addr := 27%positive.
Definition _load_idx := 28%positive.
Definition _load_info_cnt := 29%positive.
Definition _log_hold := 30%positive.
Definition _log_incr := 31%positive.
Definition _main := 32%positive.
Definition _map := 33%positive.
Definition _mapped := 34%positive.
Definition _my_ticket := 35%positive.
Definition _num := 36%positive.
Definition _outbuf := 37%positive.
Definition _outowner := 38%positive.
Definition _outpfn := 39%positive.
Definition _owner := 40%positive.
Definition _pa := 41%positive.
Definition _paddr := 42%positive.
Definition _page_count := 43%positive.
Definition _pass_hlock := 44%positive.
Definition _pass_lock := 45%positive.
Definition _pass_qlock := 46%positive.
Definition _perm := 47%positive.
Definition _pfn := 48%positive.
Definition _pgnum := 49%positive.
Definition _power := 50%positive.
Definition _prot := 51%positive.
Definition _pte := 52%positive.
Definition _pte_pa := 53%positive.
Definition _remap := 54%positive.
Definition _remap_addr := 55%positive.
Definition _res := 56%positive.
Definition _ret := 57%positive.
Definition _size := 58%positive.
Definition _start := 59%positive.
Definition _state := 60%positive.
Definition _target := 61%positive.
Definition _target_addr := 62%positive.
Definition _valid := 63%positive.
Definition _vcpu := 64%positive.
Definition _vcpu_state := 65%positive.
Definition _vcpuid := 66%positive.
Definition _vm_state := 67%positive.
Definition _vmid := 68%positive.
Definition _wait_hlock := 69%positive.
Definition _wait_lock := 70%positive.
Definition _wait_qlock := 71%positive.
Definition _t'1 := 72%positive.
Definition _t'2 := 73%positive.

Definition clear_vm_range_body :=
  (Swhile
    (Ebinop Ogt (Etempvar _num tulong) (Econst_long (Int64.repr 0) tulong)
      tint)
    (Ssequence
      (Scall None
        (Evar clear_vm_page (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                               cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) :: nil))
      (Ssequence
        (Sset _pfn
          (Ebinop Oadd (Etempvar _pfn tulong)
            (Econst_long (Int64.repr 1) tulong) tulong))
        (Sset _num
          (Ebinop Osub (Etempvar _num tulong)
            (Econst_long (Int64.repr 1) tulong) tulong))))).

Definition f_clear_vm_range := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: (_num, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := clear_vm_range_body
|}.

Definition prot_and_map_vm_s2pt_body :=
  (Ssequence
    (Sset _target
      (Ebinop Oand
        (Ebinop Oand (Etempvar _pte tulong)
          (Econst_long (Int64.repr 281474976710655) tulong) tulong)
        (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
    (Ssequence
      (Sset _pfn
        (Ebinop Odiv (Etempvar _target tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Sset _gfn
          (Ebinop Odiv (Etempvar _addr tulong)
            (Econst_long (Int64.repr 4096) tulong) tulong))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _level tuint)
                         (Econst_int (Int.repr 2) tuint) tint)
            (Ssequence
              (Sset _gfn
                (Ebinop Omul
                  (Ebinop Odiv (Etempvar _gfn tulong)
                    (Econst_long (Int64.repr 512) tulong) tulong)
                  (Econst_long (Int64.repr 512) tulong) tulong))
              (Ssequence
                (Sset _num (Econst_long (Int64.repr 512) tulong))
                (Swhile
                  (Ebinop Ogt (Etempvar _num tulong)
                    (Econst_long (Int64.repr 0) tulong) tint)
                  (Ssequence
                    (Scall None
                      (Evar assign_pfn_to_vm (Tfunction
                                                (Tcons tuint
                                                  (Tcons tulong
                                                    (Tcons tulong Tnil))) tvoid
                                                cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _gfn tulong) ::
                       (Etempvar _pfn tulong) :: nil))
                    (Ssequence
                      (Sset _gfn
                        (Ebinop Oadd (Etempvar _gfn tulong)
                          (Econst_long (Int64.repr 1) tulong) tulong))
                      (Ssequence
                        (Sset _pfn
                          (Ebinop Oadd (Etempvar _pfn tulong)
                            (Econst_long (Int64.repr 1) tulong) tulong))
                        (Sset _num
                          (Ebinop Osub (Etempvar _num tulong)
                            (Econst_long (Int64.repr 1) tulong) tulong))))))))
            (Ssequence
              (Scall None
                (Evar assign_pfn_to_vm (Tfunction
                                          (Tcons tuint
                                            (Tcons tulong (Tcons tulong Tnil)))
                                          tvoid cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _gfn tulong) ::
                 (Etempvar _pfn tulong) :: nil))
              (Sset _level (Econst_int (Int.repr 3) tuint))))
          (Scall None
            (Evar map_pfn_vm (Tfunction
                                (Tcons tuint
                                  (Tcons tulong
                                    (Tcons tulong (Tcons tuint Tnil)))) tvoid
                                cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
             (Etempvar _pte tulong) :: (Etempvar _level tuint) :: nil)))))).

Definition f_prot_and_map_vm_s2pt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: (_pte, tulong) ::
                (_level, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_target, tulong) :: (_pfn, tulong) :: (_gfn, tulong) ::
               (_num, tulong) :: nil);
  fn_body := prot_and_map_vm_s2pt_body
|}.

Definition grant_stage2_sg_gpa_body :=
  (Ssequence
    (Sset _num
      (Ebinop Odiv
        (Ebinop Oadd (Etempvar _size tulong) (Econst_int (Int.repr 4095) tint)
          tulong) (Econst_long (Int64.repr 4096) tulong) tulong))
    (Swhile
      (Ebinop Ogt (Etempvar _num tulong) (Econst_long (Int64.repr 0) tulong)
        tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar walk_s2pt (Tfunction (Tcons tuint (Tcons tulong Tnil))
                               tulong cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
          (Sset _pte (Etempvar _t'1 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar get_level_s2pt (Tfunction
                                      (Tcons tuint (Tcons tulong Tnil)) tuint
                                      cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
            (Sset _level (Etempvar _t'2 tuint)))
          (Ssequence
            (Sset _pte_pa
              (Ebinop Oand
                (Ebinop Oand (Etempvar _pte tulong)
                  (Econst_long (Int64.repr 281474976710655) tulong) tulong)
                (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _pte_pa tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Ssequence
                  (Sset _pfn
                    (Ebinop Odiv (Etempvar _pte_pa tulong)
                      (Econst_long (Int64.repr 4096) tulong) tulong))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _level tuint)
                                   (Econst_int (Int.repr 2) tuint) tint)
                      (Sset _pfn
                        (Ebinop Oadd (Etempvar _pfn tulong)
                          (Ebinop Oand
                            (Ebinop Odiv (Etempvar _addr tulong)
                              (Econst_long (Int64.repr 4096) tulong) tulong)
                            (Econst_int (Int.repr 511) tint) tulong) tulong))
                      Sskip)
                    (Scall None
                      (Evar grant_vm_page (Tfunction
                                             (Tcons tuint (Tcons tulong Tnil))
                                             tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) :: nil))))
                Sskip)
              (Ssequence
                (Sset _addr
                  (Ebinop Oadd (Etempvar _addr tulong)
                    (Econst_long (Int64.repr 4096) tulong) tulong))
                (Sset _num
                  (Ebinop Osub (Etempvar _num tulong)
                    (Econst_long (Int64.repr 1) tulong) tulong))))))))).

Definition f_grant_stage2_sg_gpa := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pte, tulong) :: (_pte_pa, tulong) :: (_pfn, tulong) ::
               (_num, tulong) :: (_level, tuint) :: (_t'2, tuint) ::
               (_t'1, tulong) :: nil);
  fn_body := grant_stage2_sg_gpa_body
|}.

Definition revoke_stage2_sg_gpa_body :=
  (Ssequence
    (Sset _num
      (Ebinop Odiv
        (Ebinop Oadd (Etempvar _size tulong) (Econst_int (Int.repr 4095) tint)
          tulong) (Econst_long (Int64.repr 4096) tulong) tulong))
    (Swhile
      (Ebinop Ogt (Etempvar _num tulong) (Econst_long (Int64.repr 0) tulong)
        tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar walk_s2pt (Tfunction (Tcons tuint (Tcons tulong Tnil))
                               tulong cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
          (Sset _pte (Etempvar _t'1 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar get_level_s2pt (Tfunction
                                      (Tcons tuint (Tcons tulong Tnil)) tuint
                                      cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) :: nil))
            (Sset _level (Etempvar _t'2 tuint)))
          (Ssequence
            (Sset _pte_pa
              (Ebinop Oand
                (Ebinop Oand (Etempvar _pte tulong)
                  (Econst_long (Int64.repr 281474976710655) tulong) tulong)
                (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _pte_pa tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Ssequence
                  (Sset _pfn
                    (Ebinop Odiv (Etempvar _pte_pa tulong)
                      (Econst_long (Int64.repr 4096) tulong) tulong))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _level tuint)
                                   (Econst_int (Int.repr 2) tuint) tint)
                      (Sset _pfn
                        (Ebinop Oadd (Etempvar _pfn tulong)
                          (Ebinop Oand
                            (Ebinop Odiv (Etempvar _addr tulong)
                              (Econst_long (Int64.repr 4096) tulong) tulong)
                            (Econst_int (Int.repr 511) tint) tulong) tulong))
                      Sskip)
                    (Scall None
                      (Evar revoke_vm_page (Tfunction
                                              (Tcons tuint (Tcons tulong Tnil))
                                              tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) :: nil))))
                Sskip)
              (Ssequence
                (Sset _addr
                  (Ebinop Oadd (Etempvar _addr tulong)
                    (Econst_long (Int64.repr 4096) tulong) tulong))
                (Sset _num
                  (Ebinop Osub (Etempvar _num tulong)
                    (Econst_long (Int64.repr 1) tulong) tulong))))))))).

Definition f_revoke_stage2_sg_gpa := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pte, tulong) :: (_pte_pa, tulong) :: (_pfn, tulong) ::
               (_num, tulong) :: (_level, tuint) :: (_t'2, tuint) ::
               (_t'1, tulong) :: nil);
  fn_body := revoke_stage2_sg_gpa_body
|}.
```
