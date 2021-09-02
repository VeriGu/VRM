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
Definition _remap := 53%positive.
Definition _remap_addr := 54%positive.
Definition _res := 55%positive.
Definition _ret := 56%positive.
Definition _size := 57%positive.
Definition _start := 58%positive.
Definition _state := 59%positive.
Definition _target := 60%positive.
Definition _target_addr := 61%positive.
Definition _valid := 62%positive.
Definition _vcpu := 63%positive.
Definition _vcpu_state := 64%positive.
Definition _vcpuid := 65%positive.
Definition _vm_state := 66%positive.
Definition _vmid := 67%positive.
Definition _wait_hlock := 68%positive.
Definition _wait_lock := 69%positive.
Definition _wait_qlock := 70%positive.
Definition _t'1 := 71%positive.
Definition _t'2 := 72%positive.
Definition _t'3 := 73%positive.
Definition _t'4 := 74%positive.

Definition mem_region_search_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_mem_region_cnt (Tfunction Tnil tuint cc_default)) nil)
      (Sset _cnt (Etempvar _t'1 tuint)))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tuint))
      (Ssequence
        (Sset _res (Econst_int (Int.repr (-1)) tuint))
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tuint) (Etempvar _cnt tuint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar get_mem_region_base (Tfunction (Tcons tuint Tnil)
                                               tulong cc_default))
                  ((Etempvar _i tuint) :: nil))
                (Sset _base (Etempvar _t'2 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_mem_region_size (Tfunction (Tcons tuint Tnil)
                                                 tulong cc_default))
                    ((Etempvar _i tuint) :: nil))
                  (Sset _size (Etempvar _t'3 tulong)))
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Ole (Etempvar _base tulong)
                                   (Etempvar _addr tulong) tint)
                      (Sset _t'4
                        (Ecast
                          (Ebinop Olt (Etempvar _addr tulong)
                            (Ebinop Oadd (Etempvar _base tulong)
                              (Etempvar _size tulong) tulong) tint) tbool))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint)))
                    (Sifthenelse (Etempvar _t'4 tint)
                      (Sset _res (Etempvar _i tuint))
                      Sskip))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tuint) tuint))))))
          (Sreturn (Some (Etempvar _res tuint))))))).

Definition f_mem_region_search := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_base, tulong) :: (_size, tulong) :: (_cnt, tuint) ::
               (_i, tuint) :: (_res, tuint) :: (_t'4, tint) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body := mem_region_search_body
|}.
```
