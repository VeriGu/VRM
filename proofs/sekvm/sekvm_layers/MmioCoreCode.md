# MmioCoreCode

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
Definition _fault_ipa := 12%positive.
Definition _get_now := 13%positive.
Definition _gfn := 14%positive.
Definition _gpa := 15%positive.
Definition _hsr := 16%positive.
Definition _i := 17%positive.
Definition _inbuf := 18%positive.
Definition _inc_exe := 19%positive.
Definition _incr_now := 20%positive.
Definition _incr_ticket := 21%positive.
Definition _index := 22%positive.
Definition _inowner := 23%positive.
Definition _inpfn := 24%positive.
Definition _iova := 25%positive.
Definition _kvm := 26%positive.
Definition _len := 27%positive.
Definition _level := 28%positive.
Definition _lk := 29%positive.
Definition _load_addr := 30%positive.
Definition _load_idx := 31%positive.
Definition _load_info_cnt := 32%positive.
Definition _log_hold := 33%positive.
Definition _log_incr := 34%positive.
Definition _main := 35%positive.
Definition _map := 36%positive.
Definition _mapped := 37%positive.
Definition _my_ticket := 38%positive.
Definition _num := 39%positive.
Definition _offset := 40%positive.
Definition _outbuf := 41%positive.
Definition _outowner := 42%positive.
Definition _outpfn := 43%positive.
Definition _owner := 44%positive.
Definition _pa := 45%positive.
Definition _paddr := 46%positive.
Definition _page_count := 47%positive.
Definition _pass_hlock := 48%positive.
Definition _pass_lock := 49%positive.
Definition _pass_qlock := 50%positive.
Definition _perm := 51%positive.
Definition _pfn := 52%positive.
Definition _pgnum := 53%positive.
Definition _power := 54%positive.
Definition _prot := 55%positive.
Definition _pte := 56%positive.
Definition _pte_pa := 57%positive.
Definition _remap := 58%positive.
Definition _remap_addr := 59%positive.
Definition _res := 60%positive.
Definition _ret := 61%positive.
Definition _size := 62%positive.
Definition _start := 63%positive.
Definition _state := 64%positive.
Definition _target := 65%positive.
Definition _target_addr := 66%positive.
Definition _val := 67%positive.
Definition _valid := 68%positive.
Definition _vcpu := 69%positive.
Definition _vcpu_state := 70%positive.
Definition _vcpuid := 71%positive.
Definition _vm_state := 72%positive.
Definition _vmid := 73%positive.
Definition _wait_hlock := 74%positive.
Definition _wait_lock := 75%positive.
Definition _wait_qlock := 76%positive.
Definition _write_val := 77%positive.
Definition _t'1 := 78%positive.
Definition _t'2 := 79%positive.
Definition _t'3 := 80%positive.
Definition _t'4 := 81%positive.

Definition handle_smmu_write_body :=
  (Ssequence
    (Sset _offset
      (Ebinop Oand (Etempvar _fault_ipa tulong)
        (Econst_int (Int.repr 65535) tuint) tulong))
    (Ssequence
      (Sset _write_val (Econst_int (Int.repr 0) tuint))
      (Sifthenelse (Ebinop Olt (Etempvar _offset tulong)
                     (Econst_int (Int.repr 32768) tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar handle_smmu_global_access (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tulong
                                                     (Tcons tuint Tnil))) tuint
                                                 cc_default))
              ((Etempvar _hsr tuint) :: (Etempvar _offset tulong) ::
               (Etempvar _index tuint) :: nil))
            (Sset _ret (Etempvar _t'1 tuint)))
          (Sifthenelse (Ebinop Oeq (Etempvar _ret tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
            (Scall None
              (Evar __handle_smmu_write (Tfunction
                                           (Tcons tuint
                                             (Tcons tulong
                                               (Tcons tuint
                                                 (Tcons tulong
                                                   (Tcons tuint Tnil))))) tvoid
                                           cc_default))
              ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
               (Etempvar _len tuint) :: (Econst_long (Int64.repr 0) tulong) ::
               (Etempvar _write_val tuint) :: nil))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar handle_smmu_cb_access (Tfunction (Tcons tulong Tnil) tuint
                                             cc_default))
              ((Etempvar _offset tulong) :: nil))
            (Sset _ret (Etempvar _t'2 tuint)))
          (Sifthenelse (Ebinop Oeq (Etempvar _ret tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
            (Sifthenelse (Ebinop Oeq (Etempvar _ret tuint)
                           (Econst_int (Int.repr 2) tuint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar smmu_get_cbndx (Tfunction (Tcons tulong Tnil) tuint
                                            cc_default))
                    ((Etempvar _offset tulong) :: nil))
                  (Sset _cbndx (Etempvar _t'3 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar get_smmu_cfg_hw_ttbr (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil))
                                                    tulong cc_default))
                      ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
                       nil))
                    (Sset _val (Etempvar _t'4 tulong)))
                  (Ssequence
                    (Sset _write_val (Econst_int (Int.repr 1) tuint))
                    (Scall None
                      (Evar __handle_smmu_write (Tfunction
                                                   (Tcons tuint
                                                     (Tcons tulong
                                                       (Tcons tuint
                                                         (Tcons tulong
                                                           (Tcons tuint Tnil)))))
                                                   tvoid cc_default))
                      ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
                       (Etempvar _len tuint) :: (Etempvar _val tulong) ::
                       (Etempvar _write_val tuint) :: nil)))))
              (Scall None
                (Evar __handle_smmu_write (Tfunction
                                             (Tcons tuint
                                               (Tcons tulong
                                                 (Tcons tuint
                                                   (Tcons tulong
                                                     (Tcons tuint Tnil)))))
                                             tvoid cc_default))
                ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
                 (Etempvar _len tuint) ::
                 (Econst_long (Int64.repr 0) tulong) ::
                 (Etempvar _write_val tuint) :: nil)))))))).

Definition f_handle_smmu_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: (_fault_ipa, tulong) :: (_len, tuint) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_offset, tulong) :: (_val, tulong) :: (_ret, tuint) ::
               (_write_val, tuint) :: (_cbndx, tuint) :: (_t'4, tulong) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := handle_smmu_write_body
|}.

Definition handle_smmu_read_body :=
  (Ssequence
    (Sset _offset
      (Ebinop Oand (Etempvar _fault_ipa tulong)
        (Econst_int (Int.repr 65535) tuint) tulong))
    (Sifthenelse (Ebinop Olt (Etempvar _offset tulong)
                   (Econst_int (Int.repr 32768) tuint) tint)
      (Scall None
        (Evar __handle_smmu_read (Tfunction
                                    (Tcons tuint
                                      (Tcons tulong (Tcons tuint Tnil))) tvoid
                                    cc_default))
        ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
         (Etempvar _len tuint) :: nil))
      (Scall None
        (Evar __handle_smmu_read (Tfunction
                                    (Tcons tuint
                                      (Tcons tulong (Tcons tuint Tnil))) tvoid
                                    cc_default))
        ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
         (Etempvar _len tuint) :: nil)))).

Definition f_handle_smmu_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: (_fault_ipa, tulong) :: (_len, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_offset, tulong) :: nil);
  fn_body := handle_smmu_read_body
|}.
```
