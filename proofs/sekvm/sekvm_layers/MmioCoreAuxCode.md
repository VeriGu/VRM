# MmioCoreAuxCode

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
Definition _kvm := 28%positive.
Definition _len := 29%positive.
Definition _level := 30%positive.
Definition _lk := 31%positive.
Definition _load_addr := 32%positive.
Definition _load_idx := 33%positive.
Definition _load_info_cnt := 34%positive.
Definition _log_hold := 35%positive.
Definition _log_incr := 36%positive.
Definition _main := 37%positive.
Definition _map := 38%positive.
Definition _mapped := 39%positive.
Definition _my_ticket := 40%positive.
Definition _n := 41%positive.
Definition _num := 42%positive.
Definition _offset := 43%positive.
Definition _outbuf := 44%positive.
Definition _outowner := 45%positive.
Definition _outpfn := 46%positive.
Definition _owner := 47%positive.
Definition _pa := 48%positive.
Definition _paddr := 49%positive.
Definition _page_count := 50%positive.
Definition _pass_hlock := 51%positive.
Definition _pass_lock := 52%positive.
Definition _pass_qlock := 53%positive.
Definition _perm := 54%positive.
Definition _pfn := 55%positive.
Definition _pgnum := 56%positive.
Definition _power := 57%positive.
Definition _prot := 58%positive.
Definition _pte := 59%positive.
Definition _pte_pa := 60%positive.
Definition _remap := 61%positive.
Definition _remap_addr := 62%positive.
Definition _res := 63%positive.
Definition _ret := 64%positive.
Definition _rt := 65%positive.
Definition _size := 66%positive.
Definition _smmu_enable := 67%positive.
Definition _smmu_index := 68%positive.
Definition _start := 69%positive.
Definition _state := 70%positive.
Definition _t_vmid := 71%positive.
Definition _target := 72%positive.
Definition _target_addr := 73%positive.
Definition _type := 74%positive.
Definition _val := 75%positive.
Definition _valid := 76%positive.
Definition _vcpu := 77%positive.
Definition _vcpu_state := 78%positive.
Definition _vcpuid := 79%positive.
Definition _vm_state := 80%positive.
Definition _vmid := 81%positive.
Definition _wait_hlock := 82%positive.
Definition _wait_lock := 83%positive.
Definition _wait_qlock := 84%positive.
Definition _write_val := 85%positive.
Definition _t'1 := 86%positive.
Definition _t'2 := 87%positive.
Definition _t'3 := 88%positive.
Definition _t'4 := 89%positive.
Definition _t'5 := 90%positive.
Definition _t'6 := 91%positive.

Definition handle_smmu_global_access_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar host_get_mmio_data (Tfunction (Tcons tuint Tnil) tulong
                                    cc_default))
        ((Etempvar _hsr tuint) :: nil))
      (Sset _data (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _offset tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'5
            (Ecast
              (Ebinop Ole (Etempvar _offset tulong)
                (Econst_int (Int.repr 4096) tuint) tint) tbool))
          (Sset _t'5 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'5 tint)
          (Sifthenelse (Ebinop Oeq (Etempvar _offset tulong)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Ssequence
              (Sset _smmu_enable
                (Ebinop Oand
                  (Ebinop Oshr (Etempvar _data tulong)
                    (Econst_int (Int.repr 21) tuint) tulong)
                  (Econst_int (Int.repr 1) tuint) tulong))
              (Sifthenelse (Ebinop Oeq (Etempvar _smmu_enable tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Sset _ret (Econst_int (Int.repr 0) tuint))
                (Sset _ret (Econst_int (Int.repr 1) tuint))))
            (Sifthenelse (Ebinop Oeq (Etempvar _offset tulong)
                           (Econst_int (Int.repr 8) tuint) tint)
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Oand (Etempvar _data tulong)
                               (Econst_int (Int.repr 255) tint) tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Sset _ret (Econst_int (Int.repr 1) tuint))
                (Sset _ret (Econst_int (Int.repr 0) tuint)))
              (Sset _ret (Econst_int (Int.repr 1) tuint))))
          (Ssequence
            (Sifthenelse (Ebinop Oge (Etempvar _offset tulong)
                           (Econst_int (Int.repr 4096) tuint) tint)
              (Sset _t'4
                (Ecast
                  (Ebinop Olt (Etempvar _offset tulong)
                    (Econst_int (Int.repr 6144) tuint) tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _n
                  (Ebinop Odiv
                    (Ebinop Osub (Etempvar _offset tulong)
                      (Econst_int (Int.repr 4096) tuint) tulong)
                    (Econst_int (Int.repr 4) tuint) tulong))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar get_smmu_cfg_vmid (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil)) tuint
                                                 cc_default))
                      ((Etempvar _n tulong) :: (Etempvar _smmu_index tuint) ::
                       nil))
                    (Sset _vmid (Ecast (Etempvar _t'2 tuint) tulong)))
                  (Ssequence
                    (Sset _type
                      (Ebinop Oshr (Etempvar _data tulong)
                        (Econst_int (Int.repr 16) tuint) tulong))
                    (Ssequence
                      (Sset _t_vmid
                        (Ebinop Oand (Etempvar _data tulong)
                          (Econst_int (Int.repr 255) tint) tulong))
                      (Sifthenelse (Ebinop Oeq (Etempvar _vmid tulong)
                                     (Econst_int (Int.repr 0) tuint) tint)
                        (Sset _ret (Econst_int (Int.repr 1) tuint))
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _type tulong)
                                         (Econst_int (Int.repr 0) tuint) tint)
                            (Sset _t'3
                              (Ecast
                                (Ebinop Oeq (Etempvar _vmid tulong)
                                  (Etempvar _t_vmid tulong) tint) tbool))
                            (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'3 tint)
                            (Sset _ret (Econst_int (Int.repr 1) tuint))
                            (Sset _ret (Econst_int (Int.repr 0) tuint)))))))))
              (Sset _ret (Econst_int (Int.repr 1) tuint))))))
      (Ssequence
        (Scall (Some _t'6)
          (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _ret tuint) :: nil))
        (Sreturn (Some (Etempvar _t'6 tuint)))))).

Definition f_handle_smmu_global_access := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: (_offset, tulong) :: (_smmu_index, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_data, tulong) :: (_smmu_enable, tulong) :: (_n, tulong) ::
               (_vmid, tulong) :: (_type, tulong) :: (_t_vmid, tulong) ::
               (_ret, tuint) :: (_t'6, tuint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tuint) ::
               (_t'1, tulong) :: nil);
  fn_body := handle_smmu_global_access_body
|}.

Definition handle_smmu_cb_access_body :=
  (Ssequence
    (Sset _offset
      (Ebinop Osub (Etempvar _offset tulong)
        (Econst_int (Int.repr 32768) tuint) tulong))
    (Ssequence
      (Sset _cb_offset
        (Ebinop Oand (Etempvar _offset tulong)
          (Econst_int (Int.repr 4095) tuint) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _cb_offset tulong)
                       (Econst_int (Int.repr 32) tint) tint)
          (Sset _ret (Econst_int (Int.repr 2) tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _cb_offset tulong)
                         (Econst_int (Int.repr 52) tint) tint)
            (Sset _ret (Econst_int (Int.repr 0) tuint))
            (Sset _ret (Econst_int (Int.repr 1) tuint))))
        (Ssequence
          (Scall (Some _t'1)
            (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
            ((Etempvar _ret tuint) :: nil))
          (Sreturn (Some (Etempvar _t'1 tuint))))))).

Definition f_handle_smmu_cb_access := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_offset, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_cb_offset, tulong) :: (_ret, tuint) :: (_t'1, tuint) :: nil);
  fn_body := handle_smmu_cb_access_body
|}.

Definition __handle_smmu_write_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _len tuint)
                 (Econst_int (Int.repr 8) tuint) tint)
    (Sifthenelse (Ebinop Oeq (Etempvar _write_val tuint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar host_get_mmio_data (Tfunction (Tcons tuint Tnil) tulong
                                        cc_default))
            ((Etempvar _hsr tuint) :: nil))
          (Sset _data (Etempvar _t'1 tulong)))
        (Scall None
          (Evar writeq_relaxed (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                  tvoid cc_default))
          ((Etempvar _data tulong) :: (Etempvar _fault_ipa tulong) :: nil)))
      (Scall None
        (Evar writeq_relaxed (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                tvoid cc_default))
        ((Etempvar _val tulong) :: (Etempvar _fault_ipa tulong) :: nil)))
    (Sifthenelse (Ebinop Oeq (Etempvar _len tuint)
                   (Econst_int (Int.repr 4) tuint) tint)
      (Scall None
        (Evar writel_relaxed (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                tvoid cc_default))
        ((Etempvar _val tulong) :: (Etempvar _fault_ipa tulong) :: nil))
      (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))).

Definition f___handle_smmu_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: (_fault_ipa, tulong) :: (_len, tuint) ::
                (_val, tulong) :: (_write_val, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_data, tulong) :: (_t'1, tulong) :: nil);
  fn_body := __handle_smmu_write_body
|}.

Definition __handle_smmu_read_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar host_dabt_get_rd (Tfunction (Tcons tuint Tnil) tuint cc_default))
        ((Etempvar _hsr tuint) :: nil))
      (Sset _rt (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _vcpuid (Etempvar _t'2 tuint)))
      (Sifthenelse (Ebinop Oeq (Etempvar _len tuint)
                     (Econst_int (Int.repr 8) tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar readq_relaxed (Tfunction (Tcons tulong Tnil) tulong
                                     cc_default))
              ((Etempvar _fault_ipa tulong) :: nil))
            (Sset _data (Etempvar _t'3 tulong)))
          (Scall None
            (Evar set_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil))))
                                     tvoid cc_default))
            ((Econst_int (Int.repr 0) tuint) :: (Etempvar _vcpuid tuint) ::
             (Etempvar _rt tuint) :: (Etempvar _data tulong) :: nil)))
        (Sifthenelse (Ebinop Oeq (Etempvar _len tuint)
                       (Econst_int (Int.repr 4) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar readl_relaxed (Tfunction (Tcons tulong Tnil) tulong
                                       cc_default))
                ((Etempvar _fault_ipa tulong) :: nil))
              (Sset _data (Etempvar _t'4 tulong)))
            (Scall None
              (Evar set_shadow_ctxt (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tulong Tnil))))
                                       tvoid cc_default))
              ((Econst_int (Int.repr 0) tuint) :: (Etempvar _vcpuid tuint) ::
               (Etempvar _rt tuint) :: (Etempvar _data tulong) :: nil)))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))))).

Definition f___handle_smmu_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hsr, tuint) :: (_fault_ipa, tulong) :: (_len, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_data, tulong) :: (_rt, tuint) :: (_vcpuid, tuint) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := __handle_smmu_read_body
|}.
```
