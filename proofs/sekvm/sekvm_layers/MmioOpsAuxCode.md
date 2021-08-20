# MmioOpsAuxCode

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
Definition _num := 43%positive.
Definition _num_context_banks := 44%positive.
Definition _offset := 45%positive.
Definition _outbuf := 46%positive.
Definition _outowner := 47%positive.
Definition _outpfn := 48%positive.
Definition _owner := 49%positive.
Definition _pa := 50%positive.
Definition _paddr := 51%positive.
Definition _page_count := 52%positive.
Definition _pass_hlock := 53%positive.
Definition _pass_lock := 54%positive.
Definition _pass_qlock := 55%positive.
Definition _perm := 56%positive.
Definition _pfn := 57%positive.
Definition _pgnum := 58%positive.
Definition _power := 59%positive.
Definition _prot := 60%positive.
Definition _pte := 61%positive.
Definition _pte_pa := 62%positive.
Definition _remap := 63%positive.
Definition _remap_addr := 64%positive.
Definition _res := 65%positive.
Definition _ret := 66%positive.
Definition _rt := 67%positive.
Definition _size := 68%positive.
Definition _smmu_enable := 69%positive.
Definition _smmu_index := 70%positive.
Definition _start := 71%positive.
Definition _state := 72%positive.
Definition _t_vmid := 73%positive.
Definition _target := 74%positive.
Definition _target_addr := 75%positive.
Definition _target_vmid := 76%positive.
Definition _total_smmu := 77%positive.
Definition _type := 78%positive.
Definition _val := 79%positive.
Definition _valid := 80%positive.
Definition _vcpu := 81%positive.
Definition _vcpu_state := 82%positive.
Definition _vcpuid := 83%positive.
Definition _vm_state := 84%positive.
Definition _vmid := 85%positive.
Definition _wait_hlock := 86%positive.
Definition _wait_lock := 87%positive.
Definition _wait_qlock := 88%positive.
Definition _write_val := 89%positive.
Definition _t'1 := 90%positive.
Definition _t'2 := 91%positive.
Definition _t'3 := 92%positive.
Definition _t'4 := 93%positive.

Definition is_smmu_range_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar get_smmu_num (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _total_smmu (Etempvar _t'1 tuint)))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tuint))
      (Ssequence
        (Sset _res (Econst_int (Int.repr (-1)) tuint))
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tuint) (Etempvar _total_smmu tuint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar get_smmu_base (Tfunction (Tcons tuint Tnil) tulong
                                         cc_default))
                  ((Etempvar _i tuint) :: nil))
                (Sset _base (Etempvar _t'2 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_smmu_size (Tfunction (Tcons tuint Tnil) tulong
                                           cc_default))
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

Definition f_is_smmu_range := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_base, tulong) :: (_size, tulong) :: (_total_smmu, tuint) ::
               (_i, tuint) :: (_res, tuint) :: (_t'4, tint) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body := is_smmu_range_body
|}.

Definition handle_host_mmio_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar host_get_fault_ipa (Tfunction (Tcons tulong Tnil) tulong
                                    cc_default))
        ((Etempvar _addr tulong) :: nil))
      (Sset _fault_ipa (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar host_dabt_get_as (Tfunction (Tcons tuint Tnil) tuint
                                    cc_default))
          ((Etempvar _hsr tuint) :: nil))
        (Sset _len (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar host_dabt_is_write (Tfunction (Tcons tuint Tnil) tuint
                                        cc_default))
            ((Etempvar _hsr tuint) :: nil))
          (Sset _is_write (Etempvar _t'3 tuint)))
        (Sifthenelse (Ebinop Oeq (Etempvar _is_write tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Scall None
              (Evar handle_smmu_read (Tfunction
                                        (Tcons tuint
                                          (Tcons tulong (Tcons tuint Tnil)))
                                        tvoid cc_default))
              ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
               (Etempvar _len tuint) :: nil))
            (Scall None
              (Evar host_skip_instr (Tfunction Tnil tvoid cc_default)) nil))
          (Ssequence
            (Scall None
              (Evar handle_smmu_write (Tfunction
                                         (Tcons tuint
                                           (Tcons tulong
                                             (Tcons tuint (Tcons tuint Tnil))))
                                         tvoid cc_default))
              ((Etempvar _hsr tuint) :: (Etempvar _fault_ipa tulong) ::
               (Etempvar _len tuint) :: (Etempvar _index tuint) :: nil))
            (Scall None
              (Evar host_skip_instr (Tfunction Tnil tvoid cc_default)) nil)))))).

Definition f_handle_host_mmio := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: (_index, tuint) :: (_hsr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_fault_ipa, tulong) :: (_is_write, tuint) :: (_len, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body := handle_host_mmio_body
|}.
```
