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
Definition _arg1 := 4%positive.
Definition _arg2 := 5%positive.
Definition _arg3 := 6%positive.
Definition _arg4 := 7%positive.
Definition _arg5 := 8%positive.
Definition _base := 9%positive.
Definition _cb_offset := 10%positive.
Definition _cbndx := 11%positive.
Definition _cnt := 12%positive.
Definition _count := 13%positive.
Definition _cur_ticket := 14%positive.
Definition _cur_vcpuid := 15%positive.
Definition _cur_vmid := 16%positive.
Definition _data := 17%positive.
Definition _dirty := 18%positive.
Definition _ec := 19%positive.
Definition _end := 20%positive.
Definition _esr := 21%positive.
Definition _esr_el2 := 22%positive.
Definition _exit_type := 23%positive.
Definition _fault_ipa := 24%positive.
Definition _get_now := 25%positive.
Definition _gfn := 26%positive.
Definition _gpa := 27%positive.
Definition _hsr := 28%positive.
Definition _hsr_ec := 29%positive.
Definition _i := 30%positive.
Definition _inbuf := 31%positive.
Definition _inc_exe := 32%positive.
Definition _incr_now := 33%positive.
Definition _incr_ticket := 34%positive.
Definition _index := 35%positive.
Definition _inowner := 36%positive.
Definition _inpfn := 37%positive.
Definition _iova := 38%positive.
Definition _is_write := 39%positive.
Definition _kvm := 40%positive.
Definition _len := 41%positive.
Definition _level := 42%positive.
Definition _lk := 43%positive.
Definition _load_addr := 44%positive.
Definition _load_idx := 45%positive.
Definition _load_info_cnt := 46%positive.
Definition _log_hold := 47%positive.
Definition _log_incr := 48%positive.
Definition _main := 49%positive.
Definition _map := 50%positive.
Definition _mapped := 51%positive.
Definition _my_ticket := 52%positive.
Definition _n := 53%positive.
Definition _next := 54%positive.
Definition _num := 55%positive.
Definition _num_context_banks := 56%positive.
Definition _offset := 57%positive.
Definition _outbuf := 58%positive.
Definition _outowner := 59%positive.
Definition _outpfn := 60%positive.
Definition _owner := 61%positive.
Definition _p_index := 62%positive.
Definition _pa := 63%positive.
Definition _paddr := 64%positive.
Definition _page_count := 65%positive.
Definition _pass_hlock := 66%positive.
Definition _pass_lock := 67%positive.
Definition _pass_qlock := 68%positive.
Definition _pc := 69%positive.
Definition _perm := 70%positive.
Definition _pfn := 71%positive.
Definition _pgd := 72%positive.
Definition _pgd_idx := 73%positive.
Definition _pgd_pa := 74%positive.
Definition _pgnum := 75%positive.
Definition _pmd := 76%positive.
Definition _pmd_idx := 77%positive.
Definition _pmd_pa := 78%positive.
Definition _power := 79%positive.
Definition _prot := 80%positive.
Definition _pte := 81%positive.
Definition _pte_idx := 82%positive.
Definition _pte_pa := 83%positive.
Definition _pud := 84%positive.
Definition _pud_idx := 85%positive.
Definition _pud_pa := 86%positive.
Definition _r_index := 87%positive.
Definition _reg := 88%positive.
Definition _remap := 89%positive.
Definition _remap_addr := 90%positive.
Definition _res := 91%positive.
Definition _ret := 92%positive.
Definition _ret64 := 93%positive.
Definition _rt := 94%positive.
Definition _size := 95%positive.
Definition _smmu_enable := 96%positive.
Definition _smmu_index := 97%positive.
Definition _start := 98%positive.
Definition _state := 99%positive.
Definition _t_vmid := 100%positive.
Definition _target := 101%positive.
Definition _target_addr := 102%positive.
Definition _target_vmid := 103%positive.
Definition _total_smmu := 104%positive.
Definition _ttbr := 105%positive.
Definition _ttbr_pa := 106%positive.
Definition _type := 107%positive.
Definition _val := 108%positive.
Definition _valid := 109%positive.
Definition _vcpu := 110%positive.
Definition _vcpu_state := 111%positive.
Definition _vcpuid := 112%positive.
Definition _vm_state := 113%positive.
Definition _vmid := 114%positive.
Definition _vttbr := 115%positive.
Definition _vttbr_pa := 116%positive.
Definition _wait_hlock := 117%positive.
Definition _wait_lock := 118%positive.
Definition _wait_qlock := 119%positive.
Definition _write_val := 120%positive.
Definition _t'1 := 121%positive.
Definition _t'2 := 122%positive.
Definition _t'3 := 123%positive.
Definition _t'4 := 124%positive.
Definition _t'5 := 125%positive.
Definition _t'6 := 126%positive.
Definition _t'7 := 127%positive.
Definition _t'8 := 128%positive.

Definition save_shadow_kvm_regs_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar get_cur_vmid (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _vmid (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _vcpuid (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar get_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))) tulong
                                     cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Econst_int (Int.repr 44) tuint) :: nil))
          (Sset _ec (Etempvar _t'3 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                       (Econst_long (Int64.repr 2) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar get_shadow_esr (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tulong
                                        cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
              (Sset _hsr (Etempvar _t'4 tulong)))
            (Ssequence
              (Sset _hsr_ec
                (Ebinop Oshr
                  (Ebinop Oand (Etempvar _hsr tulong)
                    (Econst_long (Int64.repr 4227858432) tulong) tulong)
                  (Econst_long (Int64.repr 26) tulong) tulong))
              (Sifthenelse (Ebinop Oeq (Etempvar _hsr_ec tulong)
                             (Econst_int (Int.repr 1) tint) tint)
                (Scall None
                  (Evar prep_wfx (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                    tvoid cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _hsr_ec tulong)
                               (Econst_int (Int.repr 18) tint) tint)
                  (Scall None
                    (Evar prep_hvc (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                      tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _hsr_ec tulong)
                                 (Econst_int (Int.repr 22) tint) tint)
                    (Scall None
                      (Evar prep_hvc (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _hsr_ec tulong)
                                   (Econst_int (Int.repr 32) tint) tint)
                      (Scall None
                        (Evar prep_abort (Tfunction
                                            (Tcons tuint (Tcons tuint Tnil))
                                            tvoid cc_default))
                        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                         nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _hsr_ec tulong)
                                     (Econst_int (Int.repr 36) tint) tint)
                        (Scall None
                          (Evar prep_abort (Tfunction
                                              (Tcons tuint (Tcons tuint Tnil))
                                              tvoid cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Etempvar _vcpuid tuint) :: nil))
                        (Scall None
                          (Evar panic (Tfunction Tnil tvoid cc_default)) nil))))))))
          Sskip)))).

Definition f_save_shadow_kvm_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_ec, tulong) :: (_hsr, tulong) :: (_hsr_ec, tulong) ::
               (_vmid, tuint) :: (_vcpuid, tuint) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := save_shadow_kvm_regs_body
|}.

Definition restore_shadow_kvm_regs_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar get_cur_vmid (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _vmid (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _vcpuid (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar get_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))) tulong
                                     cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Econst_int (Int.repr 45) tuint) :: nil))
          (Sset _dirty (Etempvar _t'3 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _dirty tulong)
                       (Econst_long (Int64.repr (-1)) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar is_inc_exe (Tfunction (Tcons tuint Tnil) tuint
                                    cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _inc_exe (Etempvar _t'4 tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _inc_exe tuint)
                             (Econst_int (Int.repr 0) tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar reset_gp_regs (Tfunction
                                           (Tcons tuint (Tcons tuint Tnil))
                                           tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  (Scall None
                    (Evar reset_sys_regs (Tfunction
                                            (Tcons tuint (Tcons tuint Tnil))
                                            tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil)))
                Sskip)
              (Scall None
                (Evar set_shadow_dirty_bit (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tulong Tnil))) tvoid
                                              cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_long (Int64.repr 0) tulong) :: nil))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar get_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tuint Tnil)))
                                         tulong cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 44) tuint) :: nil))
              (Sset _ec (Etempvar _t'5 tulong)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                             (Econst_long (Int64.repr 2) tulong) tint)
                (Scall None
                  (Evar sync_dirty_to_shadow (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)) tvoid
                                                cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                Sskip)
              (Ssequence
                (Sifthenelse (Ebinop Oand (Etempvar _dirty tulong)
                               (Econst_long (Int64.repr 60129542144) tulong)
                               tulong)
                  (Scall None
                    (Evar update_exception_gp_regs (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil))
                                                      tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Oand (Etempvar _dirty tulong)
                                 (Econst_long (Int64.repr 4294967296) tulong)
                                 tulong)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'6)
                          (Evar get_shadow_ctxt (Tfunction
                                                   (Tcons tuint
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil)))
                                                   tulong cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Etempvar _vcpuid tuint) ::
                           (Econst_int (Int.repr 32) tuint) :: nil))
                        (Sset _pc (Etempvar _t'6 tulong)))
                      (Scall None
                        (Evar set_shadow_ctxt (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint
                                                     (Tcons tuint
                                                       (Tcons tulong Tnil))))
                                                 tvoid cc_default))
                        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                         (Econst_int (Int.repr 32) tuint) ::
                         (Ebinop Oadd (Etempvar _pc tulong)
                           (Econst_long (Int64.repr 4) tulong) tulong) :: nil)))
                    Sskip)
                  (Ssequence
                    (Scall None
                      (Evar set_shadow_dirty_bit (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil)))
                                                    tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_long (Int64.repr 0) tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar set_shadow_ctxt (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint
                                                     (Tcons tuint
                                                       (Tcons tulong Tnil))))
                                                 tvoid cc_default))
                        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                         (Econst_int (Int.repr 41) tuint) ::
                         (Econst_long (Int64.repr 0) tulong) :: nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar get_vm_fault_addr (Tfunction
                                                       (Tcons tuint
                                                         (Tcons tuint Tnil))
                                                       tulong cc_default))
                            ((Etempvar _vmid tuint) ::
                             (Etempvar _vcpuid tuint) :: nil))
                          (Sset _addr (Etempvar _t'7 tulong)))
                        (Ssequence
                          (Sifthenelse (Ebinop Ole
                                         (Econst_long (Int64.repr 4096) tulong)
                                         (Etempvar _addr tulong) tint)
                            (Sset _t'8
                              (Ecast
                                (Ebinop Olt (Etempvar _addr tulong)
                                  (Econst_long (Int64.repr 281474976710656) tulong)
                                  tint) tbool))
                            (Sset _t'8 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'8 tint)
                            (Scall None
                              (Evar post_handle_shadow_s2pt_fault (Tfunction
                                                                     (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil)))
                                                                     tvoid
                                                                     cc_default))
                              ((Etempvar _vmid tuint) ::
                               (Etempvar _vcpuid tuint) ::
                               (Etempvar _addr tulong) :: nil))
                            Sskip))))))))))))).

Definition f_restore_shadow_kvm_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_dirty, tulong) :: (_ec, tulong) :: (_pc, tulong) ::
               (_addr, tulong) :: (_vmid, tuint) :: (_vcpuid, tuint) ::
               (_inc_exe, tuint) :: (_t'8, tint) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tuint) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := restore_shadow_kvm_regs_body
|}.
```
