# VCPUOpsAuxCode

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
Definition ___compcert_va_int64 := 1%positive.
Definition _addr := 2%positive.
Definition _alloc := 3%positive.
Definition _arg := 4%positive.
Definition _arg1 := 5%positive.
Definition _arg2 := 6%positive.
Definition _arg3 := 7%positive.
Definition _arg4 := 8%positive.
Definition _arg5 := 9%positive.
Definition _base := 10%positive.
Definition _cb_offset := 11%positive.
Definition _cbndx := 12%positive.
Definition _cnt := 13%positive.
Definition _count := 14%positive.
Definition _cur_ticket := 15%positive.
Definition _cur_vcpuid := 16%positive.
Definition _cur_vmid := 17%positive.
Definition _data := 18%positive.
Definition _dirty := 19%positive.
Definition _ec := 20%positive.
Definition _end := 21%positive.
Definition _esr := 22%positive.
Definition _esr_el2 := 23%positive.
Definition _exit_type := 24%positive.
Definition _fault_ipa := 25%positive.
Definition _get_now := 26%positive.
Definition _gfn := 27%positive.
Definition _gpa := 28%positive.
Definition _hsr := 29%positive.
Definition _hsr_ec := 30%positive.
Definition _i := 31%positive.
Definition _inbuf := 32%positive.
Definition _inc_exe := 33%positive.
Definition _incr_now := 34%positive.
Definition _incr_ticket := 35%positive.
Definition _index := 36%positive.
Definition _inowner := 37%positive.
Definition _inpfn := 38%positive.
Definition _iova := 39%positive.
Definition _is_write := 40%positive.
Definition _kvm := 41%positive.
Definition _len := 42%positive.
Definition _level := 43%positive.
Definition _lk := 44%positive.
Definition _load_addr := 45%positive.
Definition _load_idx := 46%positive.
Definition _load_info_cnt := 47%positive.
Definition _log_hold := 48%positive.
Definition _log_incr := 49%positive.
Definition _main := 50%positive.
Definition _map := 51%positive.
Definition _mapped := 52%positive.
Definition _mpidr := 53%positive.
Definition _my_ticket := 54%positive.
Definition _n := 55%positive.
Definition _new_pc := 56%positive.
Definition _next := 57%positive.
Definition _num := 58%positive.
Definition _num_context_banks := 59%positive.
Definition _offset := 60%positive.
Definition _outbuf := 61%positive.
Definition _outowner := 62%positive.
Definition _outpfn := 63%positive.
Definition _owner := 64%positive.
Definition _p_index := 65%positive.
Definition _pa := 66%positive.
Definition _paddr := 67%positive.
Definition _page_count := 68%positive.
Definition _pass_hlock := 69%positive.
Definition _pass_lock := 70%positive.
Definition _pass_qlock := 71%positive.
Definition _pc := 72%positive.
Definition _perm := 73%positive.
Definition _pfn := 74%positive.
Definition _pgd := 75%positive.
Definition _pgd_idx := 76%positive.
Definition _pgd_pa := 77%positive.
Definition _pgnum := 78%positive.
Definition _pmd := 79%positive.
Definition _pmd_idx := 80%positive.
Definition _pmd_pa := 81%positive.
Definition _power := 82%positive.
Definition _prot := 83%positive.
Definition _psci_fn := 84%positive.
Definition _pstate := 85%positive.
Definition _pte := 86%positive.
Definition _pte_idx := 87%positive.
Definition _pte_pa := 88%positive.
Definition _pud := 89%positive.
Definition _pud_idx := 90%positive.
Definition _pud_pa := 91%positive.
Definition _r_index := 92%positive.
Definition _reg := 93%positive.
Definition _remap := 94%positive.
Definition _remap_addr := 95%positive.
Definition _res := 96%positive.
Definition _ret := 97%positive.
Definition _ret64 := 98%positive.
Definition _rt := 99%positive.
Definition _size := 100%positive.
Definition _smmu_enable := 101%positive.
Definition _smmu_index := 102%positive.
Definition _start := 103%positive.
Definition _state := 104%positive.
Definition _t_vmid := 105%positive.
Definition _target := 106%positive.
Definition _target_addr := 107%positive.
Definition _target_vmid := 108%positive.
Definition _total_smmu := 109%positive.
Definition _ttbr := 110%positive.
Definition _ttbr_pa := 111%positive.
Definition _type := 112%positive.
Definition _val := 113%positive.
Definition _valid := 114%positive.
Definition _vcpu := 115%positive.
Definition _vcpu_state := 116%positive.
Definition _vcpuid := 117%positive.
Definition _vm_state := 118%positive.
Definition _vmid := 119%positive.
Definition _vttbr := 120%positive.
Definition _vttbr_pa := 121%positive.
Definition _wait_hlock := 122%positive.
Definition _wait_lock := 123%positive.
Definition _wait_qlock := 124%positive.
Definition _write_val := 125%positive.
Definition _t'1 := 126%positive.
Definition _t'2 := 127%positive.
Definition _t'3 := 128%positive.
Definition _t'4 := 129%positive.
Definition _t'5 := 130%positive.
Definition _t'6 := 131%positive.
Definition _t'7 := 132%positive.

Definition reset_gp_regs_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_int_pc (Tfunction (Tcons tuint (Tcons tuint Tnil)) tulong
                            cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
      (Sset _pc (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar search_load_info (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                    tulong cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _pc tulong) :: nil))
        (Sset _load_addr (Etempvar _t'2 tulong)))
      (Sifthenelse (Ebinop Oeq (Etempvar _load_addr tulong)
                     (Econst_long (Int64.repr 0) tulong) tint)
        (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
        (Ssequence
          (Scall None
            (Evar clear_shadow_gp_regs (Tfunction
                                          (Tcons tuint (Tcons tuint Tnil))
                                          tvoid cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar get_int_pstate (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tulong
                                        cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
              (Sset _pstate (Etempvar _t'3 tulong)))
            (Ssequence
              (Scall None
                (Evar set_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 33) tuint) ::
                 (Etempvar _pstate tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar set_shadow_ctxt (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tulong Tnil)))) tvoid
                                           cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Econst_int (Int.repr 32) tuint) :: (Etempvar _pc tulong) ::
                   nil))
                (Scall None
                  (Evar reset_fp_regs (Tfunction
                                         (Tcons tuint (Tcons tuint Tnil)) tvoid
                                         cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))))))))).

Definition f_reset_gp_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pc, tulong) :: (_pstate, tulong) :: (_load_addr, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := reset_gp_regs_body
|}.

Definition reset_sys_regs_body :=
  (Ssequence
    (Sset _i (Econst_int (Int.repr 1) tuint))
    (Swhile
      (Ebinop Ole (Etempvar _i tuint) (Econst_long (Int64.repr 24) tulong)
        tint)
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _i tuint)
                       (Econst_int (Int.repr 1) tuint) tint)
          (Ssequence
            (Sset _mpidr
              (Ecast
                (Ebinop Oadd
                  (Ebinop Oadd
                    (Ebinop Oand (Etempvar _vcpuid tuint)
                      (Econst_int (Int.repr 15) tuint) tuint)
                    (Ebinop Omul
                      (Ebinop Oand
                        (Ebinop Odiv (Etempvar _vcpuid tuint)
                          (Econst_int (Int.repr 16) tuint) tuint)
                        (Econst_int (Int.repr 255) tuint) tuint)
                      (Econst_int (Int.repr 256) tuint) tuint) tuint)
                  (Ebinop Omul
                    (Ebinop Oand
                      (Ebinop Odiv (Etempvar _vcpuid tuint)
                        (Econst_int (Int.repr 4096) tuint) tuint)
                      (Econst_int (Int.repr 255) tuint) tuint)
                    (Econst_int (Int.repr 65536) tuint) tuint) tuint) tulong))
            (Sset _val
              (Ebinop Oadd (Etempvar _mpidr tulong)
                (Econst_long (Int64.repr 2147483648) tulong) tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _i tuint)
                         (Econst_int (Int.repr 4) tuint) tint)
            (Ssequence
              (Scall (Some _t'1)
                (Evar read_actlr_el1 (Tfunction Tnil tulong cc_default)) nil)
              (Sset _val (Etempvar _t'1 tulong)))
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_sys_reg_desc_val (Tfunction (Tcons tuint Tnil)
                                              tulong cc_default))
                ((Etempvar _i tuint) :: nil))
              (Sset _val (Etempvar _t'2 tulong)))))
        (Ssequence
          (Scall None
            (Evar set_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil))))
                                     tvoid cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 47) tuint)
               tuint) :: (Etempvar _val tulong) :: nil))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tuint)
              tuint)))))).

Definition f_reset_sys_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_val, tulong) :: (_mpidr, tulong) :: (_i, tuint) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := reset_sys_regs_body
|}.

Definition sync_dirty_to_shadow_body :=
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_shadow_dirty_bit (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tulong
                                        cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
        (Sset _dirty (Etempvar _t'1 tulong)))
      (Swhile
        (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 31) tuint) tint)
        (Ssequence
          (Sifthenelse (Ebinop Oand (Etempvar _dirty tulong)
                         (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                           (Etempvar _i tuint) tuint) tulong)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar get_int_gpr (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tuint Tnil)))
                                       tulong cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Etempvar _i tuint) :: nil))
                (Sset _reg (Etempvar _t'2 tulong)))
              (Scall None
                (Evar set_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Etempvar _i tuint) :: (Etempvar _reg tulong) :: nil)))
            Sskip)
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tuint)
              tuint)))))).

Definition f_sync_dirty_to_shadow := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_dirty, tulong) :: (_reg, tulong) :: (_i, tuint) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := sync_dirty_to_shadow_body
|}.

Definition prep_wfx_body :=
  (Scall None
    (Evar set_shadow_dirty_bit (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tulong Tnil))) tvoid
                                  cc_default))
    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
     (Econst_long (Int64.repr 4294967296) tulong) :: nil)).

Definition f_prep_wfx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := prep_wfx_body
|}.

Definition prep_hvc_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_shadow_ctxt (Tfunction
                                 (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))
                                 tulong cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
         (Econst_long (Int64.repr 0) tulong) :: nil))
      (Sset _psci_fn (Etempvar _t'1 tulong)))
    (Ssequence
      (Scall None
        (Evar set_shadow_dirty_bit (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
         (Econst_long (Int64.repr 1) tulong) :: nil))
      (Ssequence
        (Scall None
          (Evar set_int_gpr (Tfunction
                               (Tcons tuint
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tulong Tnil)))) tvoid
                               cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
           (Econst_int (Int.repr 0) tuint) :: (Etempvar _psci_fn tulong) ::
           nil))
        (Ssequence
          (Sset _psci_fn
            (Ebinop Oand (Etempvar _psci_fn tulong)
              (Econst_long (Int64.repr 4294967295) tulong) tulong))
          (Sifthenelse (Ebinop Oeq (Etempvar _psci_fn tulong)
                         (Econst_long (Int64.repr 3288334339) tulong) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar get_shadow_ctxt (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tuint Tnil)))
                                           tulong cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Econst_int (Int.repr 1) tuint) :: nil))
                (Scall None
                  (Evar set_int_gpr (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tulong Tnil))))
                                       tvoid cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Econst_int (Int.repr 1) tuint) :: (Etempvar _t'2 tulong) ::
                   nil)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_shadow_ctxt (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint (Tcons tuint Tnil)))
                                             tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 2) tuint) :: nil))
                  (Scall None
                    (Evar set_int_gpr (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 2) tuint) ::
                     (Etempvar _t'3 tulong) :: nil)))
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar get_shadow_ctxt (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint (Tcons tuint Tnil)))
                                             tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 3) tuint) :: nil))
                  (Scall None
                    (Evar set_int_gpr (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 3) tuint) ::
                     (Etempvar _t'4 tulong) :: nil)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _psci_fn tulong)
                             (Econst_long (Int64.repr 2214592516) tulong) tint)
                (Sset _t'7 (Econst_int (Int.repr 1) tint))
                (Sset _t'7
                  (Ecast
                    (Ebinop Oeq (Etempvar _psci_fn tulong)
                      (Econst_long (Int64.repr 1073741828) tulong) tint) tbool)))
              (Sifthenelse (Etempvar _t'7 tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar get_shadow_ctxt (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))) tulong
                                               cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 1) tuint) :: nil))
                    (Scall None
                      (Evar set_int_gpr (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tulong Tnil)))) tvoid
                                           cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 1) tuint) ::
                       (Etempvar _t'5 tulong) :: nil)))
                  (Ssequence
                    (Scall (Some _t'6)
                      (Evar get_shadow_ctxt (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))) tulong
                                               cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 2) tuint) :: nil))
                    (Scall None
                      (Evar set_int_gpr (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tulong Tnil)))) tvoid
                                           cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 2) tuint) ::
                       (Etempvar _t'6 tulong) :: nil))))
                (Sifthenelse (Ebinop Oeq (Etempvar _psci_fn tulong)
                               (Econst_long (Int64.repr 2214592520) tulong)
                               tint)
                  (Scall None
                    (Evar set_vm_poweroff (Tfunction (Tcons tuint Tnil) tvoid
                                             cc_default))
                    ((Etempvar _vmid tuint) :: nil))
                  Sskip)))))))).

Definition f_prep_hvc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_psci_fn, tulong) :: (_t'7, tint) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := prep_hvc_body
|}.

Definition prep_abort_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_int_esr (Tfunction (Tcons tuint (Tcons tuint Tnil)) tulong
                             cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
      (Sset _esr (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _Rd
        (Ecast
          (Ebinop Oand
            (Ebinop Odiv (Etempvar _esr tulong)
              (Econst_long (Int64.repr 65536) tulong) tulong)
            (Econst_long (Int64.repr 31) tulong) tulong) tuint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))) tulong
                                     cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Econst_int (Int.repr 42) tuint) :: nil))
          (Sset _fault_ipa
            (Ebinop Omul
              (Ebinop Odiv (Etempvar _t'2 tulong)
                (Econst_long (Int64.repr 16) tulong) tulong)
              (Econst_long (Int64.repr 4096) tulong) tulong)))
        (Sifthenelse (Ebinop Olt (Etempvar _fault_ipa tulong)
                       (Econst_long (Int64.repr 1073741824) tulong) tint)
          (Ssequence
            (Scall None
              (Evar set_shadow_dirty_bit (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint (Tcons tulong Tnil)))
                                            tvoid cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
               (Econst_long (Int64.repr 4294967296) tulong) :: nil))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Oand (Etempvar _esr tulong)
                               (Econst_long (Int64.repr 64) tulong) tulong)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _t'4
                  (Ecast
                    (Ebinop Oeq
                      (Ebinop Oand (Etempvar _esr tulong)
                        (Econst_long (Int64.repr 128) tulong) tulong)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'4 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'4 tint)
                (Scall None
                  (Evar set_shadow_dirty_bit (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tulong Tnil))) tvoid
                                                cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                     (Etempvar _Rd tuint) tint) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar get_shadow_ctxt (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))) tulong
                                               cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Etempvar _Rd tuint) :: nil))
                    (Sset _reg (Etempvar _t'3 tulong)))
                  (Scall None
                    (Evar set_int_gpr (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Etempvar _Rd tuint) :: (Etempvar _reg tulong) :: nil))))))
          Sskip)))).

Definition f_prep_abort := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_esr, tulong) :: (_fault_ipa, tulong) :: (_reg, tulong) ::
               (_Rd, tuint) :: (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := prep_abort_body
|}.

Definition update_exception_gp_regs_body :=
  (Ssequence
    (Sset _esr (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_shadow_ctxt (Tfunction
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tuint Tnil))) tulong
                                   cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
           (Econst_int (Int.repr 33) tuint) :: nil))
        (Sset _pstate (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))) tulong
                                     cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Econst_int (Int.repr 32) tuint) :: nil))
          (Sset _pc (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar get_exception_vector (Tfunction (Tcons tulong Tnil) tulong
                                            cc_default))
              ((Etempvar _pstate tulong) :: nil))
            (Sset _new_pc (Etempvar _t'3 tulong)))
          (Ssequence
            (Scall None
              (Evar set_shadow_ctxt (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tulong Tnil))))
                                       tvoid cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
               (Econst_int (Int.repr 35) tuint) :: (Etempvar _pc tulong) ::
               nil))
            (Ssequence
              (Scall None
                (Evar set_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tulong Tnil))))
                                         tvoid cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 32) tuint) ::
                 (Etempvar _new_pc tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar set_shadow_ctxt (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tulong Tnil)))) tvoid
                                           cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Econst_int (Int.repr 33) tuint) ::
                   (Econst_long (Int64.repr 965) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar set_shadow_ctxt (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tulong Tnil)))) tvoid
                                             cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 71) tuint) ::
                     (Etempvar _pstate tulong) :: nil))
                  (Scall None
                    (Evar set_shadow_ctxt (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tulong Tnil)))) tvoid
                                             cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 55) tuint) ::
                     (Etempvar _esr tulong) :: nil)))))))))).

Definition f_update_exception_gp_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_esr, tulong) :: (_pstate, tulong) :: (_pc, tulong) ::
               (_new_pc, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := update_exception_gp_regs_body
|}.

Definition post_handle_shadow_s2pt_fault_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_int_new_pte (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                 tulong cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
      (Sset _pte (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_int_new_level (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                     tulong cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
        (Sset _level (Etempvar _t'2 tulong)))
      (Sifthenelse (Ebinop Oeq (Etempvar _level tulong)
                     (Econst_long (Int64.repr 2) tulong) tint)
        (Scall None
          (Evar prot_and_map_vm_s2pt (Tfunction
                                        (Tcons tuint
                                          (Tcons tulong
                                            (Tcons tulong (Tcons tuint Tnil))))
                                        tvoid cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
           (Etempvar _pte tulong) :: (Econst_int (Int.repr 2) tint) :: nil))
        (Scall None
          (Evar prot_and_map_vm_s2pt (Tfunction
                                        (Tcons tuint
                                          (Tcons tulong
                                            (Tcons tulong (Tcons tuint Tnil))))
                                        tvoid cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
           (Etempvar _pte tulong) :: (Econst_int (Int.repr 3) tint) :: nil))))).

Definition f_post_handle_shadow_s2pt_fault := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pte, tulong) :: (_level, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := post_handle_shadow_s2pt_fault_body
|}.
```
