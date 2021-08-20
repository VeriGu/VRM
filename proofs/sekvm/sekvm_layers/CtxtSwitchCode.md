# CtxtSwitchCode

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
Definition _base := 2%positive.
Definition _cbndx := 3%positive.
Definition _cur_vcpuid := 4%positive.
Definition _cur_vmid := 5%positive.
Definition _end := 6%positive.
Definition _gfn := 7%positive.
Definition _gpa := 8%positive.
Definition _inbuf := 9%positive.
Definition _inc_exe := 10%positive.
Definition _index := 11%positive.
Definition _inowner := 12%positive.
Definition _inpfn := 13%positive.
Definition _iova := 14%positive.
Definition _kvm := 15%positive.
Definition _load_addr := 16%positive.
Definition _load_idx := 17%positive.
Definition _load_info_cnt := 18%positive.
Definition _main := 19%positive.
Definition _mapped := 20%positive.
Definition _num := 21%positive.
Definition _outbuf := 22%positive.
Definition _outowner := 23%positive.
Definition _outpfn := 24%positive.
Definition _owner := 25%positive.
Definition _pa := 26%positive.
Definition _page_count := 27%positive.
Definition _pfn := 28%positive.
Definition _pgnum := 29%positive.
Definition _pte := 30%positive.
Definition _remap := 31%positive.
Definition _remap_addr := 32%positive.
Definition _ret := 33%positive.
Definition _size := 34%positive.
Definition _start := 35%positive.
Definition _state := 36%positive.
Definition _target := 37%positive.
Definition _target_addr := 38%positive.
Definition _valid := 39%positive.
Definition _vcpu := 40%positive.
Definition _vcpu_state := 41%positive.
Definition _vcpuid := 42%positive.
Definition _vm_state := 43%positive.
Definition _vmid := 44%positive.
Definition _t'1 := 45%positive.
Definition _t'2 := 46%positive.
Definition _t'3 := 47%positive.
Definition _t'4 := 48%positive.
Definition _t'5 := 49%positive.
Definition _t'6 := 50%positive.

Definition save_host_body :=
  (Ssequence
    (Scall None (Evar save_sysregs (Tfunction Tnil tvoid cc_default)) nil)
    (Scall None (Evar fpsimd_save_state (Tfunction Tnil tvoid cc_default))
      nil)).

Definition f_save_host := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := save_host_body
|}.

Definition restore_host_body :=
  (Ssequence
    (Scall None
      (Evar set_per_cpu (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                           cc_default))
      ((Econst_int (Int.repr 0) tuint) :: (Econst_int (Int.repr 0) tuint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar host_el2_restore_state (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
        (Scall None (Evar restore_sysregs (Tfunction Tnil tvoid cc_default))
          nil)
        (Scall None
          (Evar fpsimd_restore_state (Tfunction Tnil tvoid cc_default)) nil)))).

Definition f_restore_host := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body := restore_host_body
|}.

Definition save_vm_body :=
  (Ssequence
    (Scall None (Evar save_sysregs (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None (Evar fpsimd_save_state (Tfunction Tnil tvoid cc_default))
        nil)
      (Ssequence
        (Scall None (Evar deactivate_traps (Tfunction Tnil tvoid cc_default))
          nil)
        (Ssequence
          (Scall None
            (Evar timer_enable_traps (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Scall None
              (Evar save_shadow_kvm_regs (Tfunction Tnil tvoid cc_default))
              nil)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar get_cur_vmid (Tfunction Tnil tuint cc_default)) nil)
                (Sset _vmid (Etempvar _t'1 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default))
                    nil)
                  (Sset _vcpuid (Etempvar _t'2 tuint)))
                (Scall None
                  (Evar set_vcpu_inactive (Tfunction
                                             (Tcons tuint (Tcons tuint Tnil))
                                             tvoid cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))))))))).

Definition f_save_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_vcpuid, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := save_vm_body
|}.

Definition restore_vm_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar get_cur_vmid (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _cur_vmid (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar get_cur_vcpuid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _cur_vcpuid (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar get_shadow_ctxt (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))) tulong
                                     cc_default))
            ((Etempvar _cur_vmid tuint) :: (Etempvar _cur_vcpuid tuint) ::
             (Econst_int (Int.repr 0) tuint) :: nil))
          (Sset _vmid (Etempvar _t'3 tulong)))
        (Ssequence
          (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                         (Etempvar _vmid tulong) tint)
            (Sset _t'6
              (Ecast
                (Ebinop Olt (Etempvar _vmid tulong)
                  (Econst_int (Int.repr 16) tuint) tint) tbool))
            (Sset _t'6 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'6 tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar get_int_run_vcpuid (Tfunction (Tcons tuint Tnil)
                                              tulong cc_default))
                  ((Etempvar _vmid tulong) :: nil))
                (Sset _vcpuid (Etempvar _t'4 tulong)))
              (Ssequence
                (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tuint)
                               (Etempvar _vcpuid tulong) tint)
                  (Sset _t'5
                    (Ecast
                      (Ebinop Olt (Etempvar _vmid tulong)
                        (Econst_int (Int.repr 8) tuint) tint) tbool))
                  (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'5 tint)
                  (Ssequence
                    (Scall None
                      (Evar set_per_cpu (Tfunction
                                           (Tcons tuint (Tcons tuint Tnil))
                                           tvoid cc_default))
                      ((Etempvar _vmid tulong) :: (Etempvar _vcpuid tulong) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar set_vcpu_active (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                        ((Etempvar _vmid tulong) ::
                         (Etempvar _vcpuid tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar restore_shadow_kvm_regs (Tfunction Tnil tvoid
                                                           cc_default)) nil)
                        (Ssequence
                          (Scall None
                            (Evar vm_el2_restore_state (Tfunction Tnil tvoid
                                                          cc_default)) nil)
                          (Ssequence
                            (Scall None
                              (Evar timer_enable_traps (Tfunction Tnil tvoid
                                                          cc_default)) nil)
                            (Ssequence
                              (Scall None
                                (Evar activate_traps (Tfunction Tnil tvoid
                                                        cc_default)) nil)
                              (Ssequence
                                (Scall None
                                  (Evar restore_sysregs (Tfunction Tnil tvoid
                                                           cc_default)) nil)
                                (Scall None
                                  (Evar fpsimd_restore_state (Tfunction Tnil
                                                                tvoid
                                                                cc_default))
                                  nil))))))))
                  (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                    nil))))
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))))).

Definition f_restore_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_vmid, tulong) :: (_vcpuid, tulong) :: (_cur_vmid, tuint) ::
               (_cur_vcpuid, tuint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := restore_vm_body
|}.
```
