# FaultHandlerCode

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
Definition _cur_vcpuid := 5%positive.
Definition _cur_vmid := 6%positive.
Definition _end := 7%positive.
Definition _esr := 8%positive.
Definition _gfn := 9%positive.
Definition _gpa := 10%positive.
Definition _inbuf := 11%positive.
Definition _inc_exe := 12%positive.
Definition _index := 13%positive.
Definition _inowner := 14%positive.
Definition _inpfn := 15%positive.
Definition _iova := 16%positive.
Definition _kvm := 17%positive.
Definition _load_addr := 18%positive.
Definition _load_idx := 19%positive.
Definition _load_info_cnt := 20%positive.
Definition _main := 21%positive.
Definition _mapped := 22%positive.
Definition _num := 23%positive.
Definition _outbuf := 24%positive.
Definition _outowner := 25%positive.
Definition _outpfn := 26%positive.
Definition _owner := 27%positive.
Definition _pa := 28%positive.
Definition _page_count := 29%positive.
Definition _pfn := 30%positive.
Definition _pgnum := 31%positive.
Definition _pte := 32%positive.
Definition _remap := 33%positive.
Definition _remap_addr := 34%positive.
Definition _ret := 35%positive.
Definition _size := 36%positive.
Definition _start := 37%positive.
Definition _state := 38%positive.
Definition _target := 39%positive.
Definition _target_addr := 40%positive.
Definition _valid := 41%positive.
Definition _vcpu := 42%positive.
Definition _vcpu_state := 43%positive.
Definition _vcpuid := 44%positive.
Definition _vm_state := 45%positive.
Definition _vmid := 46%positive.
Definition _t'1 := 47%positive.
Definition _t'2 := 48%positive.
Definition _t'3 := 49%positive.
Definition _t'4 := 50%positive.
Definition _t'5 := 51%positive.
Definition _t'6 := 52%positive.
Definition _t'7 := 53%positive.

Definition handle_host_stage2_fault_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar read_hpfar_el2 (Tfunction Tnil tulong cc_default)) nil)
      (Sset _addr (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _addr
        (Ebinop Omul
          (Ebinop Oand (Etempvar _addr tulong)
            (Econst_long (Int64.repr 65535) tulong) tulong)
          (Econst_long (Int64.repr 256) tulong) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar read_esr_el2 (Tfunction Tnil tuint cc_default)) nil)
          (Sset _esr (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar emulate_mmio (Tfunction (Tcons tulong (Tcons tuint Tnil))
                                    tuint cc_default))
              ((Etempvar _addr tulong) :: (Etempvar _esr tuint) :: nil))
            (Sset _ret (Etempvar _t'3 tuint)))
          (Sifthenelse (Ebinop Oeq (Etempvar _ret tuint)
                         (Econst_int (Int.repr (-1)) tuint) tint)
            (Scall None
              (Evar map_page_host (Tfunction (Tcons tulong Tnil) tvoid
                                     cc_default))
              ((Etempvar _addr tulong) :: nil))
            Sskip))))).

Definition f_handle_host_stage2_fault := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_addr, tulong) :: (_esr, tuint) :: (_ret, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body := handle_host_stage2_fault_body
|}.

Definition core_handle_pvops_body :=
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
             (Econst_int (Int.repr 0) tuint) :: nil))
          (Sset _arg (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar get_shadow_ctxt (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tuint Tnil)))
                                       tulong cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
               (Econst_int (Int.repr 2) tuint) :: nil))
            (Sset _addr (Etempvar _t'4 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar get_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tuint Tnil)))
                                         tulong cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 3) tuint) :: nil))
              (Sset _size (Etempvar _t'5 tulong)))
            (Ssequence
              (Sset _ret (Econst_int (Int.repr 0) tuint))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                                 (Etempvar _vmid tuint) tint)
                    (Sset _t'6
                      (Ecast
                        (Ebinop Olt (Etempvar _vmid tuint)
                          (Econst_int (Int.repr 16) tuint) tint) tbool))
                    (Sset _t'6 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'6 tint)
                    (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                   (Econst_int (Int.repr 11) tuint) tint)
                      (Scall None
                        (Evar grant_stage2_sg_gpa (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tulong
                                                         (Tcons tulong Tnil)))
                                                     tvoid cc_default))
                        ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
                         (Etempvar _size tulong) :: nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                     (Econst_int (Int.repr 12) tuint) tint)
                        (Scall None
                          (Evar revoke_stage2_sg_gpa (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tulong
                                                            (Tcons tulong Tnil)))
                                                        tvoid cc_default))
                          ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
                           (Etempvar _size tulong) :: nil))
                        (Sset _ret (Econst_int (Int.repr 1) tuint))))
                    (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                      nil)))
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar check (Tfunction (Tcons tuint Tnil) tuint
                                   cc_default)) ((Etempvar _ret tuint) :: nil))
                  (Sreturn (Some (Etempvar _t'7 tuint))))))))))).

Definition f_core_handle_pvops := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_arg, tulong) :: (_addr, tulong) :: (_size, tulong) ::
               (_vmid, tuint) :: (_vcpuid, tuint) :: (_ret, tuint) ::
               (_t'7, tuint) :: (_t'6, tint) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := core_handle_pvops_body
|}.
```
