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
Definition _base := 2%positive.
Definition _cbndx := 3%positive.
Definition _end := 4%positive.
Definition _gfn := 5%positive.
Definition _gpa := 6%positive.
Definition _inbuf := 7%positive.
Definition _inc_exe := 8%positive.
Definition _index := 9%positive.
Definition _inowner := 10%positive.
Definition _inpfn := 11%positive.
Definition _iova := 12%positive.
Definition _kvm := 13%positive.
Definition _load_addr := 14%positive.
Definition _load_idx := 15%positive.
Definition _load_info_cnt := 16%positive.
Definition _main := 17%positive.
Definition _mapped := 18%positive.
Definition _num := 19%positive.
Definition _outbuf := 20%positive.
Definition _outowner := 21%positive.
Definition _outpfn := 22%positive.
Definition _owner := 23%positive.
Definition _pa := 24%positive.
Definition _page_count := 25%positive.
Definition _pfn := 26%positive.
Definition _pgnum := 27%positive.
Definition _pte := 28%positive.
Definition _remap := 29%positive.
Definition _remap_addr := 30%positive.
Definition _ret := 31%positive.
Definition _size := 32%positive.
Definition _start := 33%positive.
Definition _state := 34%positive.
Definition _target := 35%positive.
Definition _target_addr := 36%positive.
Definition _valid := 37%positive.
Definition _vcpu := 38%positive.
Definition _vcpu_state := 39%positive.
Definition _vcpuid := 40%positive.
Definition _vm_state := 41%positive.
Definition _vmid := 42%positive.
Definition _t'1 := 43%positive.
Definition _t'2 := 44%positive.
Definition _t'3 := 45%positive.
Definition _t'4 := 46%positive.
Definition _t'5 := 47%positive.
Definition _t'6 := 48%positive.

Definition search_load_info_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_next_load_idx (Tfunction (Tcons tuint Tnil) tuint
                                        cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _num (Etempvar _t'1 tuint)))
      (Ssequence
        (Sset _load_idx (Econst_int (Int.repr 0) tuint))
        (Ssequence
          (Sset _ret (Econst_long (Int64.repr 0) tulong))
          (Ssequence
            (Swhile
              (Ebinop Ogt (Etempvar _num tuint) (Econst_int (Int.repr 0) tuint)
                tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar get_vm_load_addr (Tfunction
                                              (Tcons tuint (Tcons tuint Tnil))
                                              tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _load_idx tuint) ::
                     nil))
                  (Sset _base (Etempvar _t'2 tulong)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar get_vm_load_size (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)) tulong
                                                cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _load_idx tuint) ::
                       nil))
                    (Sset _size (Etempvar _t'3 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar get_vm_remap_addr (Tfunction
                                                   (Tcons tuint
                                                     (Tcons tuint Tnil)) tulong
                                                   cc_default))
                        ((Etempvar _vmid tuint) ::
                         (Etempvar _load_idx tuint) :: nil))
                      (Sset _remap_addr (Etempvar _t'4 tulong)))
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _addr tulong)
                                       (Etempvar _base tulong) tint)
                          (Sset _t'5
                            (Ecast
                              (Ebinop Olt (Etempvar _addr tulong)
                                (Ebinop Oadd (Etempvar _base tulong)
                                  (Etempvar _size tulong) tulong) tint) tbool))
                          (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Sset _ret
                            (Ebinop Oadd
                              (Ebinop Osub (Etempvar _addr tulong)
                                (Etempvar _base tulong) tulong)
                              (Etempvar _remap_addr tulong) tulong))
                          Sskip))
                      (Ssequence
                        (Sset _load_idx
                          (Ebinop Oadd (Etempvar _load_idx tuint)
                            (Econst_int (Int.repr 1) tuint) tuint))
                        (Sset _num
                          (Ebinop Osub (Etempvar _num tuint)
                            (Econst_int (Int.repr 1) tuint) tuint))))))))
            (Ssequence
              (Scall None
                (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                         cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Ssequence
                (Scall (Some _t'6)
                  (Evar check64 (Tfunction (Tcons tulong Tnil) tulong
                                   cc_default))
                  ((Etempvar _ret tulong) :: nil))
                (Sreturn (Some (Etempvar _t'6 tulong)))))))))).

Definition f_search_load_info := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_base, tulong) :: (_size, tulong) ::
               (_remap_addr, tulong) :: (_num, tuint) ::
               (_load_idx, tuint) :: (_t'6, tulong) :: (_t'5, tint) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := search_load_info_body
|}.

Definition set_vcpu_active_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _vm_state (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_vcpu_state (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                    tuint cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
          (Sset _vcpu_state (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _vm_state tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Sset _t'3
                (Ecast
                  (Ebinop Oeq (Etempvar _vcpu_state tuint)
                    (Econst_int (Int.repr 2) tuint) tint) tbool))
              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'3 tint)
              (Scall None
                (Evar set_vcpu_state (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil)))
                                        tvoid cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 5) tuint) :: nil))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          (Scall None
            (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
            ((Etempvar _vmid tuint) :: nil)))))).

Definition f_set_vcpu_active := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vm_state, tuint) :: (_vcpu_state, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := set_vcpu_active_body
|}.

Definition set_vcpu_inactive_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vcpu_state (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                  tuint cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
        (Sset _vcpu_state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _vcpu_state tuint)
                       (Econst_int (Int.repr 5) tuint) tint)
          (Scall None
            (Evar set_vcpu_state (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))) tvoid
                                    cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
             (Econst_int (Int.repr 2) tuint) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_set_vcpu_inactive := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vcpu_state, tuint) :: (_t'1, tuint) :: nil);
  fn_body := set_vcpu_inactive_body
|}.

Definition register_vcpu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _vm_state (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_vcpu_state (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                    tuint cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
          (Sset _vcpu_state (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _vm_state tuint)
                           (Econst_int (Int.repr 2) tuint) tint)
              (Sset _t'4
                (Ecast
                  (Ebinop Oeq (Etempvar _vcpu_state tuint)
                    (Econst_int (Int.repr 0) tuint) tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_shared_vcpu (Tfunction
                                             (Tcons tuint (Tcons tuint Tnil))
                                             tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  (Sset _vcpu (Etempvar _t'3 tulong)))
                (Ssequence
                  (Scall None
                    (Evar set_vm_vcpu (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tulong Tnil)))
                                         tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Etempvar _vcpu tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar set_vcpu_state (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint Tnil))) tvoid
                                              cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 2) tuint) :: nil))
                    (Scall None
                      (Evar set_shadow_ctxt (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint
                                                     (Tcons tulong Tnil))))
                                               tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 45) tuint) ::
                       (Econst_long (Int64.repr (-1)) tulong) :: nil)))))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          (Scall None
            (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
            ((Etempvar _vmid tuint) :: nil)))))).

Definition f_register_vcpu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vcpu, tulong) :: (_vm_state, tuint) ::
               (_vcpu_state, tuint) :: (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := register_vcpu_body
|}.

Definition register_kvm_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar gen_vmid (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _vmid (Etempvar _t'1 tuint)))
    (Ssequence
      (Scall None
        (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Etempvar _vmid tuint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
            ((Etempvar _vmid tuint) :: nil))
          (Sset _state (Etempvar _t'2 tuint)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar get_shared_kvm (Tfunction (Tcons tuint Tnil) tulong
                                          cc_default))
                  ((Etempvar _vmid tuint) :: nil))
                (Sset _kvm (Etempvar _t'3 tulong)))
              (Ssequence
                (Scall None
                  (Evar set_vm_kvm (Tfunction
                                      (Tcons tuint (Tcons tulong Tnil)) tvoid
                                      cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _kvm tulong) :: nil))
                (Scall None
                  (Evar set_vm_state (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tvoid
                                        cc_default))
                  ((Etempvar _vmid tuint) :: (Econst_int (Int.repr 2) tuint) ::
                   nil))))
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
          (Ssequence
            (Scall None
              (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                       cc_default))
              ((Etempvar _vmid tuint) :: nil))
            (Ssequence
              (Scall (Some _t'4)
                (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sreturn (Some (Etempvar _t'4 tuint))))))))).

Definition f_register_kvm := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_kvm, tulong) :: (_vmid, tuint) :: (_state, tuint) ::
               (_t'4, tuint) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := register_kvm_body
|}.

Definition set_boot_info_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sset _load_idx (Econst_int (Int.repr 0) tuint))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                         (Econst_int (Int.repr 2) tuint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar get_vm_next_load_idx (Tfunction (Tcons tuint Tnil)
                                                tuint cc_default))
                  ((Etempvar _vmid tuint) :: nil))
                (Sset _load_idx (Etempvar _t'2 tuint)))
              (Sifthenelse (Ebinop Olt (Etempvar _load_idx tuint)
                             (Econst_int (Int.repr 5) tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar set_vm_next_load_idx (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil)) tvoid
                                                  cc_default))
                    ((Etempvar _vmid tuint) ::
                     (Ebinop Oadd (Etempvar _load_idx tuint)
                       (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                  (Ssequence
                    (Sset _page_count
                      (Ebinop Odiv
                        (Ebinop Oadd (Etempvar _size tulong)
                          (Ebinop Osub (Econst_long (Int64.repr 4096) tulong)
                            (Econst_long (Int64.repr 1) tulong) tulong) tulong)
                        (Econst_long (Int64.repr 4096) tulong) tulong))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar alloc_remap_addr (Tfunction
                                                    (Tcons tulong Tnil) tulong
                                                    cc_default))
                          ((Etempvar _page_count tulong) :: nil))
                        (Sset _remap_addr (Etempvar _t'3 tulong)))
                      (Ssequence
                        (Scall None
                          (Evar set_vm_load_addr (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil)))
                                                    tvoid cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Etempvar _load_idx tuint) ::
                           (Etempvar _load_addr tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar set_vm_load_size (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tulong Tnil)))
                                                      tvoid cc_default))
                            ((Etempvar _vmid tuint) ::
                             (Etempvar _load_idx tuint) ::
                             (Etempvar _size tulong) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar set_vm_remap_addr (Tfunction
                                                         (Tcons tuint
                                                           (Tcons tuint
                                                             (Tcons tulong
                                                               Tnil))) tvoid
                                                         cc_default))
                              ((Etempvar _vmid tuint) ::
                               (Etempvar _load_idx tuint) ::
                               (Etempvar _remap_addr tulong) :: nil))
                            (Scall None
                              (Evar set_vm_mapped_pages (Tfunction
                                                           (Tcons tuint
                                                             (Tcons tuint
                                                               (Tcons tulong
                                                                 Tnil))) tvoid
                                                           cc_default))
                              ((Etempvar _vmid tuint) ::
                               (Etempvar _load_idx tuint) ::
                               (Econst_int (Int.repr 0) tuint) :: nil))))))))
                Sskip))
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
          (Ssequence
            (Scall None
              (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                       cc_default))
              ((Etempvar _vmid tuint) :: nil))
            (Ssequence
              (Scall (Some _t'4)
                (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
                ((Etempvar _load_idx tuint) :: nil))
              (Sreturn (Some (Etempvar _t'4 tuint))))))))).

Definition f_set_boot_info := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_load_addr, tulong) :: (_size, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_page_count, tulong) :: (_remap_addr, tulong) ::
               (_state, tuint) :: (_load_idx, tuint) :: (_t'4, tuint) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := set_boot_info_body
|}.

Definition remap_vm_image_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                       (Econst_int (Int.repr 2) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_vm_next_load_idx (Tfunction (Tcons tuint Tnil) tuint
                                              cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _load_info_cnt (Etempvar _t'2 tuint)))
            (Sifthenelse (Ebinop Olt (Etempvar _load_idx tuint)
                           (Etempvar _load_info_cnt tuint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_vm_load_size (Tfunction
                                              (Tcons tuint (Tcons tuint Tnil))
                                              tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _load_idx tuint) ::
                     nil))
                  (Sset _size (Etempvar _t'3 tulong)))
                (Ssequence
                  (Sset _page_count
                    (Ebinop Odiv
                      (Ebinop Oadd (Etempvar _size tulong)
                        (Ebinop Osub (Econst_long (Int64.repr 4096) tulong)
                          (Econst_long (Int64.repr 1) tulong) tulong) tulong)
                      (Econst_long (Int64.repr 4096) tulong) tulong))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar get_vm_mapped_pages (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil))
                                                     tulong cc_default))
                        ((Etempvar _vmid tuint) ::
                         (Etempvar _load_idx tuint) :: nil))
                      (Sset _mapped (Etempvar _t'4 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar get_vm_remap_addr (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil))
                                                     tulong cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Etempvar _load_idx tuint) :: nil))
                        (Sset _remap_addr (Etempvar _t'5 tulong)))
                      (Ssequence
                        (Sset _target
                          (Ebinop Oadd (Etempvar _remap_addr tulong)
                            (Ebinop Omul (Etempvar _mapped tulong)
                              (Econst_long (Int64.repr 4096) tulong) tulong)
                            tulong))
                        (Sifthenelse (Ebinop Olt (Etempvar _mapped tulong)
                                       (Etempvar _page_count tulong) tint)
                          (Ssequence
                            (Scall None
                              (Evar map_s2pt (Tfunction
                                                (Tcons tuint
                                                  (Tcons tulong
                                                    (Tcons tuint
                                                      (Tcons tulong Tnil))))
                                                tvoid cc_default))
                              ((Econst_int (Int.repr 16) tuint) ::
                               (Etempvar _target tulong) ::
                               (Econst_long (Int64.repr 3) tulong) ::
                               (Ebinop Oor
                                 (Ebinop Omul (Etempvar _pfn tulong)
                                   (Econst_long (Int64.repr 4096) tulong)
                                   tulong)
                                 (Econst_long (Int64.repr 18014398509483859) tulong)
                                 tulong) :: nil))
                            (Scall None
                              (Evar set_vm_mapped_pages (Tfunction
                                                           (Tcons tuint
                                                             (Tcons tuint
                                                               (Tcons tulong
                                                                 Tnil))) tvoid
                                                           cc_default))
                              ((Etempvar _vmid tuint) ::
                               (Etempvar _load_idx tuint) ::
                               (Ebinop Oadd (Etempvar _mapped tulong)
                                 (Econst_long (Int64.repr 1) tulong) tulong) ::
                               nil)))
                          Sskip))))))
              Sskip))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_remap_vm_image := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: (_load_idx, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_size, tulong) :: (_page_count, tulong) ::
               (_mapped, tulong) :: (_remap_addr, tulong) ::
               (_target, tulong) :: (_state, tuint) ::
               (_load_info_cnt, tuint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := remap_vm_image_body
|}.

Definition verify_and_load_images_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                       (Econst_int (Int.repr 2) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_vm_next_load_idx (Tfunction (Tcons tuint Tnil) tuint
                                              cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _load_info_cnt (Etempvar _t'2 tuint)))
            (Ssequence
              (Sset _load_idx (Econst_int (Int.repr 0) tuint))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _load_idx tuint)
                    (Etempvar _load_info_cnt tuint) tint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar get_vm_load_addr (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil)) tulong
                                                  cc_default))
                        ((Etempvar _vmid tuint) ::
                         (Etempvar _load_idx tuint) :: nil))
                      (Sset _load_addr (Etempvar _t'3 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar get_vm_remap_addr (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil))
                                                     tulong cc_default))
                          ((Etempvar _vmid tuint) ::
                           (Etempvar _load_idx tuint) :: nil))
                        (Sset _remap_addr (Etempvar _t'4 tulong)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar get_vm_mapped_pages (Tfunction
                                                         (Tcons tuint
                                                           (Tcons tuint Tnil))
                                                         tulong cc_default))
                            ((Etempvar _vmid tuint) ::
                             (Etempvar _load_idx tuint) :: nil))
                          (Sset _mapped (Etempvar _t'5 tulong)))
                        (Ssequence
                          (Scall None
                            (Evar unmap_and_load_vm_image (Tfunction
                                                             (Tcons tuint
                                                               (Tcons tulong
                                                                 (Tcons tulong
                                                                   (Tcons
                                                                     tulong
                                                                     Tnil))))
                                                             tvoid cc_default))
                            ((Etempvar _vmid tuint) ::
                             (Etempvar _load_addr tulong) ::
                             (Etempvar _remap_addr tulong) ::
                             (Etempvar _mapped tulong) :: nil))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar verify_image (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil))
                                                      tuint cc_default))
                                ((Etempvar _vmid tuint) ::
                                 (Etempvar _remap_addr tulong) :: nil))
                              (Sset _valid (Etempvar _t'6 tuint)))
                            (Ssequence
                              (Sifthenelse (Ebinop Oeq (Etempvar _valid tuint)
                                             (Econst_int (Int.repr 0) tuint)
                                             tint)
                                (Scall None
                                  (Evar panic (Tfunction Tnil tvoid
                                                 cc_default)) nil)
                                Sskip)
                              (Sset _load_idx
                                (Ebinop Oadd (Etempvar _load_idx tuint)
                                  (Econst_int (Int.repr 1) tuint) tuint)))))))))
                (Scall None
                  (Evar set_vm_state (Tfunction
                                        (Tcons tuint (Tcons tuint Tnil)) tvoid
                                        cc_default))
                  ((Etempvar _vmid tuint) :: (Econst_int (Int.repr 3) tuint) ::
                   nil)))))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_verify_and_load_images := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_load_addr, tulong) :: (_remap_addr, tulong) ::
               (_mapped, tulong) :: (_state, tuint) ::
               (_load_info_cnt, tuint) :: (_load_idx, tuint) ::
               (_valid, tuint) :: (_t'6, tuint) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := verify_and_load_images_body
|}.

Definition alloc_smmu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                       (Etempvar _vmid tuint) tint)
          (Sset _t'2
            (Ecast
              (Ebinop Olt (Etempvar _vmid tuint)
                (Econst_int (Int.repr 16) tuint) tint) tbool))
          (Sset _t'2 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint
                                      cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _state (Etempvar _t'1 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
              Sskip))
          Sskip))
      (Ssequence
        (Scall None
          (Evar init_spt (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                            cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_alloc_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_t'2, tint) :: (_t'1, tuint) :: nil);
  fn_body := alloc_smmu_body
|}.

Definition assign_smmu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                       (Etempvar _vmid tuint) tint)
          (Sset _t'2
            (Ecast
              (Ebinop Olt (Etempvar _vmid tuint)
                (Econst_int (Int.repr 16) tuint) tint) tbool))
          (Sset _t'2 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint
                                      cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _state (Etempvar _t'1 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
              (Scall None
                (Evar assign_pfn_to_smmu (Tfunction
                                            (Tcons tuint
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _gfn tulong) ::
                 (Etempvar _pfn tulong) :: nil))))
          Sskip))
      (Scall None
        (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Etempvar _vmid tuint) :: nil)))).

Definition f_assign_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: (_gfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_t'2, tint) :: (_t'1, tuint) :: nil);
  fn_body := assign_smmu_body
|}.

Definition map_smmu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                       (Etempvar _vmid tuint) tint)
          (Sset _t'2
            (Ecast
              (Ebinop Olt (Etempvar _vmid tuint)
                (Econst_int (Int.repr 16) tuint) tint) tbool))
          (Sset _t'2 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint
                                      cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _state (Etempvar _t'1 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
              Sskip))
          Sskip))
      (Ssequence
        (Scall None
          (Evar update_smmu_page (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tulong (Tcons tulong Tnil)))))
                                    tvoid cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _cbndx tuint) ::
           (Etempvar _index tuint) :: (Etempvar _iova tulong) ::
           (Etempvar _pte tulong) :: nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_map_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_cbndx, tuint) :: (_index, tuint) ::
                (_iova, tulong) :: (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_t'2, tint) :: (_t'1, tuint) :: nil);
  fn_body := map_smmu_body
|}.

Definition clear_smmu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tuint)
                       (Etempvar _vmid tuint) tint)
          (Sset _t'2
            (Ecast
              (Ebinop Olt (Etempvar _vmid tuint)
                (Econst_int (Int.repr 16) tuint) tint) tbool))
          (Sset _t'2 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint
                                      cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _state (Etempvar _t'1 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)
              Sskip))
          Sskip))
      (Ssequence
        (Scall None
          (Evar unmap_smmu_page (Tfunction
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
           (Etempvar _iova tulong) :: nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_clear_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_cbndx, tuint) :: (_index, tuint) ::
                (_iova, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_t'2, tint) :: (_t'1, tuint) :: nil);
  fn_body := clear_smmu_body
|}.

Definition map_io_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _state (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                       (Econst_int (Int.repr 2) tuint) tint)
          (Scall None
            (Evar map_vm_io (Tfunction
                               (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))
                               tvoid cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _gpa tulong) ::
             (Etempvar _pa tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))))).

Definition f_map_io := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_gpa, tulong) :: (_pa, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, tuint) :: (_t'1, tuint) :: nil);
  fn_body := map_io_body
|}.

Definition is_inc_exe_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_inc_exe (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _inc_exe (Etempvar _t'1 tuint)))
      (Ssequence
        (Scall None
          (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Ssequence
          (Scall (Some _t'2)
            (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
            ((Etempvar _inc_exe tuint) :: nil))
          (Sreturn (Some (Etempvar _t'2 tuint))))))).

Definition f_is_inc_exe := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_inc_exe, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := is_inc_exe_body
|}.

Definition save_encrypted_vcpu_body :=
  (Ssequence
    (Scall None
      (Evar encrypt_gp_regs (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                               cc_default))
      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
    (Scall None
      (Evar encrypt_sys_regs (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                                cc_default))
      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))).

Definition f_save_encrypted_vcpu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := save_encrypted_vcpu_body
|}.

Definition load_encrypted_vcpu_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Etempvar _vmid tuint) :: nil))
        (Sset _vm_state (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_vcpu_state (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                    tuint cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
          (Sset _vcpu_state (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _vm_state tuint)
                           (Econst_int (Int.repr 2) tuint) tint)
              (Sset _t'3
                (Ecast
                  (Ebinop Oeq (Etempvar _vcpu_state tuint)
                    (Econst_int (Int.repr 2) tuint) tint) tbool))
              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'3 tint)
              (Ssequence
                (Scall None
                  (Evar decrypt_gp_regs (Tfunction
                                           (Tcons tuint (Tcons tuint Tnil))
                                           tvoid cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar decrypt_sys_regs (Tfunction
                                              (Tcons tuint (Tcons tuint Tnil))
                                              tvoid cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) :: nil))
                  (Scall None
                    (Evar set_vm_inc_exe (Tfunction
                                            (Tcons tuint (Tcons tuint Tnil))
                                            tvoid cc_default))
                    ((Etempvar _vmid tuint) ::
                     (Econst_int (Int.repr 1) tuint) :: nil))))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          (Scall None
            (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
            ((Etempvar _vmid tuint) :: nil)))))).

Definition f_load_encrypted_vcpu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vm_state, tuint) :: (_vcpu_state, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := load_encrypted_vcpu_body
|}.

Definition save_encrypt_buf_body :=
  (Ssequence
    (Sset _inpfn
      (Ebinop Odiv (Etempvar _inbuf tulong)
        (Econst_long (Int64.repr 4096) tulong) tulong))
    (Ssequence
      (Sset _outpfn
        (Ebinop Odiv (Etempvar _outbuf tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Scall None
          (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default)) nil)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
              ((Etempvar _inpfn tulong) :: nil))
            (Sset _inowner (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
                ((Etempvar _outpfn tulong) :: nil))
              (Sset _outowner (Etempvar _t'2 tuint)))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _inowner tuint)
                               (Etempvar _vmid tuint) tint)
                  (Sset _t'3
                    (Ecast
                      (Ebinop Oeq (Etempvar _outowner tuint)
                        (Econst_int (Int.repr 0) tuint) tint) tbool))
                  (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'3 tint)
                  (Scall None
                    (Evar encrypt_mem_buf (Tfunction
                                             (Tcons tuint
                                               (Tcons tulong
                                                 (Tcons tulong Tnil))) tvoid
                                             cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _inbuf tulong) ::
                     (Etempvar _outbuf tulong) :: nil))
                  (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                    nil)))
              (Scall None
                (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
                nil))))))).

Definition f_save_encrypt_buf := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_inbuf, tulong) :: (_outbuf, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_inpfn, tulong) :: (_outpfn, tulong) :: (_inowner, tuint) ::
               (_outowner, tuint) :: (_t'3, tint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := save_encrypt_buf_body
|}.

Definition load_decrypt_buf_body :=
  (Ssequence
    (Scall None
      (Evar acquire_lock_vm (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _vmid tuint) :: nil))
    (Ssequence
      (Sset _pfn
        (Ebinop Odiv (Etempvar _inbuf tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar get_vm_state (Tfunction (Tcons tuint Tnil) tuint cc_default))
            ((Etempvar _vmid tuint) :: nil))
          (Sset _state (Etempvar _t'1 tuint)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _state tuint)
                         (Econst_int (Int.repr 2) tuint) tint)
            (Ssequence
              (Scall None
                (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
                nil)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                           cc_default))
                    ((Etempvar _pfn tulong) :: nil))
                  (Sset _owner (Etempvar _t'2 tuint)))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                                 (Econst_int (Int.repr 0) tuint) tint)
                    (Ssequence
                      (Scall None
                        (Evar set_pfn_owner (Tfunction
                                               (Tcons tulong
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
                        ((Etempvar _pfn tulong) :: (Etempvar _vmid tuint) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar set_pfn_count (Tfunction
                                                 (Tcons tulong
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                          ((Etempvar _pfn tulong) ::
                           (Econst_int (Int.repr 0) tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar set_pfn_map (Tfunction
                                                 (Tcons tulong
                                                   (Tcons tulong Tnil)) tvoid
                                                 cc_default))
                            ((Etempvar _pfn tulong) ::
                             (Econst_long (Int64.repr (-1)) tulong) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar clear_pfn_host (Tfunction
                                                      (Tcons tulong Tnil) tvoid
                                                      cc_default))
                              ((Etempvar _pfn tulong) :: nil))
                            (Scall None
                              (Evar decrypt_mem_buf (Tfunction
                                                       (Tcons tuint
                                                         (Tcons tulong Tnil))
                                                       tvoid cc_default))
                              ((Etempvar _vmid tuint) ::
                               (Etempvar _inbuf tulong) :: nil))))))
                    (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                      nil))
                  (Scall None
                    (Evar release_lock_s2page (Tfunction Tnil tvoid
                                                 cc_default)) nil))))
            (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
          (Scall None
            (Evar release_lock_vm (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
            ((Etempvar _vmid tuint) :: nil)))))).

Definition f_load_decrypt_buf := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_inbuf, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pfn, tulong) :: (_state, tuint) :: (_owner, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := load_decrypt_buf_body
|}.
```
