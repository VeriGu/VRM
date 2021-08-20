# MemManagerCode

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
Definition _count := 5%positive.
Definition _cur_ticket := 6%positive.
Definition _cur_vcpuid := 7%positive.
Definition _cur_vmid := 8%positive.
Definition _end := 9%positive.
Definition _esr := 10%positive.
Definition _get_now := 11%positive.
Definition _gfn := 12%positive.
Definition _gpa := 13%positive.
Definition _inbuf := 14%positive.
Definition _inc_exe := 15%positive.
Definition _incr_now := 16%positive.
Definition _incr_ticket := 17%positive.
Definition _index := 18%positive.
Definition _inowner := 19%positive.
Definition _inpfn := 20%positive.
Definition _iova := 21%positive.
Definition _kvm := 22%positive.
Definition _level := 23%positive.
Definition _lk := 24%positive.
Definition _load_addr := 25%positive.
Definition _load_idx := 26%positive.
Definition _load_info_cnt := 27%positive.
Definition _log_hold := 28%positive.
Definition _log_incr := 29%positive.
Definition _main := 30%positive.
Definition _map := 31%positive.
Definition _mapped := 32%positive.
Definition _my_ticket := 33%positive.
Definition _num := 34%positive.
Definition _outbuf := 35%positive.
Definition _outowner := 36%positive.
Definition _outpfn := 37%positive.
Definition _owner := 38%positive.
Definition _pa := 39%positive.
Definition _paddr := 40%positive.
Definition _page_count := 41%positive.
Definition _pass_hlock := 42%positive.
Definition _pass_lock := 43%positive.
Definition _pass_qlock := 44%positive.
Definition _perm := 45%positive.
Definition _pfn := 46%positive.
Definition _pgnum := 47%positive.
Definition _power := 48%positive.
Definition _prot := 49%positive.
Definition _pte := 50%positive.
Definition _remap := 51%positive.
Definition _remap_addr := 52%positive.
Definition _ret := 53%positive.
Definition _size := 54%positive.
Definition _start := 55%positive.
Definition _state := 56%positive.
Definition _target := 57%positive.
Definition _target_addr := 58%positive.
Definition _valid := 59%positive.
Definition _vcpu := 60%positive.
Definition _vcpu_state := 61%positive.
Definition _vcpuid := 62%positive.
Definition _vm_state := 63%positive.
Definition _vmid := 64%positive.
Definition _wait_hlock := 65%positive.
Definition _wait_lock := 66%positive.
Definition _wait_qlock := 67%positive.
Definition _t'1 := 68%positive.
Definition _t'2 := 69%positive.
Definition _t'3 := 70%positive.
Definition _t'4 := 71%positive.

Definition map_page_host_body :=
  (Ssequence
    (Sset _pfn
      (Ebinop Odiv (Etempvar _addr tulong)
        (Econst_long (Int64.repr 4096) tulong) tulong))
    (Ssequence
      (Sset _pte (Econst_long (Int64.repr 0) tulong))
      (Ssequence
        (Scall None
          (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default)) nil)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
              ((Etempvar _pfn tulong) :: nil))
            (Sset _owner (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
                ((Etempvar _pfn tulong) :: nil))
              (Sset _count (Etempvar _t'2 tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                             (Econst_int (Int.repr (-1)) tuint) tint)
                (Ssequence
                  (Sset _perm
                    (Ebinop Oor
                      (Econst_long (Int64.repr 18014398509483847) tulong)
                      (Econst_long (Int64.repr 192) tulong) tulong))
                  (Ssequence
                    (Sset _pte
                      (Ebinop Oor
                        (Ebinop Omul (Etempvar _pfn tulong)
                          (Econst_long (Int64.repr 4096) tulong) tulong)
                        (Etempvar _perm tulong) tulong))
                    (Scall None
                      (Evar map_s2pt (Tfunction
                                        (Tcons tuint
                                          (Tcons tulong
                                            (Tcons tuint (Tcons tulong Tnil))))
                                        tvoid cc_default))
                      ((Econst_int (Int.repr 0) tuint) ::
                       (Etempvar _addr tulong) ::
                       (Econst_int (Int.repr 3) tuint) ::
                       (Etempvar _pte tulong) :: nil))))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                                 (Econst_int (Int.repr 0) tuint) tint)
                    (Sset _t'3 (Econst_int (Int.repr 1) tint))
                    (Sset _t'3
                      (Ecast
                        (Ebinop Ogt (Etempvar _count tuint)
                          (Econst_int (Int.repr 0) tuint) tint) tbool)))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Ssequence
                      (Sset _perm (Econst_long (Int64.repr 4095) tulong))
                      (Ssequence
                        (Sset _pte
                          (Ebinop Oor
                            (Ebinop Omul (Etempvar _pfn tulong)
                              (Econst_long (Int64.repr 4096) tulong) tulong)
                            (Etempvar _perm tulong) tulong))
                        (Scall None
                          (Evar map_s2pt (Tfunction
                                            (Tcons tuint
                                              (Tcons tulong
                                                (Tcons tuint
                                                  (Tcons tulong Tnil)))) tvoid
                                            cc_default))
                          ((Econst_int (Int.repr 0) tuint) ::
                           (Etempvar _addr tulong) ::
                           (Econst_int (Int.repr 3) tuint) ::
                           (Etempvar _pte tulong) :: nil))))
                    (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                      nil))))
              (Scall None
                (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
                nil))))))).

Definition f_map_page_host := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pfn, tulong) :: (_pte, tulong) :: (_perm, tulong) ::
               (_owner, tuint) :: (_count, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := map_page_host_body
|}.

Definition clear_vm_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _pfn tulong) :: nil))
        (Sset _owner (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint) (Etempvar _vmid tuint)
                       tint)
          (Ssequence
            (Scall None
              (Evar clear_pfn_host (Tfunction (Tcons tulong Tnil) tvoid
                                      cc_default))
              ((Etempvar _pfn tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar set_pfn_owner (Tfunction
                                       (Tcons tulong (Tcons tuint Tnil)) tvoid
                                       cc_default))
                ((Etempvar _pfn tulong) :: (Econst_int (Int.repr 0) tuint) ::
                 nil))
              (Ssequence
                (Scall None
                  (Evar set_pfn_count (Tfunction
                                         (Tcons tulong (Tcons tuint Tnil))
                                         tvoid cc_default))
                  ((Etempvar _pfn tulong) :: (Econst_int (Int.repr 0) tuint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar set_pfn_map (Tfunction
                                         (Tcons tulong (Tcons tulong Tnil))
                                         tvoid cc_default))
                    ((Etempvar _pfn tulong) ::
                     (Ebinop Oadd (Etempvar _pfn tulong)
                       (Econst_long (Int64.repr 1000000000) tulong) tulong) ::
                     nil))
                  (Scall None
                    (Evar clear_phys_page (Tfunction (Tcons tulong Tnil) tvoid
                                             cc_default))
                    ((Etempvar _pfn tulong) :: nil))))))
          Sskip)
        (Scall None
          (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default)) nil)))).

Definition f_clear_vm_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_owner, tuint) :: (_t'1, tuint) :: nil);
  fn_body := clear_vm_page_body
|}.

Definition assign_pfn_to_vm_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _pfn tulong) :: nil))
        (Sset _owner (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
            ((Etempvar _pfn tulong) :: nil))
          (Sset _count (Etempvar _t'2 tuint)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Ssequence
                (Scall None
                  (Evar clear_pfn_host (Tfunction (Tcons tulong Tnil) tvoid
                                          cc_default))
                  ((Etempvar _pfn tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar set_pfn_owner (Tfunction
                                           (Tcons tulong (Tcons tuint Tnil))
                                           tvoid cc_default))
                    ((Etempvar _pfn tulong) :: (Etempvar _vmid tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar set_pfn_map (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           tvoid cc_default))
                      ((Etempvar _pfn tulong) :: (Etempvar _gfn tulong) :: nil))
                    (Scall None
                      (Evar fetch_from_doracle (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tulong
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) ::
                       (Econst_long (Int64.repr 1) tulong) :: nil)))))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                           (Etempvar _vmid tuint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_pfn_map (Tfunction (Tcons tulong Tnil) tulong
                                         cc_default))
                    ((Etempvar _pfn tulong) :: nil))
                  (Sset _map (Etempvar _t'3 tulong)))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _map tulong)
                                 (Econst_long (Int64.repr (-1)) tulong) tint)
                    (Sset _t'4 (Econst_int (Int.repr 1) tint))
                    (Sset _t'4
                      (Ecast
                        (Ebinop Oeq (Etempvar _gfn tulong)
                          (Etempvar _map tulong) tint) tbool)))
                  (Sifthenelse (Etempvar _t'4 tint)
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _map tulong)
                                     (Econst_long (Int64.repr (-1)) tulong)
                                     tint)
                        (Scall None
                          (Evar set_pfn_map (Tfunction
                                               (Tcons tulong
                                                 (Tcons tulong Tnil)) tvoid
                                               cc_default))
                          ((Etempvar _pfn tulong) :: (Etempvar _gfn tulong) ::
                           nil))
                        Sskip)
                      (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                                     (Econst_int (Int.repr (-1)) tuint) tint)
                        (Scall None
                          (Evar set_pfn_count (Tfunction
                                                 (Tcons tulong
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                          ((Etempvar _pfn tulong) ::
                           (Econst_int (Int.repr 0) tuint) :: nil))
                        Sskip))
                    (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                      nil))))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          (Scall None
            (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default)) nil))))).

Definition f_assign_pfn_to_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_gfn, tulong) :: (_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, tulong) :: (_owner, tuint) :: (_count, tuint) ::
               (_t'4, tint) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := assign_pfn_to_vm_body
|}.

Definition map_pfn_vm_body :=
  (Ssequence
    (Sset _paddr
      (Ebinop Oand
        (Ebinop Oand (Etempvar _pte tulong)
          (Econst_long (Int64.repr 281474976710655) tulong) tulong)
        (Econst_long (Int64.repr 1152921504606842880) tulong) tulong))
    (Ssequence
      (Sset _pfn
        (Ebinop Odiv (Etempvar _paddr tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Sset _perm (Econst_long (Int64.repr 4095) tulong))
        (Sifthenelse (Ebinop Oeq (Etempvar _level tuint)
                       (Econst_int (Int.repr 2) tuint) tint)
          (Ssequence
            (Sset _pte
              (Ebinop Oor (Etempvar _paddr tulong) (Etempvar _perm tulong)
                tulong))
            (Ssequence
              (Sset _pte
                (Ebinop Oand (Etempvar _pte tulong)
                  (Econst_long (Int64.repr (-3)) tulong) tulong))
              (Scall None
                (Evar map_s2pt (Tfunction
                                  (Tcons tuint
                                    (Tcons tulong
                                      (Tcons tuint (Tcons tulong Tnil)))) tvoid
                                  cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
                 (Econst_int (Int.repr 2) tint) :: (Etempvar _pte tulong) ::
                 nil))))
          (Ssequence
            (Sset _pte
              (Ebinop Oor (Etempvar _paddr tulong) (Etempvar _perm tulong)
                tulong))
            (Scall None
              (Evar map_s2pt (Tfunction
                                (Tcons tuint
                                  (Tcons tulong
                                    (Tcons tuint (Tcons tulong Tnil)))) tvoid
                                cc_default))
              ((Etempvar _vmid tuint) :: (Etempvar _addr tulong) ::
               (Econst_int (Int.repr 3) tuint) :: (Etempvar _pte tulong) ::
               nil))))))).

Definition f_map_pfn_vm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_addr, tulong) :: (_pte, tulong) ::
                (_level, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_paddr, tulong) :: (_pfn, tulong) :: (_perm, tulong) :: nil);
  fn_body := map_pfn_vm_body
|}.

Definition map_vm_io_body :=
  (Ssequence
    (Sset _gfn
      (Ebinop Odiv (Etempvar _gpa tulong)
        (Econst_long (Int64.repr 4096) tulong) tulong))
    (Ssequence
      (Sset _pfn
        (Ebinop Odiv (Etempvar _pa tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Sset _pte
          (Ebinop Oor
            (Ebinop Oand
              (Ebinop Oand (Etempvar _pa tulong)
                (Econst_long (Int64.repr 281474976710655) tulong) tulong)
              (Econst_long (Int64.repr 1152921504606842880) tulong) tulong)
            (Ebinop Oor (Econst_long (Int64.repr 18014398509483847) tulong)
              (Econst_long (Int64.repr 192) tulong) tulong) tulong))
        (Ssequence
          (Scall None
            (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
                ((Etempvar _pfn tulong) :: nil))
              (Sset _owner (Etempvar _t'1 tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                             (Econst_int (Int.repr (-1)) tuint) tint)
                (Scall None
                  (Evar map_s2pt (Tfunction
                                    (Tcons tuint
                                      (Tcons tulong
                                        (Tcons tuint (Tcons tulong Tnil))))
                                    tvoid cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _gpa tulong) ::
                   (Econst_int (Int.repr 3) tuint) :: (Etempvar _pte tulong) ::
                   nil))
                Sskip)
              (Scall None
                (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
                nil))))))).

Definition f_map_vm_io := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_gpa, tulong) :: (_pa, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_gfn, tulong) :: (_pfn, tulong) :: (_pte, tulong) ::
               (_owner, tuint) :: (_t'1, tuint) :: nil);
  fn_body := map_vm_io_body
|}.

Definition grant_vm_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _pfn tulong) :: nil))
        (Sset _owner (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
            ((Etempvar _pfn tulong) :: nil))
          (Sset _count (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                           (Etempvar _vmid tuint) tint)
              (Sset _t'3
                (Ecast
                  (Ebinop Olt (Etempvar _count tuint)
                    (Econst_int (Int.repr 100) tuint) tint) tbool))
              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'3 tint)
              (Scall None
                (Evar set_pfn_count (Tfunction
                                       (Tcons tulong (Tcons tuint Tnil)) tvoid
                                       cc_default))
                ((Etempvar _pfn tulong) ::
                 (Ebinop Oadd (Etempvar _count tuint)
                   (Econst_int (Int.repr 1) tuint) tuint) :: nil))
              Sskip))
          (Scall None
            (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default)) nil))))).

Definition f_grant_vm_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_owner, tuint) :: (_count, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := grant_vm_page_body
|}.

Definition revoke_vm_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _pfn tulong) :: nil))
        (Sset _owner (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
            ((Etempvar _pfn tulong) :: nil))
          (Sset _count (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                           (Etempvar _vmid tuint) tint)
              (Sset _t'3
                (Ecast
                  (Ebinop Ogt (Etempvar _count tuint)
                    (Econst_int (Int.repr 0) tuint) tint) tbool))
              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'3 tint)
              (Ssequence
                (Scall None
                  (Evar set_pfn_count (Tfunction
                                         (Tcons tulong (Tcons tuint Tnil))
                                         tvoid cc_default))
                  ((Etempvar _pfn tulong) ::
                   (Ebinop Osub (Etempvar _count tuint)
                     (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                               (Econst_int (Int.repr 1) tuint) tint)
                  (Ssequence
                    (Scall None
                      (Evar clear_pfn_host (Tfunction (Tcons tulong Tnil)
                                              tvoid cc_default))
                      ((Etempvar _pfn tulong) :: nil))
                    (Scall None
                      (Evar fetch_from_doracle (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tulong
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) ::
                       (Econst_long (Int64.repr 1) tulong) :: nil)))
                  Sskip))
              Sskip))
          (Scall None
            (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default)) nil))))).

Definition f_revoke_vm_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_owner, tuint) :: (_count, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := revoke_vm_page_body
|}.

Definition assign_pfn_to_smmu_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _pfn tulong) :: nil))
        (Sset _owner (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
            ((Etempvar _pfn tulong) :: nil))
          (Sset _count (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar get_pfn_map (Tfunction (Tcons tulong Tnil) tulong
                                   cc_default))
              ((Etempvar _pfn tulong) :: nil))
            (Sset _map (Etempvar _t'3 tulong)))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                             (Econst_int (Int.repr 0) tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar clear_pfn_host (Tfunction (Tcons tulong Tnil) tvoid
                                            cc_default))
                    ((Etempvar _pfn tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar set_pfn_owner (Tfunction
                                             (Tcons tulong (Tcons tuint Tnil))
                                             tvoid cc_default))
                      ((Etempvar _pfn tulong) :: (Etempvar _vmid tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar set_pfn_map (Tfunction
                                             (Tcons tulong (Tcons tulong Tnil))
                                             tvoid cc_default))
                        ((Etempvar _pfn tulong) :: (Etempvar _gfn tulong) ::
                         nil))
                      (Scall None
                        (Evar set_pfn_count (Tfunction
                                               (Tcons tulong
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
                        ((Etempvar _pfn tulong) ::
                         (Econst_int (Int.repr (-1)) tuint) :: nil)))))
                (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                  nil))
              (Sifthenelse (Ebinop One (Etempvar _owner tuint)
                             (Etempvar _vmid tuint) tint)
                (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                  nil)
                Sskip))
            (Scall None
              (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
              nil)))))).

Definition f_assign_pfn_to_smmu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_gfn, tulong) :: (_pfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, tulong) :: (_owner, tuint) :: (_count, tuint) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := assign_pfn_to_smmu_body
|}.

Definition update_smmu_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Sset _pfn
        (Ebinop Odiv
          (Ebinop Oand
            (Ebinop Oand (Etempvar _pte tulong)
              (Econst_long (Int64.repr 281474976710655) tulong) tulong)
            (Econst_long (Int64.repr 1152921504606842880) tulong) tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Sset _gfn
          (Ebinop Odiv (Etempvar _iova tulong)
            (Econst_long (Int64.repr 4096) tulong) tulong))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar get_pfn_owner (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
              ((Etempvar _pfn tulong) :: nil))
            (Sset _owner (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_pfn_map (Tfunction (Tcons tulong Tnil) tulong
                                     cc_default))
                ((Etempvar _pfn tulong) :: nil))
              (Sset _map (Etempvar _t'2 tulong)))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _vmid tuint)
                               (Etempvar _owner tuint) tint)
                  (Sset _t'4
                    (Ecast
                      (Ebinop Oeq (Etempvar _gfn tulong) (Etempvar _map tulong)
                        tint) tbool))
                  (Sset _t'4 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'4 tint)
                  (Ssequence
                    (Scall None
                      (Evar map_spt (Tfunction
                                       (Tcons tuint
                                         (Tcons tuint
                                           (Tcons tulong (Tcons tulong Tnil))))
                                       tvoid cc_default))
                      ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
                       (Etempvar _iova tulong) :: (Etempvar _pte tulong) ::
                       nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _owner tuint)
                                   (Econst_int (Int.repr 0) tuint) tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Evar get_pfn_count (Tfunction (Tcons tulong Tnil)
                                                   tuint cc_default))
                            ((Etempvar _pfn tulong) :: nil))
                          (Sset _count (Etempvar _t'3 tuint)))
                        (Sifthenelse (Ebinop Olt (Etempvar _count tuint)
                                       (Econst_int (Int.repr 16) tuint) tint)
                          (Scall None
                            (Evar set_pfn_count (Tfunction
                                                   (Tcons tulong
                                                     (Tcons tuint Tnil)) tvoid
                                                   cc_default))
                            ((Etempvar _pfn tulong) ::
                             (Ebinop Oadd (Etempvar _count tuint)
                               (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                          Sskip))
                      Sskip))
                  (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                    nil)))
              (Scall None
                (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
                nil))))))).

Definition f_update_smmu_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_cbndx, tuint) :: (_index, tuint) ::
                (_iova, tulong) :: (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pfn, tulong) :: (_gfn, tulong) :: (_map, tulong) ::
               (_owner, tuint) :: (_count, tuint) :: (_t'4, tint) ::
               (_t'3, tuint) :: (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body := update_smmu_page_body
|}.

Definition unmap_smmu_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_s2page (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar unmap_spt (Tfunction
                             (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))
                             tulong cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
           (Etempvar _iova tulong) :: nil))
        (Sset _pte (Etempvar _t'1 tulong)))
      (Ssequence
        (Sset _pfn
          (Ebinop Odiv
            (Ebinop Oand
              (Ebinop Oand (Etempvar _pte tulong)
                (Econst_long (Int64.repr 281474976710655) tulong) tulong)
              (Econst_long (Int64.repr 1152921504606842880) tulong) tulong)
            (Econst_long (Int64.repr 4096) tulong) tulong))
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
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar get_pfn_count (Tfunction (Tcons tulong Tnil) tuint
                                           cc_default))
                    ((Etempvar _pfn tulong) :: nil))
                  (Sset _count (Etempvar _t'3 tuint)))
                (Sifthenelse (Ebinop Ogt (Etempvar _count tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Scall None
                    (Evar set_pfn_count (Tfunction
                                           (Tcons tulong (Tcons tuint Tnil))
                                           tvoid cc_default))
                    ((Etempvar _pfn tulong) ::
                     (Ebinop Osub (Etempvar _count tuint)
                       (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                  Sskip))
              Sskip)
            (Scall None
              (Evar release_lock_s2page (Tfunction Tnil tvoid cc_default))
              nil)))))).

Definition f_unmap_smmu_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: (_iova, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pte, tulong) :: (_pfn, tulong) :: (_owner, tuint) ::
               (_count, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tulong) :: nil);
  fn_body := unmap_smmu_page_body
|}.
```
