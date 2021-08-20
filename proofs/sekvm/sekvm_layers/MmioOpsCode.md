# MmioOpsCode

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
Definition _num_context_banks := 43%positive.
Definition _offset := 44%positive.
Definition _outbuf := 45%positive.
Definition _outowner := 46%positive.
Definition _outpfn := 47%positive.
Definition _owner := 48%positive.
Definition _pa := 49%positive.
Definition _paddr := 50%positive.
Definition _page_count := 51%positive.
Definition _pass_hlock := 52%positive.
Definition _pass_lock := 53%positive.
Definition _pass_qlock := 54%positive.
Definition _perm := 55%positive.
Definition _pfn := 56%positive.
Definition _pgnum := 57%positive.
Definition _power := 58%positive.
Definition _prot := 59%positive.
Definition _pte := 60%positive.
Definition _pte_pa := 61%positive.
Definition _remap := 62%positive.
Definition _remap_addr := 63%positive.
Definition _res := 64%positive.
Definition _ret := 65%positive.
Definition _rt := 66%positive.
Definition _size := 67%positive.
Definition _smmu_enable := 68%positive.
Definition _smmu_index := 69%positive.
Definition _start := 70%positive.
Definition _state := 71%positive.
Definition _t_vmid := 72%positive.
Definition _target := 73%positive.
Definition _target_addr := 74%positive.
Definition _target_vmid := 75%positive.
Definition _type := 76%positive.
Definition _val := 77%positive.
Definition _valid := 78%positive.
Definition _vcpu := 79%positive.
Definition _vcpu_state := 80%positive.
Definition _vcpuid := 81%positive.
Definition _vm_state := 82%positive.
Definition _vmid := 83%positive.
Definition _wait_hlock := 84%positive.
Definition _wait_lock := 85%positive.
Definition _wait_qlock := 86%positive.
Definition _write_val := 87%positive.
Definition _t'1 := 88%positive.
Definition _t'2 := 89%positive.

Definition emulate_mmio_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar is_smmu_range (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _addr tulong) :: nil))
        (Sset _ret (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _ret tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Scall None
            (Evar handle_host_mmio (Tfunction
                                      (Tcons tulong
                                        (Tcons tuint (Tcons tuint Tnil))) tvoid
                                      cc_default))
            ((Etempvar _addr tulong) :: (Etempvar _ret tuint) ::
             (Etempvar _hsr tuint) :: nil))
          Sskip)
        (Ssequence
          (Scall None
            (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Scall (Some _t'2)
              (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
              ((Etempvar _ret tuint) :: nil))
            (Sreturn (Some (Etempvar _t'2 tuint)))))))).

Definition f_emulate_mmio := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: (_hsr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := emulate_mmio_body
|}.

Definition el2_free_smmu_pgd_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_smmu_cfg_vmid (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                     tuint cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
        (Sset _vmid (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _vmid tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_vm_poweron (Tfunction (Tcons tuint Tnil) tuint
                                        cc_default))
                ((Etempvar _vmid tuint) :: nil))
              (Sset _power (Etempvar _t'2 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _power tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Scall None
                (Evar set_smmu_cfg_vmid (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tuint Tnil)))
                                           tvoid cc_default))
                ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
                 (Econst_int (Int.repr (-1)) tuint) :: nil))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          Sskip)
        (Scall None (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default))
          nil)))).

Definition f_el2_free_smmu_pgd := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_power, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := el2_free_smmu_pgd_body
|}.

Definition el2_alloc_smmu_pgd_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_smmu_num_context_banks (Tfunction (Tcons tuint Tnil) tuint
                                              cc_default))
          ((Etempvar _index tuint) :: nil))
        (Sset _num_context_banks (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _cbndx tuint)
                       (Etempvar _num_context_banks tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar get_smmu_cfg_vmid (Tfunction
                                           (Tcons tuint (Tcons tuint Tnil))
                                           tuint cc_default))
                ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
              (Sset _target_vmid (Etempvar _t'2 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _target_vmid tuint)
                           (Econst_int (Int.repr (-1)) tuint) tint)
              (Ssequence
                (Scall None
                  (Evar set_smmu_cfg_vmid (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint (Tcons tuint Tnil)))
                                             tvoid cc_default))
                  ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
                   (Etempvar _vmid tuint) :: nil))
                (Scall None
                  (Evar alloc_smmu (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))) tvoid
                                      cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _cbndx tuint) ::
                   (Etempvar _index tuint) :: nil)))
              Sskip))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Scall None (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default))
          nil)))).

Definition f_el2_alloc_smmu_pgd := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_vmid, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_target_vmid, tuint) :: (_num_context_banks, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := el2_alloc_smmu_pgd_body
|}.

Definition smmu_assign_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_smmu_cfg_vmid (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                     tuint cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
        (Sset _vmid (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _vmid tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Scall None
            (Evar assign_smmu (Tfunction
                                 (Tcons tuint
                                   (Tcons tulong (Tcons tulong Tnil))) tvoid
                                 cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _pfn tulong) ::
             (Etempvar _gfn tulong) :: nil))
          Sskip)
        (Scall None (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default))
          nil)))).

Definition f_smmu_assign_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: (_pfn, tulong) ::
                (_gfn, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_t'1, tuint) :: nil);
  fn_body := smmu_assign_page_body
|}.

Definition smmu_map_page_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_smmu_cfg_vmid (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                     tuint cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
        (Sset _vmid (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _vmid tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Scall None
            (Evar map_smmu (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tulong (Tcons tulong Tnil))))) tvoid
                              cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _cbndx tuint) ::
             (Etempvar _index tuint) :: (Etempvar _iova tulong) ::
             (Etempvar _pte tulong) :: nil))
          Sskip)
        (Scall None (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default))
          nil)))).

Definition f_smmu_map_page := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cbndx, tuint) :: (_index, tuint) :: (_iova, tulong) ::
                (_pte, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_t'1, tuint) :: nil);
  fn_body := smmu_map_page_body
|}.

Definition el2_arm_lpae_iova_to_phys_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar walk_spt (Tfunction
                          (Tcons tuint (Tcons tuint (Tcons tulong Tnil)))
                          tulong cc_default))
        ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
         (Etempvar _iova tulong) :: nil))
      (Sset _pte (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _ret
        (Ebinop Oadd
          (Ebinop Oand
            (Ebinop Oand (Etempvar _pte tulong)
              (Econst_long (Int64.repr 281474976710655) tulong) tulong)
            (Econst_long (Int64.repr 1152921504606842880) tulong) tulong)
          (Ebinop Oand (Etempvar _iova tulong)
            (Econst_int (Int.repr 4095) tint) tulong) tulong))
      (Ssequence
        (Scall (Some _t'2)
          (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _ret tulong) :: nil))
        (Sreturn (Some (Etempvar _t'2 tulong)))))).

Definition f_el2_arm_lpae_iova_to_phys := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_iova, tulong) :: (_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pte, tulong) :: (_ret, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := el2_arm_lpae_iova_to_phys_body
|}.

Definition el2_arm_lpae_clear_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_smmu (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_smmu_cfg_vmid (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                     tuint cc_default))
          ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) :: nil))
        (Sset _vmid (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _vmid tuint)
                       (Econst_int (Int.repr (-1)) tuint) tint)
          (Scall None
            (Evar clear_smmu (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tulong Tnil)))) tvoid
                                cc_default))
            ((Etempvar _vmid tuint) :: (Etempvar _cbndx tuint) ::
             (Etempvar _index tuint) :: (Etempvar _iova tulong) :: nil))
          Sskip)
        (Scall None (Evar release_lock_smmu (Tfunction Tnil tvoid cc_default))
          nil)))).

Definition f_el2_arm_lpae_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iova, tulong) :: (_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_t'1, tuint) :: nil);
  fn_body := el2_arm_lpae_clear_body
|}.
```
