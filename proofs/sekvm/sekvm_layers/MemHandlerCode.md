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
Definition _arg := 2%positive.
Definition _base := 3%positive.
Definition _cbndx := 4%positive.
Definition _cur_ticket := 5%positive.
Definition _cur_vcpuid := 6%positive.
Definition _cur_vmid := 7%positive.
Definition _end := 8%positive.
Definition _esr := 9%positive.
Definition _get_now := 10%positive.
Definition _gfn := 11%positive.
Definition _gpa := 12%positive.
Definition _inbuf := 13%positive.
Definition _inc_exe := 14%positive.
Definition _incr_now := 15%positive.
Definition _incr_ticket := 16%positive.
Definition _index := 17%positive.
Definition _inowner := 18%positive.
Definition _inpfn := 19%positive.
Definition _iova := 20%positive.
Definition _kvm := 21%positive.
Definition _lk := 22%positive.
Definition _load_addr := 23%positive.
Definition _load_idx := 24%positive.
Definition _load_info_cnt := 25%positive.
Definition _log_hold := 26%positive.
Definition _log_incr := 27%positive.
Definition _main := 28%positive.
Definition _mapped := 29%positive.
Definition _my_ticket := 30%positive.
Definition _num := 31%positive.
Definition _outbuf := 32%positive.
Definition _outowner := 33%positive.
Definition _outpfn := 34%positive.
Definition _owner := 35%positive.
Definition _pa := 36%positive.
Definition _paddr := 37%positive.
Definition _page_count := 38%positive.
Definition _pass_hlock := 39%positive.
Definition _pass_lock := 40%positive.
Definition _pass_qlock := 41%positive.
Definition _pfn := 42%positive.
Definition _pgnum := 43%positive.
Definition _power := 44%positive.
Definition _prot := 45%positive.
Definition _pte := 46%positive.
Definition _remap := 47%positive.
Definition _remap_addr := 48%positive.
Definition _ret := 49%positive.
Definition _size := 50%positive.
Definition _start := 51%positive.
Definition _state := 52%positive.
Definition _target := 53%positive.
Definition _target_addr := 54%positive.
Definition _valid := 55%positive.
Definition _vcpu := 56%positive.
Definition _vcpu_state := 57%positive.
Definition _vcpuid := 58%positive.
Definition _vm_state := 59%positive.
Definition _vmid := 60%positive.
Definition _wait_hlock := 61%positive.
Definition _wait_lock := 62%positive.
Definition _wait_qlock := 63%positive.
Definition _t'1 := 64%positive.

Definition clear_vm_stage2_range_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_vm_poweron (Tfunction (Tcons tuint Tnil) tuint cc_default))
        ((Etempvar _vmid tuint) :: nil))
      (Sset _power (Etempvar _t'1 tuint)))
    (Sifthenelse (Ebinop Oeq (Etempvar _power tuint)
                   (Econst_long (Int64.repr 0) tulong) tint)
      (Scall None
        (Evar clear_vm_range (Tfunction
                                (Tcons tuint
                                  (Tcons tulong (Tcons tulong Tnil))) tvoid
                                cc_default))
        ((Etempvar _vmid tuint) ::
         (Ebinop Odiv (Etempvar _start tulong)
           (Econst_long (Int64.repr 4096) tulong) tulong) ::
         (Ebinop Odiv (Etempvar _size tulong)
           (Econst_long (Int64.repr 4096) tulong) tulong) :: nil))
      Sskip)).

Definition f_clear_vm_stage2_range := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_start, tulong) :: (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_power, tuint) :: (_t'1, tuint) :: nil);
  fn_body := clear_vm_stage2_range_body
|}.

Definition el2_arm_lpae_map_body :=
  (Ssequence
    (Sset _pfn
      (Ebinop Odiv (Etempvar _paddr tulong)
        (Econst_long (Int64.repr 4096) tulong) tulong))
    (Ssequence
      (Sset _gfn
        (Ebinop Odiv (Etempvar _iova tulong)
          (Econst_long (Int64.repr 4096) tulong) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar smmu_init_pte (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                   tulong cc_default))
            ((Etempvar _prot tulong) :: (Etempvar _paddr tulong) :: nil))
          (Sset _pte (Etempvar _t'1 tulong)))
        (Ssequence
          (Scall None
            (Evar smmu_assign_page (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tulong (Tcons tulong Tnil))))
                                      tvoid cc_default))
            ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
             (Etempvar _pfn tulong) :: (Etempvar _gfn tulong) :: nil))
          (Scall None
            (Evar smmu_map_page (Tfunction
                                   (Tcons tuint
                                     (Tcons tuint
                                       (Tcons tulong (Tcons tulong Tnil))))
                                   tvoid cc_default))
            ((Etempvar _cbndx tuint) :: (Etempvar _index tuint) ::
             (Etempvar _iova tulong) :: (Etempvar _pte tulong) :: nil)))))).

Definition f_el2_arm_lpae_map := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iova, tulong) :: (_paddr, tulong) :: (_prot, tulong) ::
                (_cbndx, tuint) :: (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pfn, tulong) :: (_gfn, tulong) :: (_pte, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := el2_arm_lpae_map_body
|}.

Definition kvm_phys_addr_ioremap_body :=
  (Ssequence
    (Sset _num
      (Ebinop Odiv
        (Ebinop Oadd (Etempvar _size tulong) (Econst_int (Int.repr 4095) tint)
          tulong) (Econst_long (Int64.repr 4096) tulong) tulong))
    (Swhile
      (Ebinop Ogt (Etempvar _num tulong) (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall None
          (Evar map_io (Tfunction
                          (Tcons tuint (Tcons tulong (Tcons tulong Tnil)))
                          tvoid cc_default))
          ((Etempvar _vmid tuint) :: (Etempvar _gpa tulong) ::
           (Etempvar _pa tulong) :: nil))
        (Ssequence
          (Sset _gpa
            (Ebinop Oadd (Etempvar _gpa tulong)
              (Econst_long (Int64.repr 4096) tulong) tulong))
          (Ssequence
            (Sset _pa
              (Ebinop Oadd (Etempvar _pa tulong)
                (Econst_long (Int64.repr 4096) tulong) tulong))
            (Sset _num
              (Ebinop Osub (Etempvar _num tulong)
                (Econst_int (Int.repr 1) tint) tulong))))))).

Definition f_kvm_phys_addr_ioremap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_gpa, tulong) :: (_pa, tulong) ::
                (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_num, tulong) :: nil);
  fn_body := kvm_phys_addr_ioremap_body
|}.
```
