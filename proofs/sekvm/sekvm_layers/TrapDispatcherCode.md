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
Definition _end := 18%positive.
Definition _esr := 19%positive.
Definition _esr_el2 := 20%positive.
Definition _exit_type := 21%positive.
Definition _fault_ipa := 22%positive.
Definition _get_now := 23%positive.
Definition _gfn := 24%positive.
Definition _gpa := 25%positive.
Definition _hsr := 26%positive.
Definition _i := 27%positive.
Definition _inbuf := 28%positive.
Definition _inc_exe := 29%positive.
Definition _incr_now := 30%positive.
Definition _incr_ticket := 31%positive.
Definition _index := 32%positive.
Definition _inowner := 33%positive.
Definition _inpfn := 34%positive.
Definition _iova := 35%positive.
Definition _is_write := 36%positive.
Definition _kvm := 37%positive.
Definition _len := 38%positive.
Definition _level := 39%positive.
Definition _lk := 40%positive.
Definition _load_addr := 41%positive.
Definition _load_idx := 42%positive.
Definition _load_info_cnt := 43%positive.
Definition _log_hold := 44%positive.
Definition _log_incr := 45%positive.
Definition _main := 46%positive.
Definition _map := 47%positive.
Definition _mapped := 48%positive.
Definition _my_ticket := 49%positive.
Definition _n := 50%positive.
Definition _next := 51%positive.
Definition _num := 52%positive.
Definition _num_context_banks := 53%positive.
Definition _offset := 54%positive.
Definition _outbuf := 55%positive.
Definition _outowner := 56%positive.
Definition _outpfn := 57%positive.
Definition _owner := 58%positive.
Definition _p_index := 59%positive.
Definition _pa := 60%positive.
Definition _paddr := 61%positive.
Definition _page_count := 62%positive.
Definition _pass_hlock := 63%positive.
Definition _pass_lock := 64%positive.
Definition _pass_qlock := 65%positive.
Definition _perm := 66%positive.
Definition _pfn := 67%positive.
Definition _pgd := 68%positive.
Definition _pgd_idx := 69%positive.
Definition _pgd_pa := 70%positive.
Definition _pgnum := 71%positive.
Definition _pmd := 72%positive.
Definition _pmd_idx := 73%positive.
Definition _pmd_pa := 74%positive.
Definition _power := 75%positive.
Definition _prot := 76%positive.
Definition _pte := 77%positive.
Definition _pte_idx := 78%positive.
Definition _pte_pa := 79%positive.
Definition _pud := 80%positive.
Definition _pud_idx := 81%positive.
Definition _pud_pa := 82%positive.
Definition _r_index := 83%positive.
Definition _reg := 84%positive.
Definition _remap := 85%positive.
Definition _remap_addr := 86%positive.
Definition _res := 87%positive.
Definition _ret := 88%positive.
Definition _ret64 := 89%positive.
Definition _rt := 90%positive.
Definition _size := 91%positive.
Definition _smmu_enable := 92%positive.
Definition _smmu_index := 93%positive.
Definition _start := 94%positive.
Definition _state := 95%positive.
Definition _t_vmid := 96%positive.
Definition _target := 97%positive.
Definition _target_addr := 98%positive.
Definition _target_vmid := 99%positive.
Definition _total_smmu := 100%positive.
Definition _ttbr := 101%positive.
Definition _ttbr_pa := 102%positive.
Definition _type := 103%positive.
Definition _val := 104%positive.
Definition _valid := 105%positive.
Definition _vcpu := 106%positive.
Definition _vcpu_state := 107%positive.
Definition _vcpuid := 108%positive.
Definition _vm_state := 109%positive.
Definition _vmid := 110%positive.
Definition _vttbr := 111%positive.
Definition _vttbr_pa := 112%positive.
Definition _wait_hlock := 113%positive.
Definition _wait_lock := 114%positive.
Definition _wait_qlock := 115%positive.
Definition _write_val := 116%positive.
Definition _t'1 := 117%positive.
Definition _t'10 := 118%positive.
Definition _t'11 := 119%positive.
Definition _t'12 := 120%positive.
Definition _t'13 := 121%positive.
Definition _t'14 := 122%positive.
Definition _t'15 := 123%positive.
Definition _t'16 := 124%positive.
Definition _t'17 := 125%positive.
Definition _t'18 := 126%positive.
Definition _t'19 := 127%positive.
Definition _t'2 := 128%positive.
Definition _t'20 := 129%positive.
Definition _t'21 := 130%positive.
Definition _t'22 := 131%positive.
Definition _t'23 := 132%positive.
Definition _t'24 := 133%positive.
Definition _t'25 := 134%positive.
Definition _t'26 := 135%positive.
Definition _t'27 := 136%positive.
Definition _t'28 := 137%positive.
Definition _t'29 := 138%positive.
Definition _t'3 := 139%positive.
Definition _t'30 := 140%positive.
Definition _t'31 := 141%positive.
Definition _t'32 := 142%positive.
Definition _t'33 := 143%positive.
Definition _t'34 := 144%positive.
Definition _t'35 := 145%positive.
Definition _t'36 := 146%positive.
Definition _t'37 := 147%positive.
Definition _t'38 := 148%positive.
Definition _t'39 := 149%positive.
Definition _t'4 := 150%positive.
Definition _t'40 := 151%positive.
Definition _t'41 := 152%positive.
Definition _t'42 := 153%positive.
Definition _t'43 := 154%positive.
Definition _t'44 := 155%positive.
Definition _t'45 := 156%positive.
Definition _t'46 := 157%positive.
Definition _t'47 := 158%positive.
Definition _t'48 := 159%positive.
Definition _t'49 := 160%positive.
Definition _t'5 := 161%positive.
Definition _t'50 := 162%positive.
Definition _t'51 := 163%positive.
Definition _t'52 := 164%positive.
Definition _t'53 := 165%positive.
Definition _t'54 := 166%positive.
Definition _t'55 := 167%positive.
Definition _t'56 := 168%positive.
Definition _t'57 := 169%positive.
Definition _t'58 := 170%positive.
Definition _t'59 := 171%positive.
Definition _t'6 := 172%positive.
Definition _t'60 := 173%positive.
Definition _t'61 := 174%positive.
Definition _t'62 := 175%positive.
Definition _t'63 := 176%positive.
Definition _t'64 := 177%positive.
Definition _t'7 := 178%positive.
Definition _t'8 := 179%positive.
Definition _t'9 := 180%positive.

Definition host_hvc_dispatcher_body :=
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
               (Econst_int (Int.repr 1) tuint) :: nil))
            (Sset _arg1 (Etempvar _t'4 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar get_shadow_ctxt (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tuint Tnil)))
                                         tulong cc_default))
                ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sset _arg2 (Etempvar _t'5 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar get_shadow_ctxt (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint (Tcons tuint Tnil)))
                                           tulong cc_default))
                  ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                   (Econst_int (Int.repr 3) tuint) :: nil))
                (Sset _arg3 (Etempvar _t'6 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar get_shadow_ctxt (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint (Tcons tuint Tnil)))
                                             tulong cc_default))
                    ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                     (Econst_int (Int.repr 4) tuint) :: nil))
                  (Sset _arg4 (Etempvar _t'7 tulong)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar get_shadow_ctxt (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))) tulong
                                               cc_default))
                      ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
                       (Econst_int (Int.repr 5) tuint) :: nil))
                    (Sset _arg5 (Etempvar _t'8 tulong)))
                  (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                 (Econst_int (Int.repr 13) tuint) tint)
                    (Scall None
                      (Evar timer_set_cntvoff (Tfunction Tnil tvoid
                                                 cc_default)) nil)
                    (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                   (Econst_int (Int.repr 14) tuint) tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Econst_int (Int.repr 0) tuint)
                                               (Etempvar _arg1 tulong) tint)
                                  (Sset _t'9
                                    (Ecast
                                      (Ebinop Olt (Etempvar _arg1 tulong)
                                        (Econst_int (Int.repr 16) tuint) tint)
                                      tbool))
                                  (Sset _t'9 (Econst_int (Int.repr 0) tint)))
                                (Sifthenelse (Etempvar _t'9 tint)
                                  (Sset _t'10
                                    (Ecast
                                      (Ebinop Ole
                                        (Econst_long (Int64.repr 0) tulong)
                                        (Etempvar _arg2 tulong) tint) tbool))
                                  (Sset _t'10 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'10 tint)
                                (Sset _t'11
                                  (Ecast
                                    (Ebinop Olt (Etempvar _arg2 tulong)
                                      (Econst_long (Int64.repr 281474976710656) tulong)
                                      tint) tbool))
                                (Sset _t'11 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'11 tint)
                              (Sset _t'12
                                (Ecast
                                  (Ebinop Ole
                                    (Econst_long (Int64.repr 0) tulong)
                                    (Etempvar _arg3 tulong) tint) tbool))
                              (Sset _t'12 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'12 tint)
                            (Sset _t'13
                              (Ecast
                                (Ebinop Olt (Etempvar _arg3 tulong)
                                  (Econst_long (Int64.repr 1099511627776) tulong)
                                  tint) tbool))
                            (Sset _t'13 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'13 tint)
                          (Scall None
                            (Evar clear_vm_stage2_range (Tfunction
                                                           (Tcons tuint
                                                             (Tcons tulong
                                                               (Tcons tulong
                                                                 Tnil))) tvoid
                                                           cc_default))
                            ((Etempvar _arg1 tulong) ::
                             (Etempvar _arg2 tulong) ::
                             (Etempvar _arg3 tulong) :: nil))
                          (Scall None
                            (Evar panic (Tfunction Tnil tvoid cc_default))
                            nil)))
                      (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                     (Econst_int (Int.repr 15) tuint) tint)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Econst_int (Int.repr 0) tuint)
                                                   (Etempvar _arg1 tulong)
                                                   tint)
                                      (Sset _t'14
                                        (Ecast
                                          (Ebinop Olt (Etempvar _arg1 tulong)
                                            (Econst_int (Int.repr 16) tuint)
                                            tint) tbool))
                                      (Sset _t'14
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sifthenelse (Etempvar _t'14 tint)
                                      (Sset _t'15
                                        (Ecast
                                          (Ebinop Ole
                                            (Econst_long (Int64.repr 0) tulong)
                                            (Etempvar _arg2 tulong) tint)
                                          tbool))
                                      (Sset _t'15
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'15 tint)
                                    (Sset _t'16
                                      (Ecast
                                        (Ebinop Olt (Etempvar _arg2 tulong)
                                          (Econst_long (Int64.repr 1099511627776) tulong)
                                          tint) tbool))
                                    (Sset _t'16 (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'16 tint)
                                  (Sset _t'17
                                    (Ecast
                                      (Ebinop Ole
                                        (Econst_long (Int64.repr 0) tulong)
                                        (Etempvar _arg3 tulong) tint) tbool))
                                  (Sset _t'17 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'17 tint)
                                (Sset _t'18
                                  (Ecast
                                    (Ebinop Olt (Etempvar _arg3 tulong)
                                      (Econst_long (Int64.repr 1099511627776) tulong)
                                      tint) tbool))
                                (Sset _t'18 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'18 tint)
                              (Sset _t'19
                                (Ecast
                                  (Ebinop Olt
                                    (Ebinop Oadd (Etempvar _arg2 tulong)
                                      (Etempvar _arg3 tulong) tulong)
                                    (Econst_long (Int64.repr 1099511627776) tulong)
                                    tint) tbool))
                              (Sset _t'19 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'19 tint)
                            (Scall None
                              (Evar set_boot_info (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tulong
                                                         (Tcons tulong Tnil)))
                                                     tuint cc_default))
                              ((Etempvar _arg1 tulong) ::
                               (Etempvar _arg2 tulong) ::
                               (Etempvar _arg3 tulong) :: nil))
                            (Scall None
                              (Evar panic (Tfunction Tnil tvoid cc_default))
                              nil)))
                        (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                       (Econst_int (Int.repr 16) tuint) tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Econst_int (Int.repr 0) tuint)
                                                   (Etempvar _arg1 tulong)
                                                   tint)
                                      (Sset _t'20
                                        (Ecast
                                          (Ebinop Olt (Etempvar _arg1 tulong)
                                            (Econst_int (Int.repr 16) tuint)
                                            tint) tbool))
                                      (Sset _t'20
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sifthenelse (Etempvar _t'20 tint)
                                      (Sset _t'21
                                        (Ecast
                                          (Ebinop Ole
                                            (Econst_long (Int64.repr 0) tulong)
                                            (Etempvar _arg2 tulong) tint)
                                          tbool))
                                      (Sset _t'21
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'21 tint)
                                    (Sset _t'22
                                      (Ecast
                                        (Ebinop Olt (Etempvar _arg2 tulong)
                                          (Econst_long (Int64.repr 268435456) tulong)
                                          tint) tbool))
                                    (Sset _t'22 (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'22 tint)
                                  (Sset _t'23
                                    (Ecast
                                      (Ebinop Ole
                                        (Econst_int (Int.repr 0) tuint)
                                        (Etempvar _arg3 tulong) tint) tbool))
                                  (Sset _t'23 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'23 tint)
                                (Sset _t'24
                                  (Ecast
                                    (Ebinop Olt (Etempvar _arg3 tulong)
                                      (Econst_int (Int.repr 5) tuint) tint)
                                    tbool))
                                (Sset _t'24 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'24 tint)
                              (Scall None
                                (Evar remap_vm_image (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tulong
                                                            (Tcons tuint Tnil)))
                                                        tvoid cc_default))
                                ((Etempvar _arg1 tulong) ::
                                 (Etempvar _arg2 tulong) ::
                                 (Etempvar _arg3 tulong) :: nil))
                              (Scall None
                                (Evar panic (Tfunction Tnil tvoid cc_default))
                                nil)))
                          (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                         (Econst_int (Int.repr 17) tuint) tint)
                            (Ssequence
                              (Sifthenelse (Ebinop Olt
                                             (Econst_int (Int.repr 0) tuint)
                                             (Etempvar _arg1 tulong) tint)
                                (Sset _t'25
                                  (Ecast
                                    (Ebinop Olt (Etempvar _arg1 tulong)
                                      (Econst_int (Int.repr 16) tuint) tint)
                                    tbool))
                                (Sset _t'25 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'25 tint)
                                (Scall None
                                  (Evar verify_and_load_images (Tfunction
                                                                  (Tcons tuint
                                                                    Tnil) tvoid
                                                                  cc_default))
                                  ((Etempvar _arg1 tulong) :: nil))
                                (Scall None
                                  (Evar panic (Tfunction Tnil tvoid
                                                 cc_default)) nil)))
                            (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                           (Econst_int (Int.repr 18) tuint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Ole
                                                   (Econst_int (Int.repr 0) tuint)
                                                   (Etempvar _arg1 tulong)
                                                   tint)
                                      (Sset _t'26
                                        (Ecast
                                          (Ebinop Olt (Etempvar _arg1 tulong)
                                            (Econst_int (Int.repr 8) tuint)
                                            tint) tbool))
                                      (Sset _t'26
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sifthenelse (Etempvar _t'26 tint)
                                      (Sset _t'27
                                        (Ecast
                                          (Ebinop Ole
                                            (Econst_int (Int.repr 0) tuint)
                                            (Etempvar _arg2 tulong) tint)
                                          tbool))
                                      (Sset _t'27
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'27 tint)
                                    (Sset _t'28
                                      (Ecast
                                        (Ebinop Olt (Etempvar _arg2 tulong)
                                          (Econst_int (Int.repr 2) tuint) tint)
                                        tbool))
                                    (Sset _t'28 (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'28 tint)
                                  (Scall None
                                    (Evar el2_free_smmu_pgd (Tfunction
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil)) tvoid
                                                               cc_default))
                                    ((Etempvar _arg1 tulong) ::
                                     (Etempvar _arg2 tulong) :: nil))
                                  (Scall None
                                    (Evar panic (Tfunction Tnil tvoid
                                                   cc_default)) nil)))
                              (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                             (Econst_int (Int.repr 19) tuint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ole
                                                         (Econst_int (Int.repr 0) tuint)
                                                         (Etempvar _arg1 tulong)
                                                         tint)
                                            (Sset _t'29
                                              (Ecast
                                                (Ebinop Olt
                                                  (Etempvar _arg1 tulong)
                                                  (Econst_int (Int.repr 8) tuint)
                                                  tint) tbool))
                                            (Sset _t'29
                                              (Econst_int (Int.repr 0) tint)))
                                          (Sifthenelse (Etempvar _t'29 tint)
                                            (Sset _t'30
                                              (Ecast
                                                (Ebinop Ole
                                                  (Econst_int (Int.repr 0) tuint)
                                                  (Etempvar _arg2 tulong) tint)
                                                tbool))
                                            (Sset _t'30
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'30 tint)
                                          (Sset _t'31
                                            (Ecast
                                              (Ebinop Olt
                                                (Etempvar _arg2 tulong)
                                                (Econst_int (Int.repr 16) tuint)
                                                tint) tbool))
                                          (Sset _t'31
                                            (Econst_int (Int.repr 0) tint))))
                                      (Sifthenelse (Etempvar _t'31 tint)
                                        (Sset _t'32
                                          (Ecast
                                            (Ebinop Ole
                                              (Econst_int (Int.repr 0) tuint)
                                              (Etempvar _arg3 tulong) tint)
                                            tbool))
                                        (Sset _t'32
                                          (Econst_int (Int.repr 0) tint))))
                                    (Sifthenelse (Etempvar _t'32 tint)
                                      (Sset _t'33
                                        (Ecast
                                          (Ebinop Olt (Etempvar _arg3 tulong)
                                            (Econst_int (Int.repr 2) tuint)
                                            tint) tbool))
                                      (Sset _t'33
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'33 tint)
                                    (Scall None
                                      (Evar el2_alloc_smmu_pgd (Tfunction
                                                                  (Tcons tuint
                                                                    (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                      ((Etempvar _arg1 tulong) ::
                                       (Etempvar _arg2 tulong) ::
                                       (Etempvar _arg3 tulong) :: nil))
                                    (Scall None
                                      (Evar panic (Tfunction Tnil tvoid
                                                     cc_default)) nil)))
                                (Sifthenelse (Ebinop Oeq (Etempvar _arg tulong)
                                               (Econst_int (Int.repr 20) tuint)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Ole
                                                                     (Econst_long (Int64.repr 0) tulong)
                                                                     (Etempvar _arg1 tulong)
                                                                     tint)
                                                        (Sset _t'34
                                                          (Ecast
                                                            (Ebinop Olt
                                                              (Etempvar _arg1 tulong)
                                                              (Econst_long (Int64.repr 1099511627776) tulong)
                                                              tint) tbool))
                                                        (Sset _t'34
                                                          (Econst_int (Int.repr 0) tint)))
                                                      (Sifthenelse (Etempvar _t'34 tint)
                                                        (Sset _t'35
                                                          (Ecast
                                                            (Ebinop Ole
                                                              (Econst_long (Int64.repr 0) tulong)
                                                              (Etempvar _arg2 tulong)
                                                              tint) tbool))
                                                        (Sset _t'35
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Etempvar _t'35 tint)
                                                      (Sset _t'36
                                                        (Ecast
                                                          (Ebinop Olt
                                                            (Etempvar _arg2 tulong)
                                                            (Econst_long (Int64.repr 1099511627776) tulong)
                                                            tint) tbool))
                                                      (Sset _t'36
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'36 tint)
                                                    (Sset _t'37
                                                      (Ecast
                                                        (Ebinop Ole
                                                          (Econst_long (Int64.repr 0) tulong)
                                                          (Etempvar _arg3 tulong)
                                                          tint) tbool))
                                                    (Sset _t'37
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'37 tint)
                                                  (Sset _t'38
                                                    (Ecast
                                                      (Ebinop Olt
                                                        (Etempvar _arg3 tulong)
                                                        (Econst_long (Int64.repr 9223372036854775807) tulong)
                                                        tint) tbool))
                                                  (Sset _t'38
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'38 tint)
                                                (Sset _t'39
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Ebinop Oand
                                                        (Ebinop Oand
                                                          (Etempvar _arg3 tulong)
                                                          (Econst_long (Int64.repr 281474976710655) tulong)
                                                          tulong)
                                                        (Econst_long (Int64.repr 1152921504606842880) tulong)
                                                        tulong)
                                                      (Econst_long (Int64.repr 0) tulong)
                                                      tint) tbool))
                                                (Sset _t'39
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'39 tint)
                                              (Sset _t'40
                                                (Ecast
                                                  (Ebinop Ole
                                                    (Econst_int (Int.repr 0) tuint)
                                                    (Etempvar _arg4 tulong)
                                                    tint) tbool))
                                              (Sset _t'40
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'40 tint)
                                            (Sset _t'41
                                              (Ecast
                                                (Ebinop Olt
                                                  (Etempvar _arg4 tulong)
                                                  (Econst_int (Int.repr 8) tuint)
                                                  tint) tbool))
                                            (Sset _t'41
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'41 tint)
                                          (Sset _t'42
                                            (Ecast
                                              (Ebinop Ole
                                                (Econst_int (Int.repr 0) tuint)
                                                (Etempvar _arg5 tulong) tint)
                                              tbool))
                                          (Sset _t'42
                                            (Econst_int (Int.repr 0) tint))))
                                      (Sifthenelse (Etempvar _t'42 tint)
                                        (Sset _t'43
                                          (Ecast
                                            (Ebinop Olt (Etempvar _arg5 tulong)
                                              (Econst_int (Int.repr 2) tuint)
                                              tint) tbool))
                                        (Sset _t'43
                                          (Econst_int (Int.repr 0) tint))))
                                    (Sifthenelse (Etempvar _t'43 tint)
                                      (Scall None
                                        (Evar el2_arm_lpae_map (Tfunction
                                                                  (Tcons tulong
                                                                    (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)))))
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _arg1 tulong) ::
                                         (Etempvar _arg2 tulong) ::
                                         (Etempvar _arg3 tulong) ::
                                         (Etempvar _arg4 tulong) ::
                                         (Etempvar _arg5 tulong) :: nil))
                                      (Scall None
                                        (Evar panic (Tfunction Tnil tvoid
                                                       cc_default)) nil)))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _arg tulong)
                                                 (Econst_int (Int.repr 21) tuint)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Ole
                                                             (Econst_long (Int64.repr 0) tulong)
                                                             (Etempvar _arg1 tulong)
                                                             tint)
                                                (Sset _t'45
                                                  (Ecast
                                                    (Ebinop Olt
                                                      (Etempvar _arg1 tulong)
                                                      (Econst_long (Int64.repr 1099511627776) tulong)
                                                      tint) tbool))
                                                (Sset _t'45
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _t'45 tint)
                                                (Sset _t'46
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Econst_int (Int.repr 0) tuint)
                                                      (Etempvar _arg2 tulong)
                                                      tint) tbool))
                                                (Sset _t'46
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'46 tint)
                                              (Sset _t'47
                                                (Ecast
                                                  (Ebinop Olt
                                                    (Etempvar _arg2 tulong)
                                                    (Econst_int (Int.repr 8) tuint)
                                                    tint) tbool))
                                              (Sset _t'47
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'47 tint)
                                            (Sset _t'48
                                              (Ecast
                                                (Ebinop Ole
                                                  (Econst_int (Int.repr 0) tuint)
                                                  (Etempvar _arg3 tulong) tint)
                                                tbool))
                                            (Sset _t'48
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'48 tint)
                                          (Sset _t'49
                                            (Ecast
                                              (Ebinop Olt
                                                (Etempvar _arg3 tulong)
                                                (Econst_int (Int.repr 2) tuint)
                                                tint) tbool))
                                          (Sset _t'49
                                            (Econst_int (Int.repr 0) tint))))
                                      (Sifthenelse (Etempvar _t'49 tint)
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'44)
                                              (Evar el2_arm_lpae_iova_to_phys 
                                              (Tfunction
                                                (Tcons tulong
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil))) tulong
                                                cc_default))
                                              ((Etempvar _arg1 tulong) ::
                                               (Etempvar _arg2 tulong) ::
                                               (Etempvar _arg3 tulong) :: nil))
                                            (Sset _ret64
                                              (Etempvar _t'44 tulong)))
                                          (Scall None
                                            (Evar set_shadow_ctxt (Tfunction
                                                                     (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))))
                                                                     tvoid
                                                                     cc_default))
                                            ((Etempvar _vmid tuint) ::
                                             (Etempvar _vcpuid tuint) ::
                                             (Econst_int (Int.repr 0) tuint) ::
                                             (Etempvar _ret64 tulong) :: nil)))
                                        (Scall None
                                          (Evar panic (Tfunction Tnil tvoid
                                                         cc_default)) nil)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _arg tulong)
                                                   (Econst_int (Int.repr 22) tuint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sifthenelse (Ebinop Ole
                                                               (Econst_long (Int64.repr 0) tulong)
                                                               (Etempvar _arg1 tulong)
                                                               tint)
                                                  (Sset _t'50
                                                    (Ecast
                                                      (Ebinop Olt
                                                        (Etempvar _arg1 tulong)
                                                        (Econst_long (Int64.repr 1099511627776) tulong)
                                                        tint) tbool))
                                                  (Sset _t'50
                                                    (Econst_int (Int.repr 0) tint)))
                                                (Sifthenelse (Etempvar _t'50 tint)
                                                  (Sset _t'51
                                                    (Ecast
                                                      (Ebinop Ole
                                                        (Econst_int (Int.repr 0) tuint)
                                                        (Etempvar _arg2 tulong)
                                                        tint) tbool))
                                                  (Sset _t'51
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'51 tint)
                                                (Sset _t'52
                                                  (Ecast
                                                    (Ebinop Olt
                                                      (Etempvar _arg2 tulong)
                                                      (Econst_int (Int.repr 8) tuint)
                                                      tint) tbool))
                                                (Sset _t'52
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'52 tint)
                                              (Sset _t'53
                                                (Ecast
                                                  (Ebinop Ole
                                                    (Econst_int (Int.repr 0) tuint)
                                                    (Etempvar _arg3 tulong)
                                                    tint) tbool))
                                              (Sset _t'53
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'53 tint)
                                            (Sset _t'54
                                              (Ecast
                                                (Ebinop Olt
                                                  (Etempvar _arg3 tulong)
                                                  (Econst_int (Int.repr 2) tuint)
                                                  tint) tbool))
                                            (Sset _t'54
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'54 tint)
                                          (Scall None
                                            (Evar el2_arm_lpae_clear (Tfunction
                                                                      (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)))
                                                                      tvoid
                                                                      cc_default))
                                            ((Etempvar _arg1 tulong) ::
                                             (Etempvar _arg2 tulong) ::
                                             (Etempvar _arg3 tulong) :: nil))
                                          (Scall None
                                            (Evar panic (Tfunction Tnil tvoid
                                                           cc_default)) nil)))
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _arg tulong)
                                                     (Econst_int (Int.repr 26) tuint)
                                                     tint)
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'55)
                                              (Evar register_kvm (Tfunction
                                                                    Tnil tuint
                                                                    cc_default))
                                              nil)
                                            (Sset _ret (Etempvar _t'55 tuint)))
                                          (Scall None
                                            (Evar set_shadow_ctxt (Tfunction
                                                                     (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))))
                                                                     tvoid
                                                                     cc_default))
                                            ((Etempvar _vmid tuint) ::
                                             (Etempvar _vcpuid tuint) ::
                                             (Econst_int (Int.repr 0) tuint) ::
                                             (Etempvar _ret tuint) :: nil)))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _arg tulong)
                                                       (Econst_int (Int.repr 27) tuint)
                                                       tint)
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Econst_int (Int.repr 0) tuint)
                                                               (Etempvar _arg1 tulong)
                                                               tint)
                                                  (Sset _t'56
                                                    (Ecast
                                                      (Ebinop Olt
                                                        (Etempvar _arg1 tulong)
                                                        (Econst_int (Int.repr 16) tuint)
                                                        tint) tbool))
                                                  (Sset _t'56
                                                    (Econst_int (Int.repr 0) tint)))
                                                (Sifthenelse (Etempvar _t'56 tint)
                                                  (Sset _t'57
                                                    (Ecast
                                                      (Ebinop Ole
                                                        (Econst_int (Int.repr 0) tuint)
                                                        (Etempvar _arg2 tulong)
                                                        tint) tbool))
                                                  (Sset _t'57
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'57 tint)
                                                (Sset _t'58
                                                  (Ecast
                                                    (Ebinop Olt
                                                      (Etempvar _arg2 tulong)
                                                      (Econst_int (Int.repr 8) tuint)
                                                      tint) tbool))
                                                (Sset _t'58
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'58 tint)
                                              (Scall None
                                                (Evar register_vcpu (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                ((Etempvar _arg1 tulong) ::
                                                 (Etempvar _arg2 tulong) ::
                                                 nil))
                                              (Scall None
                                                (Evar panic (Tfunction Tnil
                                                               tvoid
                                                               cc_default))
                                                nil)))
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _arg tulong)
                                                         (Econst_int (Int.repr 23) tuint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse (Ebinop Ole
                                                                      (Econst_int (Int.repr 0) tuint)
                                                                      (Etempvar _arg1 tulong)
                                                                      tint)
                                                          (Sset _t'59
                                                            (Ecast
                                                              (Ebinop Ole
                                                                (Etempvar _arg1 tulong)
                                                                (Econst_int (Int.repr 16) tuint)
                                                                tint) tbool))
                                                          (Sset _t'59
                                                            (Econst_int (Int.repr 0) tint)))
                                                        (Sifthenelse (Etempvar _t'59 tint)
                                                          (Sset _t'60
                                                            (Ecast
                                                              (Ebinop Ole
                                                                (Econst_long (Int64.repr 0) tulong)
                                                                (Etempvar _arg2 tulong)
                                                                tint) tbool))
                                                          (Sset _t'60
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Etempvar _t'60 tint)
                                                        (Sset _t'61
                                                          (Ecast
                                                            (Ebinop Ole
                                                              (Econst_long (Int64.repr 0) tulong)
                                                              (Etempvar _arg3 tulong)
                                                              tint) tbool))
                                                        (Sset _t'61
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Etempvar _t'61 tint)
                                                      (Sset _t'62
                                                        (Ecast
                                                          (Ebinop Ole
                                                            (Econst_long (Int64.repr 0) tulong)
                                                            (Etempvar _arg4 tulong)
                                                            tint) tbool))
                                                      (Sset _t'62
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'62 tint)
                                                    (Sset _t'63
                                                      (Ecast
                                                        (Ebinop Olt
                                                          (Ebinop Oadd
                                                            (Etempvar _arg2 tulong)
                                                            (Etempvar _arg4 tulong)
                                                            tulong)
                                                          (Econst_long (Int64.repr 281474976710656) tulong)
                                                          tint) tbool))
                                                    (Sset _t'63
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'63 tint)
                                                  (Sset _t'64
                                                    (Ecast
                                                      (Ebinop Olt
                                                        (Ebinop Oadd
                                                          (Etempvar _arg3 tulong)
                                                          (Etempvar _arg4 tulong)
                                                          tulong)
                                                        (Econst_long (Int64.repr 1099511627776) tulong)
                                                        tint) tbool))
                                                  (Sset _t'64
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'64 tint)
                                                (Scall None
                                                  (Evar kvm_phys_addr_ioremap 
                                                  (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tulong
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))))
                                                    tvoid cc_default))
                                                  ((Etempvar _arg1 tulong) ::
                                                   (Etempvar _arg2 tulong) ::
                                                   (Etempvar _arg3 tulong) ::
                                                   (Etempvar _arg4 tulong) ::
                                                   nil))
                                                (Scall None
                                                  (Evar panic (Tfunction Tnil
                                                                 tvoid
                                                                 cc_default))
                                                  nil)))
                                            Sskip))))))))))))))))))))).

Definition f_host_hvc_dispatcher := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_vcpuid, tuint) :: (_ret, tuint) ::
               (_arg, tulong) :: (_arg1, tulong) :: (_arg2, tulong) ::
               (_arg3, tulong) :: (_arg4, tulong) :: (_arg5, tulong) ::
               (_ret64, tulong) :: (_t'64, tint) :: (_t'63, tint) ::
               (_t'62, tint) :: (_t'61, tint) :: (_t'60, tint) ::
               (_t'59, tint) :: (_t'58, tint) :: (_t'57, tint) ::
               (_t'56, tint) :: (_t'55, tuint) :: (_t'54, tint) ::
               (_t'53, tint) :: (_t'52, tint) :: (_t'51, tint) ::
               (_t'50, tint) :: (_t'49, tint) :: (_t'48, tint) ::
               (_t'47, tint) :: (_t'46, tint) :: (_t'45, tint) ::
               (_t'44, tulong) :: (_t'43, tint) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tint) :: (_t'39, tint) ::
               (_t'38, tint) :: (_t'37, tint) :: (_t'36, tint) ::
               (_t'35, tint) :: (_t'34, tint) :: (_t'33, tint) ::
               (_t'32, tint) :: (_t'31, tint) :: (_t'30, tint) ::
               (_t'29, tint) :: (_t'28, tint) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tint) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tint) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := host_hvc_dispatcher_body
|}.

Definition vm_exit_dispatcher_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar get_shadow_ctxt (Tfunction
                                 (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))
                                 tulong cc_default))
        ((Etempvar _vmid tuint) :: (Etempvar _vcpuid tuint) ::
         (Econst_int (Int.repr 72) tuint) :: nil))
      (Sset _esr_el2 (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _exit_type
        (Ebinop Oand
          (Ebinop Odiv (Etempvar _esr_el2 tulong)
            (Econst_long (Int64.repr 67108864) tulong) tulong)
          (Econst_long (Int64.repr 63) tulong) tulong))
      (Ssequence
        (Sset _ret (Econst_int (Int.repr 0) tuint))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _exit_type tulong)
                         (Econst_int (Int.repr 30) tuint) tint)
            (Scall None
              (Evar core_handle_sys64 (Tfunction Tnil tvoid cc_default)) nil)
            (Sifthenelse (Ebinop Oeq (Etempvar _exit_type tulong)
                           (Econst_int (Int.repr 22) tint) tint)
              (Ssequence
                (Scall (Some _t'2)
                  (Evar core_handle_pvops (Tfunction Tnil tuint cc_default))
                  nil)
                (Sset _ret (Etempvar _t'2 tuint)))
              (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil)))
          (Ssequence
            (Scall (Some _t'3)
              (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
              ((Etempvar _ret tuint) :: nil))
            (Sreturn (Some (Etempvar _t'3 tuint)))))))).

Definition f_vm_exit_dispatcher := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_vcpuid, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_esr_el2, tulong) :: (_exit_type, tulong) :: (_ret, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body := vm_exit_dispatcher_body
|}.
```
