# BootAuxCode

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
Definition _end := 1%positive.
Definition _gfn := 2%positive.
Definition _main := 3%positive.
Definition _num := 4%positive.
Definition _pfn := 5%positive.
Definition _pte := 6%positive.
Definition _remap_addr := 7%positive.
Definition _start := 8%positive.
Definition _target_addr := 9%positive.
Definition _vmid := 10%positive.
Definition _t'1 := 11%positive.

Definition unmap_and_load_vm_image_body :=
  (Ssequence
    (Sset _start
      (Ebinop Omul
        (Ebinop Odiv (Etempvar _target_addr tulong)
          (Econst_long (Int64.repr 2097152) tulong) tulong)
        (Econst_long (Int64.repr 2097152) tulong) tulong))
    (Ssequence
      (Sset _end
        (Ebinop Oadd (Etempvar _target_addr tulong)
          (Ebinop Omul (Etempvar _num tulong)
            (Econst_long (Int64.repr 4096) tulong) tulong) tulong))
      (Ssequence
        (Sset _num
          (Ebinop Odiv
            (Ebinop Oadd
              (Ebinop Osub (Etempvar _end tulong) (Etempvar _start tulong)
                tulong) (Econst_int (Int.repr 2097151) tint) tulong)
            (Econst_long (Int64.repr 2097152) tulong) tulong))
        (Swhile
          (Ebinop Ogt (Etempvar _num tulong)
            (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar walk_s2pt (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                   tulong cc_default))
                ((Econst_int (Int.repr 16) tuint) ::
                 (Etempvar _remap_addr tulong) :: nil))
              (Sset _pte (Etempvar _t'1 tulong)))
            (Ssequence
              (Sset _pfn
                (Ebinop Omul
                  (Ebinop Odiv
                    (Ebinop Oand
                      (Ebinop Oand (Etempvar _pte tulong)
                        (Econst_long (Int64.repr 281474976710655) tulong)
                        tulong)
                      (Econst_long (Int64.repr 1152921504606842880) tulong)
                      tulong) (Econst_long (Int64.repr 2097152) tulong) tulong)
                  (Econst_long (Int64.repr 512) tulong) tulong))
              (Ssequence
                (Sset _gfn
                  (Ebinop Odiv (Etempvar _start tulong)
                    (Econst_long (Int64.repr 4096) tulong) tulong))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _pfn tulong)
                                 (Econst_long (Int64.repr 0) tulong) tint)
                    (Scall None (Evar panic (Tfunction Tnil tvoid cc_default))
                      nil)
                    (Scall None
                      (Evar prot_and_map_vm_s2pt (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tulong
                                                        (Tcons tulong
                                                          (Tcons tuint Tnil))))
                                                    tvoid cc_default))
                      ((Etempvar _vmid tuint) ::
                       (Ebinop Omul (Etempvar _gfn tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong) ::
                       (Ebinop Omul (Etempvar _pfn tulong)
                         (Econst_long (Int64.repr 4096) tulong) tulong) ::
                       (Econst_int (Int.repr 2) tuint) :: nil)))
                  (Ssequence
                    (Sset _start
                      (Ebinop Oadd (Etempvar _start tulong)
                        (Econst_long (Int64.repr 2097152) tulong) tulong))
                    (Ssequence
                      (Sset _remap_addr
                        (Ebinop Oadd (Etempvar _remap_addr tulong)
                          (Ebinop Osub (Etempvar _start tulong)
                            (Etempvar _target_addr tulong) tulong) tulong))
                      (Ssequence
                        (Sset _target_addr (Etempvar _start tulong))
                        (Sset _num
                          (Ebinop Osub (Etempvar _num tulong)
                            (Econst_int (Int.repr 1) tint) tulong))))))))))))).

Definition f_unmap_and_load_vm_image := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vmid, tuint) :: (_target_addr, tulong) ::
                (_remap_addr, tulong) :: (_num, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_start, tulong) :: (_end, tulong) :: (_gfn, tulong) ::
               (_pte, tulong) :: (_pfn, tulong) :: (_t'1, tulong) :: nil);
  fn_body := unmap_and_load_vm_image_body
|}.
```
