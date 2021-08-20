# BootCoreCode

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
Definition _pgnum := 6%positive.
Definition _pte := 7%positive.
Definition _remap := 8%positive.
Definition _remap_addr := 9%positive.
Definition _start := 10%positive.
Definition _target_addr := 11%positive.
Definition _vmid := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.

Definition gen_vmid_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_core (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_next_vmid (Tfunction Tnil tuint cc_default)) nil)
        (Sset _vmid (Etempvar _t'1 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _vmid tuint)
                       (Econst_int (Int.repr 16) tuint) tint)
          (Scall None
            (Evar set_next_vmid (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
            ((Ebinop Oadd (Etempvar _vmid tuint)
               (Econst_int (Int.repr 1) tuint) tuint) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall None
            (Evar release_lock_core (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Scall (Some _t'2)
              (Evar check (Tfunction (Tcons tuint Tnil) tuint cc_default))
              ((Etempvar _vmid tuint) :: nil))
            (Sreturn (Some (Etempvar _t'2 tuint)))))))).

Definition f_gen_vmid := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_vmid, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := gen_vmid_body
|}.

Definition alloc_remap_addr_body :=
  (Ssequence
    (Scall None (Evar acquire_lock_core (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar get_next_remap_ptr (Tfunction Tnil tulong cc_default)) nil)
        (Sset _remap (Etempvar _t'1 tulong)))
      (Ssequence
        (Sifthenelse (Ebinop Olt
                       (Ebinop Oadd (Etempvar _remap tulong)
                         (Ebinop Omul (Etempvar _pgnum tulong)
                           (Econst_long (Int64.repr 4096) tulong) tulong)
                         tulong) (Econst_long (Int64.repr 67108864) tulong)
                       tint)
          (Scall None
            (Evar set_next_remap_ptr (Tfunction (Tcons tulong Tnil) tvoid
                                        cc_default))
            ((Ebinop Oadd (Etempvar _remap tulong)
               (Ebinop Omul (Etempvar _pgnum tulong)
                 (Econst_long (Int64.repr 4096) tulong) tulong) tulong) :: nil))
          (Scall None (Evar panic (Tfunction Tnil tvoid cc_default)) nil))
        (Ssequence
          (Scall None
            (Evar release_lock_core (Tfunction Tnil tvoid cc_default)) nil)
          (Ssequence
            (Scall (Some _t'2)
              (Evar check64 (Tfunction (Tcons tulong Tnil) tulong cc_default))
              ((Etempvar _remap tulong) :: nil))
            (Sreturn (Some (Etempvar _t'2 tulong)))))))).

Definition f_alloc_remap_addr := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_pgnum, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_remap, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := alloc_remap_addr_body
|}.
```
