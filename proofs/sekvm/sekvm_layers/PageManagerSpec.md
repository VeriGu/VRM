# Spec

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import GenSem.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import RealParams.
Require Import GenSem.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import PrimSemantics.
Require Import CompatClightSem.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractMachine.Spec.
Require Import PageIndex.Layer.
Require Import PageIndex.Spec.
Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section PageManagerSpec.

  Definition get_pfn_owner_spec (pfn: Z64) (adt: RData) : option Z :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      if halt adt then Some 0 else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        rely is_int (s2_owner page);
        Some (s2_owner page)
      | _ => None
      end
    end.

  Definition set_pfn_owner_spec (pfn: Z64) (vmid: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      if halt adt then Some adt else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        if s2_owner page =? INVALID then
          Some adt
        else
          rely is_vmid vmid;
          Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # pfn == (page {s2_owner: vmid})}}
      | _ => None
      end
    end.

  Definition get_pfn_count_spec (pfn: Z64) (adt: RData) : option Z :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      if halt adt then Some 0 else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        rely is_int (s2_count page);
        Some (s2_count page)
      | _ => None
      end
    end.

  Definition set_pfn_count_spec (pfn: Z64) (count: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      if halt adt then Some adt else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        if s2_owner page =? INVALID then
          Some adt
        else
          Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # pfn == (page {s2_count: count})}}
      | _ => None
      end
    end.

  Definition get_pfn_map_spec (pfn: Z64) (adt: RData) : option Z64 :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      if halt adt then Some (VZ64 0) else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        rely is_int64 (s2_gfn page);
        Some (VZ64 (s2_gfn page))
      | _ => None
      end
    end.

  Definition set_pfn_map_spec (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    match pfn, gfn with
    | VZ64 pfn, VZ64 gfn =>
      rely is_gfn pfn;
      if halt adt then Some adt else
      let id := S2PAGE_ID in
      match ZMap.get id (lock adt) with
      | LockOwn true =>
        let page := pfn @ (s2page (shared adt)) in
        if s2_owner page =? INVALID then
          Some adt
        else
          Some adt {shared: (shared adt) {s2page: (s2page (shared adt)) # pfn == (page {s2_gfn: gfn})}}
      | _ => None
      end
    end.

End PageManagerSpec.

Section PageManagerSpecLow.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := PageIndex_ops) LDATA).

  Definition get_pfn_owner_spec0 (pfn: Z64) (adt: RData) : option Z :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        check_spec INVALID adt
      else
        rely is_s2page index;
        when ret == get_s2_page_vmid_spec (VZ64 index) adt;
        rely is_int ret;
        check_spec ret adt
    end.

  Definition set_pfn_owner_spec0 (pfn: Z64) (vmid: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        Some adt
      else
        set_s2_page_vmid_spec (VZ64 index) vmid adt
    end.

  Definition get_pfn_count_spec0 (pfn: Z64) (adt: RData) : option Z :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        check_spec INVALID adt
      else
        when ret == get_s2_page_count_spec (VZ64 index) adt;
        rely is_int ret;
        check_spec ret adt
    end.

  Definition set_pfn_count_spec0 (pfn: Z64) (count: Z) (adt: RData) : option RData :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        Some adt
      else
        set_s2_page_count_spec (VZ64 index) count adt
    end.

  Definition get_pfn_map_spec0 (pfn: Z64) (adt: RData) : option Z64 :=
    match pfn with
    | VZ64 pfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        check64_spec (VZ64 INVALID64) adt
      else
        when' ret == get_s2_page_gfn_spec (VZ64 index) adt;
        rely is_int64 ret;
        check64_spec (VZ64 ret) adt
    end.

  Definition set_pfn_map_spec0 (pfn: Z64) (gfn: Z64) (adt: RData) : option RData :=
    match pfn, gfn with
    | VZ64 pfn, VZ64 gfn =>
      rely is_gfn pfn;
      when' index == get_s2_page_index_spec (VZ64 (pfn * PAGE_SIZE)) adt;
      rely is_int64 index;
      if index =? INVALID64 then
        Some adt
      else
        set_s2_page_gfn_spec (VZ64 index) (VZ64 gfn) adt
    end.

  Inductive get_pfn_owner_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_pfn_owner_spec_low_intro s (WB: _ -> Prop) m'0 labd pfn res
      (Hinv: high_level_invariant labd)
      (Hspec: get_pfn_owner_spec0 (VZ64 (Int64.unsigned pfn)) labd = Some (Int.unsigned res)):
      get_pfn_owner_spec_low_step s WB ((Vlong pfn)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive set_pfn_owner_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_pfn_owner_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pfn vmid
      (Hinv: high_level_invariant labd)
      (Hspec: set_pfn_owner_spec0 (VZ64 (Int64.unsigned pfn)) (Int.unsigned vmid) labd = Some labd'):
      set_pfn_owner_spec_low_step s WB ((Vlong pfn)::(Vint vmid)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive get_pfn_count_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_pfn_count_spec_low_intro s (WB: _ -> Prop) m'0 labd pfn res
      (Hinv: high_level_invariant labd)
      (Hspec: get_pfn_count_spec0 (VZ64 (Int64.unsigned pfn)) labd = Some (Int.unsigned res)):
      get_pfn_count_spec_low_step s WB ((Vlong pfn)::nil) (m'0, labd) (Vint res) (m'0, labd).

  Inductive set_pfn_count_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_pfn_count_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pfn count
      (Hinv: high_level_invariant labd)
      (Hspec: set_pfn_count_spec0 (VZ64 (Int64.unsigned pfn)) (Int.unsigned count) labd = Some labd'):
      set_pfn_count_spec_low_step s WB ((Vlong pfn)::(Vint count)::nil) (m'0, labd) Vundef (m'0, labd').

  Inductive get_pfn_map_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | get_pfn_map_spec_low_intro s (WB: _ -> Prop) m'0 labd pfn res
      (Hinv: high_level_invariant labd)
      (Hspec: get_pfn_map_spec0 (VZ64 (Int64.unsigned pfn)) labd = Some (VZ64 (Int64.unsigned res))):
      get_pfn_map_spec_low_step s WB ((Vlong pfn)::nil) (m'0, labd) (Vlong res) (m'0, labd).

  Inductive set_pfn_map_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | set_pfn_map_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pfn gfn
      (Hinv: high_level_invariant labd)
      (Hspec: set_pfn_map_spec0 (VZ64 (Int64.unsigned pfn)) (VZ64 (Int64.unsigned gfn)) labd = Some labd'):
      set_pfn_map_spec_low_step s WB ((Vlong pfn)::(Vlong gfn)::nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_pfn_owner_spec_low: compatsem LDATAOps :=
      csem get_pfn_owner_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

    Definition set_pfn_owner_spec_low: compatsem LDATAOps :=
      csem set_pfn_owner_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

    Definition get_pfn_count_spec_low: compatsem LDATAOps :=
      csem get_pfn_count_spec_low_step (type_of_list_type (Tint64::nil)) Tint32.

    Definition set_pfn_count_spec_low: compatsem LDATAOps :=
      csem set_pfn_count_spec_low_step (type_of_list_type (Tint64::Tint32::nil)) Tvoid.

    Definition get_pfn_map_spec_low: compatsem LDATAOps :=
      csem get_pfn_map_spec_low_step (type_of_list_type (Tint64::nil)) Tint64.

    Definition set_pfn_map_spec_low: compatsem LDATAOps :=
      csem set_pfn_map_spec_low_step (type_of_list_type (Tint64::Tint64::nil)) Tvoid.

  End WITHMEM.

End PageManagerSpecLow.

```
