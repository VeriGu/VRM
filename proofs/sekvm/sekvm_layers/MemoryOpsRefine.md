# MemoryOpsRefine

```coq
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import ZSet.
Require Import ListLemma2.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import RealParams.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import LayerCalculusLemma.
Require Import TacticsForTesting.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractMachine.Spec.
Require Import MemoryOps.Spec.
Require Import RData.
Require Import MemManager.Layer.
Require Import Constants.
Require Import MemoryOps.Layer.
Require Import HypsecCommLib.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section MemoryOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := MemoryOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := MemManager_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_rel: hadt = ladt
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    Section FreshPrim.

      Lemma clear_vm_range_spec_exists:
        forall habd habd' labd vmid pfn num f
               (Hspec: clear_vm_range_spec vmid pfn num habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', clear_vm_range_spec vmid pfn num labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        intros; inv Hrel; rewrite Hspec.
        eexists; split. reflexivity. constructor; reflexivity.
      Qed.

      Lemma clear_vm_range_spec_ref:
        compatsim (crel RData RData) (gensem clear_vm_range_spec) clear_vm_range_spec_low.
      Proof.
        Opaque clear_vm_range_spec.
        compatsim_simpl (@match_RData).
        exploit clear_vm_range_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent clear_vm_range_spec.
      Qed.

      Lemma prot_and_map_vm_s2pt_spec_exists:
        forall habd habd' labd vmid addr pte level f
               (Hspec: prot_and_map_vm_s2pt_spec vmid addr pte level habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', prot_and_map_vm_s2pt_spec vmid addr pte level labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma prot_and_map_vm_s2pt_spec_ref:
        compatsim (crel RData RData) (gensem prot_and_map_vm_s2pt_spec) prot_and_map_vm_s2pt_spec_low.
      Proof.
        Opaque prot_and_map_vm_s2pt_spec.
        compatsim_simpl (@match_RData).
        exploit prot_and_map_vm_s2pt_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent prot_and_map_vm_s2pt_spec.
      Qed.

      Lemma grant_stage2_sg_gpa_spec_exists:
        forall habd habd' labd vmid addr size f
               (Hspec: grant_stage2_sg_gpa_spec vmid addr size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', grant_stage2_sg_gpa_spec vmid addr size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma grant_stage2_sg_gpa_spec_ref:
        compatsim (crel RData RData) (gensem grant_stage2_sg_gpa_spec) grant_stage2_sg_gpa_spec_low.
      Proof.
        Opaque grant_stage2_sg_gpa_spec.
        compatsim_simpl (@match_RData).
        exploit grant_stage2_sg_gpa_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent grant_stage2_sg_gpa_spec.
      Qed.

      Lemma revoke_stage2_sg_gpa_spec_exists:
        forall habd habd' labd vmid addr size f
               (Hspec: revoke_stage2_sg_gpa_spec vmid addr size habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', revoke_stage2_sg_gpa_spec vmid addr size labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          intros; inv Hrel; rewrite Hspec.
          eexists; split. reflexivity. constructor; reflexivity.
        Qed.

      Lemma revoke_stage2_sg_gpa_spec_ref:
        compatsim (crel RData RData) (gensem revoke_stage2_sg_gpa_spec) revoke_stage2_sg_gpa_spec_low.
      Proof.
        Opaque revoke_stage2_sg_gpa_spec.
        compatsim_simpl (@match_RData).
        exploit revoke_stage2_sg_gpa_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
        Transparent revoke_stage2_sg_gpa_spec.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) MemoryOps_passthrough MemManager.
        Admitted.

    End PassthroughPrim.

  End WITHMEM.

End MemoryOpsProofHigh.


  (*
  Fixpoint clear_vm_loop (n: nat) (pfn: Z) (vmid: Z) (adt: RData) :=
    match n with
    | O => Some (pfn, adt)
    | S n' =>
      match clear_vm_loop n' pfn vmid adt with
      | Some (pfn', adt') =>
        if halt adt' then Some (pfn' + 1, adt') else
        let cpu := curid adt' in
        match S2PAGE_ID @ (lock adt'), S2PAGE_ID @ (log adt'), S2PAGE_ID @ (oracle adt'), FLATMEM_ID @ (log adt'), FLATMEM_ID @ (oracle adt') with
        | LockFalse, spl0, spo, fml0, fmo =>
          let s2p := CalS2Page (s2page (shared adt')) (spo cpu spl0) in
          let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
          let fmem := CalFlatmem (flatmem (shared adt')) (fmo cpu fml0) in
          match H_CalLock ((spo cpu spl0) ++ spl0) with
          | Some (_, LEMPTY, None) =>
            let page := pfn' @ s2p in
            rely is_int (s2_owner page);
            if s2_owner page =? vmid then
              let page' := mkS2Page HOSTVISOR 0 (pfn' + SMMU_HOST_OFFSET) in
              let s2p' := s2p # pfn' == page' in
              let fmem' := fmem # pfn' == 0 in
              let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
              let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
              Some (pfn' + 1,
                    adt' {tstate: 1} {shared: (shared adt') {s2page: s2p'} {flatmem: fmem'}}
                         {log: ((log adt') # S2PAGE_ID == spl') # FLATMEM_ID == fml'} {lock: (lock adt') # S2PAGE_ID == LockFalse})
            else
              let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
              Some (pfn' + 1,
                    adt' {tstate: 1} {shared: (shared adt') {s2page: s2p}}
                         {log: (log adt') # S2PAGE_ID == spl'} {lock: (lock adt') # S2PAGE_ID == LockFalse})
          | _ => None
          end
        | _, _, _, _, _ => None
        end
      | _ => None
      end
    end.

  Fixpoint clear_vm_loop (n: nat) (pfn: Z) (vmid: Z) (adt: RData) :=
    match n with
    | O => Some (pfn, adt)
    | S n' =>
      match clear_vm_loop n' pfn vmid adt with
      | Some (pfn', adt') =>
        if halt adt' then Some (pfn' + 1, adt') else
        when adt'' == clear_vm_page_spec vmid (VZ64 pfn') adt';
        Some (pfn' + 1, adt'')
      | _ => None
      end
    end.

  Definition clear_vm_range_spec (vmid: Z) (pfn: Z64) (num: Z64) (adt: RData) : option RData :=
    match pfn, num with
    | VZ64 pfn, VZ64 num =>
      rely is_vmid vmid; rely is_pfn pfn; rely is_pfn num; rely (pfn + num <=? KVM_PFN_SPACE);
      match clear_vm_loop (Z.to_nat num) pfn vmid adt with
      | Some (pfn', adt'') => Some adt''
      | _ => None
      end
    end.

  Fixpoint prot_and_map_vm_loop (n: nat) (vmid: Z) (gfn: Z) (pfn: Z) (adt: RData) :=
    match n with
    | O => Some (gfn, pfn, adt)
    | S n' =>
      match prot_and_map_vm_loop n' vmid gfn pfn adt with
      | Some (gfn', pfn', adt') =>
        if halt adt' then Some (gfn' + 1, pfn' + 1, adt') else
        let cpu := curid adt' in
        let ptid := NPT_ID in
        match S2PAGE_ID @ (lock adt'), S2PAGE_ID @ (log adt'), S2PAGE_ID @ (oracle adt'),
              ptid @ (lock adt'), ptid @ (log adt'), ptid @ (oracle adt'),
              FLATMEM_ID @ (log adt'), FLATMEM_ID @ (oracle adt')
        with
        | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
          let s2p := CalS2Page (s2page (shared adt')) (spo cpu spl0) in
          let npt := CalNPT (HOSTVISOR @ (npts (shared adt'))) (pto cpu ptl0) in
          let fmem := CalFlatmem (flatmem (shared adt')) (fmo cpu fml0) in
          let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
          let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
          match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
          | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
            let page := pfn' @ s2p in
            rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
            if s2_owner page =? HOSTVISOR then
              if s2_count page =? 0 then
                let s2p' := s2p # pfn' == (mkS2Page vmid 0 gfn') in
                let logn := vmid @ (data_log adt') in
                let fmem' := fmem # pfn' == ((doracle adt') vmid logn) in
                match pfn' @ (pt npt) with
                | (_, level, pte) =>
                  rely is_int level;
                  match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                        else local_mmap HOSTVISOR (pfn' * PAGE_SIZE) 3 PAGE_GUEST npt) with
                  | Some (halt', npt') =>
                    let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                    let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                    let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                    if halt' then
                      Some (gfn' + 1, pfn' + 1,
                            adt' {halt: true} {tstate: 0}
                                 {shared: (shared adt') {npts: (npts (shared adt')) # HOSTVISOR == npt'} {s2page: s2p'}}
                                 {log: ((log adt') # S2PAGE_ID == spl) # ptid == ptl}
                                 {lock: ((lock adt') # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)})
                    else
                      Some (gfn' + 1, pfn' + 1,
                            adt' {tstate: 1} {data_log: (data_log adt') # vmid == (logn + 1)}
                                 {shared: (shared adt') {npts: (npts (shared adt')) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'}}
                                 {log: (((log adt') # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                                 {lock: ((lock adt') # S2PAGE_ID == LockFalse) # ptid == LockFalse})
                  | _ => None
                  end
                end
              else
                Some (gfn' + 1, pfn' + 1,
                      adt' {halt: true} {tstate: 0} {shared: (shared adt') {s2page: s2p}}
                           {log: ((log adt') # S2PAGE_ID == spl)} {lock: (lock adt') # S2PAGE_ID == (LockOwn true)})
            else
              if (s2_owner page =? vmid) && (gfn' =? s2_gfn page) then
                if s2_count page =? INVALID then
                  let page' := page {s2_count: 0} in
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE (s2p # pfn' == page'))) :: spl in
                  Some (gfn' + 1, pfn' + 1,
                        adt' {tstate: 1} {shared: (shared adt') {s2page: s2p # pfn' == page'}}
                             {log: ((log adt') # S2PAGE_ID == spl')} {lock: (lock adt') # S2PAGE_ID == LockFalse})
                else
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
                  Some (gfn' + 1, pfn' + 1,
                        adt' {tstate: 1} {shared: (shared adt') {s2page: s2p}}
                             {log: ((log adt') # S2PAGE_ID == spl')} {lock: (lock adt') # S2PAGE_ID == LockFalse})
              else
                Some (gfn' + 1, pfn' + 1,
                      adt' {halt: true} {tstate: 0} {shared: (shared adt') {s2page: s2p}}
                           {log: ((log adt') # S2PAGE_ID == spl)} {lock: (lock adt') # S2PAGE_ID == (LockOwn true)})
          | _, _ => None
          end
        | _, _, _, _, _, _, _, _ => None
        end
      | _ => None
      end
    end.

  Fixpoint prot_and_map_vm_loop (n: nat) (vmid: Z) (gfn: Z) (pfn: Z) (adt: RData) :=
    match n with
    | O => Some (gfn, pfn, adt)
    | S n' =>
      match prot_and_map_vm_loop n' vmid gfn pfn adt with
      | Some (gfn', pfn', adt') =>
        if halt adt' then Some (gfn' + 1, pfn' + 1, adt') else
        when adt'' == assign_pfn_to_vm_spec vmid (VZ64 gfn')  (VZ64 pfn') adt';
        let cpu := curid adt' in
        let ptid := NPT_ID in
        match S2PAGE_ID @ (lock adt'), S2PAGE_ID @ (log adt'), S2PAGE_ID @ (oracle adt'),
              ptid @ (lock adt'), ptid @ (log adt'), ptid @ (oracle adt'),
              FLATMEM_ID @ (log adt'), FLATMEM_ID @ (oracle adt')
        with
        | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
          let s2p := CalS2Page (s2page (shared adt')) (spo cpu spl0) in
          let npt := CalNPT (HOSTVISOR @ (npts (shared adt'))) (pto cpu ptl0) in
          let fmem := CalFlatmem (flatmem (shared adt')) (fmo cpu fml0) in
          let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
          let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
          match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
          | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
            let page := pfn' @ s2p in
            rely is_int (s2_owner page); rely is_int (s2_count page); rely is_int64 (s2_gfn page);
            if s2_owner page =? HOSTVISOR then
              if s2_count page =? 0 then
                let s2p' := s2p # pfn' == (mkS2Page vmid 0 gfn') in
                let logn := vmid @ (data_log adt') in
                let fmem' := fmem # pfn' == ((doracle adt') vmid logn) in
                match pfn' @ (pt npt) with
                | (_, level, pte) =>
                  rely is_int level;
                  match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                        else local_mmap HOSTVISOR (pfn' * PAGE_SIZE) 3 PAGE_GUEST npt) with
                  | Some (halt', npt') =>
                    let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                    let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                    let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                    if halt' then
                      Some (gfn' + 1, pfn' + 1,
                            adt' {halt: true} {tstate: 0}
                                 {shared: (shared adt') {npts: (npts (shared adt')) # HOSTVISOR == npt'} {s2page: s2p'}}
                                 {log: ((log adt') # S2PAGE_ID == spl) # ptid == ptl}
                                 {lock: ((lock adt') # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)})
                    else
                      Some (gfn' + 1, pfn' + 1,
                            adt' {tstate: 1} {data_log: (data_log adt') # vmid == (logn + 1)}
                                 {shared: (shared adt') {npts: (npts (shared adt')) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'}}
                                 {log: (((log adt') # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                                 {lock: ((lock adt') # S2PAGE_ID == LockFalse) # ptid == LockFalse})
                  | _ => None
                  end
                end
              else
                Some (gfn' + 1, pfn' + 1,
                      adt' {halt: true} {tstate: 0} {shared: (shared adt') {s2page: s2p}}
                           {log: ((log adt') # S2PAGE_ID == spl)} {lock: (lock adt') # S2PAGE_ID == (LockOwn true)})
            else
              if (s2_owner page =? vmid) && (gfn' =? s2_gfn page) then
                if s2_count page =? INVALID then
                  let page' := page {s2_count: 0} in
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE (s2p # pfn' == page'))) :: spl in
                  Some (gfn' + 1, pfn' + 1,
                        adt' {tstate: 1} {shared: (shared adt') {s2page: s2p # pfn' == page'}}
                             {log: ((log adt') # S2PAGE_ID == spl')} {lock: (lock adt') # S2PAGE_ID == LockFalse})
                else
                  let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
                  Some (gfn' + 1, pfn' + 1,
                        adt' {tstate: 1} {shared: (shared adt') {s2page: s2p}}
                             {log: ((log adt') # S2PAGE_ID == spl')} {lock: (lock adt') # S2PAGE_ID == LockFalse})
              else
                Some (gfn' + 1, pfn' + 1,
                      adt' {halt: true} {tstate: 0} {shared: (shared adt') {s2page: s2p}}
                           {log: ((log adt') # S2PAGE_ID == spl)} {lock: (lock adt') # S2PAGE_ID == (LockOwn true)})
          | _, _ => None
          end
        | _, _, _, _, _, _, _, _ => None
        end
      | _ => None
      end
    end.

  Definition prot_and_map_vm_s2pt_spec (vmid: Z) (addr: Z64) (pte: Z64) (level: Z) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vm vmid; rely is_addr addr; rely is_int64 pte;
      rely is_pfn (phys_page pte / PAGE_SIZE); rely (phys_page pte / PAGE_SIZE + (if level =? 2 then 512 else 1) <=? KVM_PFN_SPACE);
      match (if level =? 2
             then (addr / PAGE_SIZE / PTRS_PER_PMD * PTRS_PER_PMD, PMD_PAGE_NUM)
             else (addr / PAGE_SIZE, 1)) with
      | (gfn, num) =>
        let pfn := phys_page pte / PAGE_SIZE in
        match prot_and_map_vm_loop (Z.to_nat num) vmid gfn pfn adt with
        | Some (gfn', pfn', adt') =>
          if halt adt' then Some adt' else
          let id := NPT_ID + vmid in
          let cpu := curid adt' in
          match id @ (lock adt'), id @ (log adt'), id @ (oracle adt') with
          | LockFalse, l, orac =>
            let npt := CalNPT (vmid @ (npts (shared adt'))) (orac cpu l) in
            let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l) ++ l in
            match H_CalLock ((orac cpu l) ++ l) with
            | Some (_, LEMPTY, None) =>
              let paddr := phys_page pte in
              let perm := PAGE_S2_KERNEL in
              let pte' := (if level =? 2 then Z.land (Z.lor paddr perm) NOT_PMD_TABLE_BIT else Z.lor paddr perm) in
              let level' := (if level =? 2 then 2 else 3) in
              match local_mmap vmid addr level' pte' npt with
              | Some (halt', npt') =>
                let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: l' in
                Some adt' {halt: halt'} {tstate: if halt' then 0 else 1}
                     {shared: (shared adt') {npts: (npts (shared adt')) # vmid == npt'}}
                     {log: (log adt') # id == (if halt' then l' else l'')}
                     {lock: (lock adt') # id == (if halt' then LockOwn true else LockFalse)}
              | _ => None
              end
            | _ => None
            end
          | _, _, _ => None
          end
        | _ => None
        end
      end
    end.

  Fixpoint grant_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
    match n with
    | O => Some (addr, adt)
    | S n' =>
      match grant_stage2_loop n' vmid addr adt with
      | Some (addr', adt') =>
        let gfn := addr' / PAGE_SIZE in
        if halt adt' then Some (addr' + PAGE_SIZE, adt') else
        let id := NPT_ID + vmid in
        let cpu := curid adt' in
        match id @ (lock adt'), id @ (oracle adt'), id @ (log adt') with
        | LockFalse, orac, l0 =>
          let npt := CalNPT (vmid @ (npts (shared adt'))) (orac cpu l0) in
          match H_CalLock ((orac cpu l0) ++ l0) with
          | Some (_, LEMPTY, None) =>
            let l1 := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt)) ::
                            TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l0) ++ l0 in
            let adt1 := adt' {tstate: 1} {shared: (shared adt') {npts: (npts (shared adt')) # vmid == npt}}
                             {log: (log adt') # id == l1} {lock: (lock adt') # id == LockFalse} in
            match gfn @ (pt npt) with
            | (_, _, pte) =>
              rely is_int64 pte;
              let npt' := CalNPT npt (orac cpu l1) in
              match H_CalLock ((orac cpu l1) ++ l1) with
              | Some (_, LEMPTY, None) =>
                let l2 := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) ::
                                TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l1) ++ l1 in
                let adt2 := adt1 {tstate: 1} {shared: (shared adt') {npts: (npts (shared adt')) # vmid == npt'}}
                                {log: (log adt') # id == l2} {lock: (lock adt') # id == LockFalse} in
                match gfn @ (pt npt') with
                | (_, level, _) =>
                  rely is_int level;
                  let pte_pa := phys_page pte in
                  if pte_pa =? 0 then Some (addr' + PAGE_SIZE, adt2)
                  else
                    let pfn := (if level =? 2 then pte_pa / PAGE_SIZE + (Z.land (addr' / PAGE_SIZE) 511) else pte_pa / PAGE_SIZE) in
                    match S2PAGE_ID @ (lock adt2), S2PAGE_ID @ (log adt2), S2PAGE_ID @ (oracle adt2) with
                    | LockFalse, spl0, spo =>
                      let s2p := CalS2Page (s2page (shared adt2)) (spo cpu spl0) in
                      let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
                      match H_CalLock ((spo cpu spl0) ++ spl0) with
                      | Some (_, LEMPTY, None) =>
                        let page := pfn @ s2p in
                        rely is_int (s2_owner page); rely is_int (s2_count page);
                        let s2p' := (if (s2_owner page =? vmid) && (s2_count page <? MAX_SHARE_COUNT)
                                      then s2p # pfn == (page {s2_count: (s2_count page) + 1})
                                      else s2p) in
                        let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                        Some (addr' + PAGE_SIZE,
                              adt2 {tstate: 1} {shared: (shared adt2) {s2page: s2p'}}
                                   {log: (log adt2) # S2PAGE_ID == spl'} {lock: (lock adt2) # S2PAGE_ID == LockFalse})
                      | _ => None
                      end
                    | _, _, _ => None
                    end
                end
              | _ => None
              end
            end
          | _ => None
          end
        | _, _, _ => None
        end
      | _ => None
      end
    end.

    Definition grant_stage2_sg_gpa_spec (vmid: Z) (addr: Z64) (size: Z64) (adt: RData) : option RData :=
      match addr, size with
      | VZ64 addr, VZ64 size =>
        let num := (size + 4095) / PAGE_SIZE in
        rely is_vm vmid; rely is_addr addr; rely is_addr size; rely (addr + num * PAGE_SIZE <=? KVM_ADDR_SPACE);
        match grant_stage2_loop (Z.to_nat num) vmid addr adt with
        | Some (addr', adt') => Some adt'
        | _ => None
        end
      end.

  Fixpoint revoke_stage2_loop (n: nat) (vmid: Z) (addr: Z) (adt: RData) :=
    match n with
    | O => Some (addr, adt)
    | S n' =>
      match grant_stage2_loop n' vmid addr adt with
      | Some (addr', adt') =>
        let gfn := addr' / PAGE_SIZE in
        if halt adt' then Some (addr' + PAGE_SIZE, adt') else
        let id := NPT_ID + vmid in
        let cpu := curid adt' in
        match id @ (lock adt'), id @ (oracle adt'), id @ (log adt') with
        | LockFalse, orac, l0 =>
          let npt := CalNPT (vmid @ (npts (shared adt'))) (orac cpu l0) in
          match H_CalLock ((orac cpu l0) ++ l0) with
          | Some (_, LEMPTY, None) =>
            let l1 := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt)) ::
                            TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l0) ++ l0 in
            let adt1 := adt' {tstate: 1} {shared: (shared adt') {npts: (npts (shared adt')) # vmid == npt}}
                             {log: (log adt') # id == l1} {lock: (lock adt') # id == LockFalse} in
            match gfn @ (pt npt) with
            | (_, _, pte) =>
              rely is_int64 pte;
              let npt' := CalNPT npt (orac cpu l1) in
              match H_CalLock ((orac cpu l1) ++ l1) with
              | Some (_, LEMPTY, None) =>
                let l2 := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) ::
                                TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (orac cpu l1) ++ l1 in
                let adt2 := adt1 {tstate: 1} {shared: (shared adt') {npts: (npts (shared adt')) # vmid == npt'}}
                                {log: (log adt') # id == l2} {lock: (lock adt') # id == LockFalse} in
                match gfn @ (pt npt') with
                | (_, level, _) =>
                  rely is_int level;
                  let pte_pa := phys_page pte in
                  if pte_pa =? 0 then Some (addr' + PAGE_SIZE, adt2)
                  else
                    let pfn := (if level =? 2 then pte_pa / PAGE_SIZE + (Z.land (addr' / PAGE_SIZE) 511) else pte_pa / PAGE_SIZE) in
                    let ptid := NPT_ID in
                    match S2PAGE_ID @ (lock adt2), S2PAGE_ID @ (log adt2), S2PAGE_ID @ (oracle adt2),
                          ptid @ (lock adt2), ptid @ (log adt2), ptid @ (oracle adt2),
                          FLATMEM_ID @ (log adt2), FLATMEM_ID @ (oracle adt2)
                    with
                    | LockFalse, spl0, spo, LockFalse, ptl0, pto, fml0, fmo =>
                      let s2p := CalS2Page (s2page (shared adt2)) (spo cpu spl0) in
                      let npt := CalNPT (HOSTVISOR @ (npts (shared adt2))) (pto cpu ptl0) in
                      let fmem := CalFlatmem (flatmem (shared adt2)) (fmo cpu fml0) in
                      let spl := TEVENT cpu (TSHARED (OPULL S2PAGE_ID)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (spo cpu spl0) ++ spl0 in
                      let ptl := TEVENT cpu (TSHARED (OPULL ptid)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: (pto cpu ptl0) ++ ptl0 in
                      match H_CalLock ((spo cpu spl0) ++ spl0), H_CalLock ((pto cpu ptl0) ++ ptl0) with
                      | Some (_, LEMPTY, None), Some (_, LEMPTY, None) =>
                        let page := pfn @ s2p in
                        rely is_int (s2_owner page); rely is_int (s2_count page);
                        if (s2_owner page =? vmid) && (s2_count page >? 0) then
                          let s2p' := s2p # pfn == (page {s2_count: (s2_count page) - 1}) in
                          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p')) :: spl in
                          if s2_count page =? 1 then
                            let logn := vmid @ (data_log adt2) in
                            let fmem' := fmem # pfn == ((doracle adt2) vmid logn) in
                            match pfn @ (pt npt) with
                            | (_, level, pte) =>
                              rely is_int level;
                              match (if (if phys_page pte =? 0 then 0 else level) =? 0 then Some (false, npt)
                                    else local_mmap HOSTVISOR (pfn * PAGE_SIZE) 3 PAGE_GUEST npt) with
                              | Some (halt', npt') =>
                                let ptl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: ptl in
                                let fml' := TEVENT cpu (TSHARED (OFLATMEM fmem')) :: (fmo cpu fml0) ++ fml0 in
                                if halt' then
                                  Some (addr' + PAGE_SIZE,
                                        adt2 {halt: true} {tstate: 0}
                                             {shared: (shared adt2) {npts: (npts (shared adt2)) # HOSTVISOR == npt'} {s2page: s2p'}}
                                             {log: (((log adt2) # S2PAGE_ID == spl) # ptid == ptl)}
                                             {lock: ((lock adt2) # S2PAGE_ID == (LockOwn true)) # ptid == (LockOwn true)})
                                else
                                  Some (addr' + PAGE_SIZE,
                                        adt2 {tstate: 1} {data_log: (data_log adt2) # vmid == (logn + 1)}
                                             {shared: (shared adt2) {npts: (npts (shared adt2)) # HOSTVISOR == npt'} {s2page: s2p'} {flatmem: fmem'}}
                                             {log: (((log adt2) # S2PAGE_ID == spl') # ptid == ptl') # FLATMEM_ID == fml'}
                                             {lock: ((lock adt2) # S2PAGE_ID == LockFalse) # ptid == LockFalse})
                              | _ => None
                              end
                            end
                          else
                            Some (addr' + PAGE_SIZE,
                                  adt2 {tstate: 1} {shared: (shared adt2) {s2page: s2p'}}
                                       {log: (log adt2) # S2PAGE_ID == spl'} {lock: (lock adt2) # S2PAGE_ID == LockFalse})
                        else
                          let spl' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (OS2_PAGE s2p)) :: spl in
                          Some (addr' + PAGE_SIZE,
                                adt2 {tstate: 1} {shared: (shared adt2) {s2page: s2p}}
                                     {log: (log adt2) # S2PAGE_ID == spl'} {lock: (lock adt2) # S2PAGE_ID == LockFalse})
                      | _, _ => None
                      end
                    | _, _, _, _, _, _, _, _ => None
                    end
                end
              | _ => None
              end
            end
          | _ => None
          end
        | _, _, _ => None
        end
      | _ => None
      end
    end.

    Definition revoke_stage2_sg_gpa_spec (vmid: Z) (addr: Z64) (size: Z64) (adt: RData) : option RData :=
      match addr, size with
      | VZ64 addr, VZ64 size =>
        let num := (size + 4095) / PAGE_SIZE in
        rely is_vm vmid; rely is_addr addr; rely is_addr size; rely (addr + num * PAGE_SIZE <=? KVM_ADDR_SPACE);
        match revoke_stage2_loop (Z.to_nat num) vmid addr adt with
        | Some (addr', adt') => Some adt'
        | _ => None
        end
      end.

  Lemma clear_vm_range_spec_exists:
    forall habd habd' labd vmid pfn num f
            (Hspec: clear_vm_range_spec vmid pfn num habd = Some habd')
            (Hrel: relate_RData f habd labd),
      exists labd', clear_vm_range_spec vmid pfn num labd = Some labd' /\ relate_RData f habd' labd'.
    Proof.
      intros; inv Hrel; hsimpl_func Hspec; repeat autounfold in *; srewrite.
      assert(forall n t d (nrange: 0 <= Z.of_nat n < 268435456) (nsum: z + (Z.of_nat n) <= 268435456)
                (loopH: clear_vm_loop n z vmid labd = Some (t, d)),
                clear_vm_loop0 n z vmid labd = Some (t, d) /\ t = z + (Z.of_nat n)).
      { induction n. intros. simpl in *. inv loopH. rewrite Z.add_0_r. split; reflexivity.
        intros. rewrite Nat2Z.inj_succ, succ_plus_1 in nrange, nsum.
        assert(range: 0 <= Z.of_nat n < 268435456) by omega.
        rewrite Z.add_comm in nsum. assert(sum: z + Z.of_nat n <= 268435456) by (bool_rel_all; omega).
        simpl in *; repeat autounfold in *. simpl_hyp loopH. destruct p.
        exploit (IHn z2 r range sum). reflexivity. intros [loop0 t0]. rewrite loop0. srewrite.
        bool_rel_all. extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond.
        repeat simpl_hyp loopH; contra.
        - inv loopH. split. reflexivity. rewrite Zpos_P_of_succ_nat.
          rewrite succ_plus_1. rewrite Z.add_assoc. reflexivity.
        - srewrite. inv loopH. split. reflexivity. rewrite Zpos_P_of_succ_nat.
          rewrite succ_plus_1. rewrite Z.add_assoc. reflexivity.
        - srewrite. inv loopH. split. reflexivity. rewrite Zpos_P_of_succ_nat.
          rewrite succ_plus_1. rewrite Z.add_assoc. reflexivity. }
      bool_rel_all; clear_hyp.
      exploit H; try apply C5; rewrite Z2Nat.id; try omega. intros [H1 H2].
      eexists; split. reflexivity. constructor; reflexivity.
    Qed.

  Lemma prot_and_map_vm_s2pt_spec_exists:
    forall habd habd' labd vmid addr pte level f
            (Hspec: prot_and_map_vm_s2pt_spec vmid addr pte level habd = Some habd')
            (Hrel: relate_RData f habd labd),
      exists labd', prot_and_map_vm_s2pt_spec0 vmid addr pte level labd = Some labd' /\ relate_RData f habd' labd'.
    Proof.
      intros; inv Hrel; repeat autounfold in *.
      simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
      simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
      destruct (level =? 2) eqn:Hlevel; simpl_hyp Hspec.
      - assert(forall n t1 t2 d (nrange: 0 <= Z.of_nat n <= 512)
                  (loopH: prot_and_map_vm_loop n vmid (z / 4096 / 512 * 512) (phys_page z0 / 4096) labd = Some (t1, t2, d)),
                  prot_and_map_vm_loop0 n vmid (z / 4096 / 512 * 512) (phys_page z0 / 4096) labd = Some (t1, t2, d) /\
                  t1 = (z / 4096 / 512 * 512) + (Z.of_nat n) /\
                  t2 = (phys_page z0 / 4096) + (Z.of_nat n)).
        { clear C6. induction n. intros. simpl in *. inv loopH. repeat rewrite Z.add_0_r. split_and; reflexivity.
          intros. rewrite Nat2Z.inj_succ, succ_plus_1 in nrange.
          assert(range: 0 <= Z.of_nat n <= 512) by omega.
          simpl in *; repeat autounfold in *. simpl_hyp loopH. destruct p0. destruct p0.
          exploit (IHn z1 z2 r range). reflexivity. intros (loop0 & t0 & t0'). rewrite loop0. srewrite.
          bool_rel_all. extract_if. apply andb_true_iff; split; bool_rel. somega.
          assert(z / 4096 / 512 <= 281474976710655 / 4096 / 512) by(repeat apply Z_div_le; omega).
          assert(z / 4096 / 512 <= 134217727) by apply H.
          assert(z / 4096 / 512 * 512 <= 68719476224) by omega. omega. rewrite Cond.
          extract_if. apply andb_true_iff; split; bool_rel. unfold phys_page; autounfold; somega.
          omega. rewrite Cond0. extract_if. apply andb_true_iff; split; bool_rel; omega. rewrite Cond1.
          repeat simpl_hyp loopH; contra; inv loopH;
            (split; [first[reflexivity|destruct r; simpl in *; srewrite; reflexivity]|
                      split; rewrite Zpos_P_of_succ_nat; rewrite succ_plus_1; rewrite Z.add_assoc; reflexivity]). }
        bool_rel_all; clear_hyp.
        destruct p. destruct p. exploit H; try apply C6; rewrite Z2Nat.id; try omega. intros (H1 & H2 & H3).
        srewrite. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond0.
        extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond1.
        eexists; split. reflexivity. constructor; reflexivity.
      - simpl in *. bool_rel_all. extract_if. apply andb_true_iff; split; bool_rel; somega. rewrite Cond.
        extract_if. apply andb_true_iff; split; bool_rel; somega.
        assert(z / 4096 <= 281474976710655 / 4096) by (apply Z_div_le; omega).
        assert(z / 4096 <= 68719476735) by apply H. omega. rewrite Cond0.
        repeat simpl_hyp C6; contra.
        inv C6. srewrite. inv Hspec. eexists; split. reflexivity. constructor; reflexivity.
        assert(3 =? 2 = false) by reflexivity.
        repeat autounfold in *; repeat simpl_hyp C6; contra; inv C6; simpl in *; srewrite; repeat simpl_hyp Hspec; inv Hspec; simpl in *;
          repeat srewrite; (eexists; split; [reflexivity|constructor; reflexivity]).
    Qed.
   *)
```
