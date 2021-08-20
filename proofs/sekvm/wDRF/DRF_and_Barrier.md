### DRF-Kernel & No-Barrier-Misuse

We verify DRF-Kernel & No-Barrier-Misuse by enforcing constraints at bottom layer primitives and proving SeKVM satisfies all constraints during refinement proof.

SeKVM always invokes bottom layer primitives to access shared memory. For example, writing to page table is done by primitive `pt_store` of `AbsMachine` layer.
```
  Definition pt_store_spec0 (vmid: Z) (addr: Z64) (value: Z64) (adt: RData) : option RData :=
    if halt adt then Some adt else
    match addr, value with
    | VZ64 addr, VZ64 value' =>
      rely is_vmid vmid; rely (pool_start vmid <=? addr); rely (addr <? pool_end vmid);
      let id := NPT_ID + vmid in
      match ZMap.get id (lock adt), bars adt with
      | LockOwn true, BarrierValid =>
        let npt := vmid @ (npts (shared adt)) in
        if (pool_start vmid <=? addr) && (addr <? pgd_start vmid) then
          let npt' := npt {pt_vttbr_pool: (pt_vttbr_pool npt) # addr == value'} in
          Some adt {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
        else ...
      | _, _ => None
      end
    end.
```
Notice that `pt_store`'s specification encodes two constraints: one is for `lock`, the other is for `barrier`.
```
match ZMap.get id (lock adt), bars adt with
| LockOwn true, BarrierValid =>
...
| _, _ => None
end
```
The lock constraint enforces that when invoking a memory access, the corresponding lock must be held, which implies DRF-Kernel property. The barrier constraint enforces that a memory access can be invoked only if barriers are correctly placed, which is related to No-Barrier-Misuse Property.

Each kernel's shared object (e.g. a page table) has an associated lock whose state can be `LockFalse` (the lock is free), `LockOwn true` (the lock is held by local CPU), and `LockOwn false` (an intermediate state only used in the proof of ticket lock's implementation). An `acquire_lock` primitives turns a lock from `LockFalse` to `LockOwn true` and a `release_lock` primitive turns the state from `LockOwn true` back to `LockFalse`. All memory accesses to a shared object require `LockOwn true` state (as shown in `pt_store`'s specification).
With this setting, DRF-Kernel property is natually satisfied. 

All memory accesses will be checked during refinement proof. For example, the function `map_s2pt` of `NPTOps` layer acquires a page table lock, accesses the page table, and releases the lock, as shown below. 
```
void map_s2pt(u32 vmid, u64 addr, u32 level, u64 pte)
{
    acquire_lock_pt(vmid);
    set_npt(vmid, addr, level, pte);
    release_lock_pt(vmid);
}

void set_npt(u32 vmid, u64 addr, u32 level, u64 pte)
{
    u64 vttbr, pgd, pud, pmd;

    vttbr = get_pt_vttbr(vmid);
    pgd = walk_pgd(vmid, vttbr, addr, 1U);
    pud = walk_pud(vmid, pgd, addr, 1U);
    if (level == 2U) {
        set_pmd(vmid, pud, addr, pte);
    }
    else {
        pmd = walk_pmd(vmid, pud, addr, 1U);
        if (pmd_table(pmd) == PMD_TYPE_TABLE) {
            set_pte(vmid, pmd, addr, pte);
        }
        else panic();
    }
}
```
Each primitive used in `set_npt`(`walk_pgd`, `walk_pud`, `walk_pmd` `set_pmd`, `set_pte` in `PTWalk` layer) has the lock constraint requiring `LockOwn true` state. In `map_s2pt` function, we prove that the lock is indeed correctly used so that all the contraints are satisfied and eliminated in `map_s2pt`'s specification. Related proof can be found in [NPTOpsRefine](../sekvm_layers/NPTOpsRefine.md)
```
  Definition map_s2pt_spec (vmid: Z) (addr: Z64) (level: Z) (pte: Z64) (adt: RData) : option RData :=
    match addr, pte with
    | VZ64 addr, VZ64 pte =>
      rely is_vmid vmid; rely is_addr addr; rely is_int64 pte;
      if halt adt then Some adt else
      let id := NPT_ID + vmid in
      let cpu := curid adt in
      match id @ (lock adt) with
      | LockFalse =>
        let l := id @ (log adt) in
        let orac := id @ (oracle adt) in
        let l0 := orac cpu l in
        let npt0 := vmid @ (npts (shared adt)) in
        let npt := CalNPT npt0 (orac cpu l) in
        let l' := TEVENT cpu (TSHARED (OPULL id)) :: TEVENT cpu (TTICKET (WAIT_LOCK local_lock_bound)) :: orac cpu l ++ l in
        if (level =? 2) || (level =? 3) then
          if pte =? 0 then None
          else
            match local_mmap vmid addr level pte npt with
            | Some (halt', npt') =>
              let l'' := TEVENT cpu (TTICKET REL_LOCK) :: TEVENT cpu (TSHARED (ONPT npt')) :: l' in
              let adt' := adt {halt: halt'} 
	                      {tstate: if halt' then 0 else 1} 
			      {shared: (shared adt) {npts: (npts (shared adt)) # vmid == npt'}}
                              {log: (log adt) # id == if halt' then l' else l''}
                              {lock: (lock adt) # id == if halt' then LockOwn true else LockFalse}
              in
              match H_CalLock l'' with
              | Some _ => Some adt'
              | _ => None
              end
            | _ => None
            end
        else None
      | _ => None
      end
    end.
```


Since barriers are required right after acquiring a lock and right before releasing a lock, we model the machine's barrier state(`bars`) as `BarrierValid` (barriers are well placed), `BarrierNeeded` (require a barrier immediately), or `Barriered` (a barrier is just placed). The bottom layer primitive `barrier` whose implementation is inserting a full-barrier `dsb; isb` can turn the state from `BarrierValid` to `Barriered` or from `BarrierNeeded` to `BarrierValid`. 
Here is `barrier` primitive's specification:
```
  Definition barrier_spec (adt: RData): option RData :=
    match adt.(bars) with
    | BarrierValid => Some adt {bars: Barriered}
    | BarrierNeeded => Some adt {bars: BarrierValid}
    | Barriered => None
    end.
```
`log_hold` is the primitive that generates an event of successfully holding a lock. It must be followed by a `barrier`. Therefore, we enforce that `log_hold` can only be invoked with `BarrierValid` and it turns the state to `BarrierNeeded`.
```
  Definition log_hold_spec (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), adt.(bars) with
    | l, BarrierValid =>
      let l' := TEVENT adt.(curid) (TTICKET HOLD_LOCK) :: l in
      Some adt {log: ZMap.set lk (l') adt.(log)} {bars: BarrierNeeded}
    | _, _ => None
    end.
```

`incr_now` is the only primitive that releases a lock. It requires a barrier before it. So `incr_now` must start with a `Barriered` state and turn it to `BarrierValid`.
```
  Definition incr_now_spec (lk: Z) (adt: RData): option RData :=
    match ZMap.get lk adt.(log), adt.(bars) with
    | l, Barriered =>
      let l' := TEVENT adt.(curid) (TTICKET INC_NOW) :: l in
      Some adt {log: ZMap.set lk (l') adt.(log)}
               {bars: BarrierValid}
    | _, _ => None
    end.
```
To satisfy the barrier constraints, we implement the ticket lock in `LockOps` layer as follows.
```
void wait_lock(u32 lk)
{
    u32 my_ticket, cur_ticket;
    my_ticket = incr_ticket(10U, lk);
    cur_ticket = get_now(lk);
    while (my_ticket != cur_ticket) {
        cur_ticket = get_now(lk);
    }
    log_hold(lk);
    barrier();
}

void pass_lock(u32 lk)
{
    barrier();
    incr_now(lk);
}
```
Since `barrier`s are correctly placed, we verify that the primitive `wait_lock` and `pass_lock` of `LockOps` eventually restore the barrier state to `BarrierValid`. Besides, since all other primitives of `LockOps`  will not change the barrier state, we prove that the barrier state will always be `BarrierValid` in `LockOps` layer, meaning that barriers are indeed well placed whatever systems built upon `LockOps` layer. Related proof can be found in [LockOpsRefine](../sekvm_layers/LockOpsRefine.md).
