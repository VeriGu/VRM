# CalLock

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import CLemmas.
Require Import CommonTactic.

Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.

Local Open Scope Z_scope.

Section Constants.
  (* TODO: FIXME *)
  Definition lock_bound := 10 % Z.
  Lemma lock_bound_lt_max: 0 <= lock_bound <= Int.max_unsigned.
  Proof. unfold lock_bound. pose proof max_unsigned_val. omega. Qed.

  Definition fairness := 20 % nat.
  Lemma positive_fairness: (0 < fairness)%nat.
  Proof. unfold fairness. omega. Qed.

End Constants.

Global Opaque lock_bound fairness.

Section CalLockOpsCode.

  Local Notation wrap z := (Int.unsigned (Int.repr z)) (only parsing).

  (* returns (ticket_value * now_value * waiting_list), but with wraparounds *)
  Fixpoint CalTicketLockWraparound (l: MultiLog): option (Z * Z * list nat) :=
    let wrapSome tnq :=
      match tnq with (t, n, q) => Some (wrap t, wrap n, q) end
    in

    match l with
    | nil => Some (0, 0, nil)
    | TEVENT _ e :: l' =>
      match CalTicketLockWraparound l', e with
      | None,              _                      => None
      | Some prv,          TSHARED _
      | Some prv,          TTICKET GET_NOW
      | Some prv,          TTICKET HOLD_LOCK      => wrapSome prv
      | Some (t', n', q'), TTICKET (INC_TICKET p) => let t := t' + 1 in
                                                     let q := q' ++ (p::nil) in
                                                     wrapSome (t, n', q)
      | Some (t', n', q'), TTICKET INC_NOW        => let n := n' + 1 in
                                                     match q' with
                                                     | nil as q | _ :: q =>
                                                       wrapSome (t', n, q)
                                                     end
      | _,                _                      => None
      end
    end.

  (* b  := wait bound
   * c  := current CPU
   * t  := c's ticket number
   * l  := log
   * to := oracle
   *
   * advance l to when now == t, i.e. when c can obtain the lock,
   * with wait bound b, and with integer wraparound
   *)
  Fixpoint CalTicketWaitWraparound (b: nat) (c t: Z)
                                   (l: MultiLog) (to: MultiOracle):
                                   option (list MultiOracleEvent) :=
    match b with
    | O    => None
    | S b' => let l' := TEVENT c (TTICKET GET_NOW) :: (to c l) ++ l in
              match CalTicketLockWraparound l' with
              | Some (_, n, _) => if zeq t n
                                   then Some l'
                                   else CalTicketWaitWraparound b' c t l' to
              | _               => None
              end
    end.

End CalLockOpsCode.

Section CalLockOps.

  (* returns (ticket_value * now_value * waiting_list) *)
  Fixpoint CalTicketLock (l: MultiLog): option (Z * Z * list nat) :=
    match l with
    | nil => Some (0, 0, nil)
    | TEVENT _ e :: l' =>
      match CalTicketLock l', e with
      | None,              _                      => None
      | Some prv,          TSHARED _
      | Some prv,          TTICKET GET_NOW
      | Some prv,          TTICKET HOLD_LOCK      => Some prv
      | Some (t', n', q'), TTICKET (INC_TICKET p) => let t := t' + 1 in
                                                     let q := q' ++ (p::nil) in
                                                     Some (t, n', q)
      | Some (t', n', q'), TTICKET INC_NOW        => let n := n' + 1 in
                                                     match q' with
                                                     | nil as q | _ :: q =>
                                                       Some (t', n, q)
                                                     end
      | _,                _                      => None
      end
    end.

  (* b  := wait bound
   * c  := current CPU
   * t  := c's ticket number
   * l  := log
   * to := oracle
   *
   * advance l to when now == t, i.e. when c can obtain the lock,
   * with wait bound b, but without integer wraparound
   *)
  Fixpoint CalTicketWait (b: nat) (c t: Z)
                         (l: MultiLog) (to: MultiOracle):
                         option (list MultiOracleEvent) :=
    match b with
      | O    => None
      | S b' => let l' := TEVENT c (TTICKET GET_NOW) :: (to c l) ++ l in
                match CalTicketLock l' with
                  | Some (_, n, _) => if zeq t n
                                       then Some l'
                                       else CalTicketWait b' c t l' to
                  | _               => None
                end
    end.
End CalLockOps.

Section CalLockOpsQ.

  Inductive qhead_status := LEMPTY | LGET | LHOLD.
  (* enqueue *)
  Definition enq {X: Type} (l: list X) (x: X) := l ++ (x::nil).

  (* returns (n * self_c * other_c * qst * q * tq)
   * where n    := now
   *       sctr := how long do I have left
   *       octr := how long do others have left
   *       qst  := queue status
   *       q    := queue of CPUs waiting
   *       tq   := queue of the hold time each CPU has requested
   *)
  Fixpoint Q_CalTicketLock (l: MultiLog):
      option (Z * nat * nat * qhead_status * list Z * list nat) :=
    match l with
    | nil => Some (0, O, fairness, LEMPTY, nil, nil)
    | TEVENT c e :: l' =>
      match Q_CalTicketLock l', e with
      | Some (n, sctr, octr, _, nil, nil), TTICKET (INC_TICKET p) =>
          (* when the queues are empty, we can only INC_TICKET *)
          Some (n, sctr, octr, LEMPTY, c::nil, p::nil)

      | Some (n, sctr, octr, qst, (_::_) as q, (_::_) as tq), TTICKET (INC_TICKET p) =>
          if in_dec zeq c q      (* were we previously in the queue? *)
          then None              (* because we should not have been *)
          else match octr with   (* decrement others' counters *)
               | O       => None (* timed out *)
               | S octr' => Some (n, sctr, octr', qst, q ++ c::nil, tq ++ p::nil)
               end

      | Some (n, sctr, octr, qst, c'::q', p'::tq'), TTICKET GET_NOW =>
          if zeq c c'                 (* was c at the head of the queue? *)
          then match qst with         (* yes; check queue state *)
               | LGET | LHOLD => None (* must be LEMPTY ~> LGET *)
               | LEMPTY       => Some (n, p', fairness, LGET, c'::q', p'::tq')
               end
          else match octr with        (* no; how long do we have to wait? *)
               | O => None            (* timed out *)
               | S octr' => Some (n, sctr, octr', qst, c'::q', p'::tq')
               end

      | Some (n, sctr, octr, qst, c'::q', (_::_) as tq), TTICKET HOLD_LOCK =>
          if zeq c c'                   (* was c at the head of the queue? *)
          then match qst with           (* yes; check queue state *)
               | LEMPTY | LHOLD => None (* must be LGET ~> LHOLD *)
               | LGET           => Some (n, sctr, fairness, LHOLD, c'::q', tq)
               end
          else None                     (* no; only queue head can obtain lock *)

      | Some (n, sctr, octr, qst, c'::q', _::tq'), TTICKET INC_NOW =>
          if zeq c c'                  (* was c at the head of the queue? *)
          then match qst with          (* yes; check queue state *)
               | LEMPTY | LGET => None (* must be LHOLD ~> LEMPTY *)
               | LHOLD         => Some (n + 1, O, fairness, LEMPTY, q', tq')
               end
          else None                    (* no; only head can release lock *)

      | Some (n, sctr, octr, qst, c'::q', (_::_) as tq), TSHARED _ =>
          if zeq c c'                   (* was c at the head of the queue? *)
          then match qst, sctr with     (* yes; decrement self ctr *)
               | LHOLD, S sctr' => Some (n, sctr', fairness, LHOLD, c'::q', tq)
               | _,     _       => None (* lock must be in held state *)
               end
          else None                     (* no; only head can perform mem ops *)

      | _, _ => None
      end
    end.

  (* b  := wait bound
   * c  := current CPU
   * l  := log
   * to := oracle
   *
   * advance l to when c is at the head of the wait queue,
   * i.e. when c can obtain the lock, with wait bound b
   *)
  Fixpoint Q_CalTicketWait (b: nat) (c: Z) (l: MultiLog) (to: MultiOracle):
                           option (list MultiOracleEvent) :=
    let l' := TEVENT c (TTICKET GET_NOW) :: to c l ++ l in
    match b, Q_CalTicketLock l' with
    | S b', Some (_, _, _, _, c'::q', _) => if zeq c c'
                                            then Some l'
                                            else Q_CalTicketWait b' c l' to
    | _,    _                            => None
    end.

  (* basically, snd \o Q_CalTicketLock (removing now) *)
  Fixpoint Q_CalLock (l: MultiLog):
      option (nat * nat * qhead_status * list Z * list nat) :=
    match l with
    | nil => Some (O, fairness, LEMPTY, nil, nil)
    | TEVENT c e :: l' =>
      match Q_CalLock l', e with
      | Some (sctr, octr, _, nil, nil), TTICKET (INC_TICKET p) =>
          (* when the queues are empty, we can only INC_TICKET *)
          Some (sctr, octr, LEMPTY, c::nil, p::nil)

      | Some (sctr, octr, qst, (_::_) as q, (_::_) as tq), TTICKET (INC_TICKET p) =>
          if in_dec zeq c q      (* were we previously in the queue? *)
          then None              (* because we should not have been *)
          else match octr with   (* decrement others' counters *)
               | O       => None (* timed out *)
               | S octr' => Some (sctr, octr', qst, q ++ c::nil, tq ++ p::nil)
               end

      | Some (sctr, octr, qst, c'::q', p'::tq'), TTICKET GET_NOW =>
          if zeq c c'                 (* was c at the head of the queue? *)
          then match qst with         (* yes; check queue state *)
               | LGET | LHOLD => None (* must be LEMPTY ~> LGET *)
               | LEMPTY       => Some (p', fairness, LGET, c'::q', p'::tq')
               end
          else match octr with        (* no; how long do we have to wait? *)
               | O => None            (* timed out *)
               | S octr' => Some (sctr, octr', qst, c'::q', p'::tq')
               end

      | Some (sctr, octr, qst, c'::q', (_::_) as tq), TTICKET HOLD_LOCK =>
          if zeq c c'                   (* was c at the head of the queue? *)
          then match qst with           (* yes; check queue state *)
               | LEMPTY | LHOLD => None (* must be LGET ~> LHOLD *)
               | LGET           => Some (sctr, fairness, LHOLD, c'::q', tq)
               end
          else None                     (* no; only queue head can obtain lock *)

      | Some (sctr, octr, qst, c'::q', _::tq'), TTICKET INC_NOW =>
          if zeq c c'                  (* was c at the head of the queue? *)
          then match qst with          (* yes; check queue state *)
               | LEMPTY | LGET => None (* must be LHOLD ~> LEMPTY *)
               | LHOLD         => Some (O, fairness, LEMPTY, q', tq')
               end
          else None                    (* no; only head can release lock *)

      | Some (sctr, octr, qst, c'::q', (_::_) as tq), TSHARED _ =>
          if zeq c c'                   (* was c at the head of the queue? *)
          then match qst, sctr with     (* yes; decrement self ctr *)
               | LHOLD, S sctr' => Some (sctr', fairness, LHOLD, c'::q', tq)
               | _,     _       => None (* lock must be in held state *)
               end
          else None                     (* no; only head can perform mem ops *)

      | _, _ => None
      end
    end.

  (* b  := wait bound
   * c  := current CPU
   * l  := log
   * to := oracle
   *
   * advance l to when c is at the head of the wait queue,
   * i.e. when c can obtain the lock, with wait bound b
   *)
  Fixpoint Q_CalWait (n: nat) (c: Z)
                     (l: MultiLog) (to: MultiOracle):
                     option (list MultiOracleEvent) :=
    let l' := TEVENT c (TTICKET GET_NOW) :: to c l ++ l in
    match n, Q_CalLock l' with
    | S n', Some (_, _, _, c'::q', _) => if zeq c c'
                                            then Some l'
                                            else Q_CalWait n' c l' to
    | _,    _                            => None
    end.

End CalLockOpsQ.

Section CalLockOpsH.

  Fixpoint H_CalLock (l: MultiLog): option (nat * qhead_status * option Z) :=
    match l with
    | nil => Some (O, LEMPTY, None)
    | TEVENT i e :: l' =>
      match H_CalLock l', e with
      | Some (self_c, LHOLD, Some i'), TTICKET REL_LOCK =>
          if negb (zeq i i') then None else
          Some (O, LEMPTY, None)

      | Some (self_c, LHOLD, Some i'), TSHARED _ =>
          if negb (zeq i i') then None else
          match self_c with
          | O         => None
          | S self_c' => Some (self_c', LHOLD, Some i')
          end

      | Some (_, LEMPTY, None), TTICKET (WAIT_LOCK n) =>
          Some (n, LHOLD, Some i)

      | _, _ => None
      end
    end.
End CalLockOpsH.

Section GetLog.

  (* Get latest shared memory event *)
  Fixpoint GetSharedMemEvent (l: MultiLog): option SharedMemEvent :=
    match l with
    | nil => None
    | TEVENT _ (TSHARED e) :: l' => Some e
    | _ :: l' => GetSharedMemEvent l'
    end.

End GetLog.



Section WaitTime.

  Fixpoint CalSumWait (l: list nat) :=
    match l with
    | nil     => O
    | a :: l' => (4 + a + CalSumWait l') % nat
    end.

  Definition rm_head {A: Type} (l: list A) :=
    match l with
      | nil => nil
      | _ :: l' => l'
    end.

  Definition CalStatus (h: qhead_status) :=
    match h with
      | LEMPTY => O
      | LHOLD => 1%nat
      | LGET => 2%nat
    end.

  Definition decrease_number (self_c other_c: nat) (h: qhead_status) (tq: list nat) :=
    match h with
      | LEMPTY => (other_c + (CalSumWait tq) * fairness) % nat
      | _ => (other_c + (self_c + CalSumWait (rm_head tq) + CalStatus h)  * fairness)%nat
    end.

  (* given waiting list l, calculate how long one has to left to wait *)
  Definition CalWaitTime (l: list nat) :=
    S (fairness + (CalSumWait l) * fairness).

End WaitTime.

Section Invariants.

  Section QLOCK_POOL_LENGTH_INV.

    Definition qlock_length (l: MultiLog):=
      forall self_c other_c b q tq
             (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
        (forall i, In i q -> 0 <= i < TOTAL_CPU).

    Definition qlock_pool_length (l: MultiLogPool):=
      forall lk q (Hdef: ZMap.get lk l = q),
        qlock_length q.

    Lemma qlock_pool_length_gss:
      forall l l' z (Hq: qlock_pool_length l) (Hlen: qlock_length l'),
        qlock_pool_length (ZMap.set z (l') l).
    Proof.
      intros. unfold qlock_pool_length in *; intros.
      destruct (zeq lk z); subst.
      - rewrite ZMap.gss in *. trivial.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma qlock_length_cons:
      forall i e l (Hrange: 0 <= i < TOTAL_CPU) (Hl: qlock_length l),
        qlock_length (TEVENT i e :: l).
    Proof.
      unfold qlock_length; intros.
      simpl in Hcal.
      subdestruct; inv Hcal; eauto.
      - inv H; trivial. inv H0.
      - eapply Hl; eauto. right; trivial.
      - rewrite app_comm_cons in H.
        eapply in_app_or in H.
        inv H; eauto. inv H0; trivial. inv H.
      - eapply Hl; eauto. right; trivial.
      - rewrite app_comm_cons in H.
        eapply in_app_or in H.
        inv H; eauto. inv H0; trivial. inv H.
    Qed.

    Lemma qlock_length_append:
      forall l' l (Hlen1: qlock_length l)
                  (Hto: forall i0 e, In (TEVENT i0 e) l' -> 0 <= i0 < TOTAL_CPU),
        qlock_length (l' ++ l).
    Proof.
      induction l'; simpl; intros; trivial.
      destruct a.
      eapply qlock_length_cons; eauto.
    Qed.

    Lemma Q_CalWait_length:
      forall n l l' i to
             (Hrange: 0 <= i < TOTAL_CPU)
             (Hlen: qlock_length l)
             (Hto: forall q i0 e, In (TEVENT i0 e) (to i q) -> 0 <= i0 < TOTAL_CPU)
             (Hwait: Q_CalWait n i l to = Some l'),
        qlock_length l'.
    Proof.
      Local Transparent Q_CalWait.
      induction n; simpl; intros; try congruence.
      subdestruct; subst.
      - inv Hwait.
        eapply qlock_length_cons; eauto.
        eapply qlock_length_append; eauto.
      - eapply IHn; try eapply Hwait; eauto.
        eapply qlock_length_cons; eauto.
        eapply qlock_length_append; eauto.
    Qed.

  End QLOCK_POOL_LENGTH_INV.

  Section CORRECT_QLOCK_POOL_STATUS_INV.

    Definition correct_qlock_status (l: MultiLog) (k: LockStatus) (cpu: Z):=
      forall self_c other_c b q tq
             (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
        (k = LockFalse -> ~ In cpu q) /\
          (forall lb, k = LockOwn lb ->
            exists q', q = cpu :: q' /\ b = LHOLD /\ ~ In cpu q').

    Definition correct_qlock_pool_status (l: MultiLogPool) (k: ZMap.t LockStatus) (cpu: Z):=
      forall lk q (Hdef: ZMap.get lk l = q),
        correct_qlock_status q (ZMap.get lk k) cpu.

    Lemma correct_qlock_pool_status_gss':
      forall l k c l' z
             (HP: correct_qlock_pool_status l k c)
             (Hc: correct_qlock_status l' (ZMap.get z k) c),
        correct_qlock_pool_status (ZMap.set z (l') l) k c.
    Proof.
      Local Transparent Q_CalLock.
      intros. unfold correct_qlock_pool_status in *; intros.
      destruct (zeq lk z); subst.
      - rewrite ZMap.gss in *. trivial.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Inductive MatchLock: LockStatus -> LockStatus -> Prop :=
    | MLFALSE: MatchLock LockFalse LockFalse
    | MLOWN: forall a b, MatchLock (LockOwn a) (LockOwn b).

    Lemma correct_qlock_status_Match:
      forall l k k' c
             (Hc: correct_qlock_status l k c)
             (Hl: MatchLock k' k),
        correct_qlock_status l k' c.
    Proof.
      intros. unfold correct_qlock_status in *; intros.
      exploit Hc; eauto.
      intros (HF & HO).
      split; intros; subst; eauto.
      - inv Hl. eapply HF; eauto.
      - inv Hl. eapply HO; eauto.
    Qed.

    Lemma correct_qlock_pool_status_gss:
      forall l k c l' k' z
             (HP: correct_qlock_pool_status l k c)
             (Hc: correct_qlock_status l' k' c),
        correct_qlock_pool_status (ZMap.set z (l') l) (ZMap.set z k' k) c.
    Proof.
      intros.
      unfold correct_qlock_pool_status in *; intros.
      destruct (zeq lk z); subst.
      - repeat rewrite ZMap.gss in *.
        trivial.
      - repeat rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma correct_qlock_pool_status_gss_match:
      forall l k c l' k' z
             (HP: correct_qlock_pool_status l k c)
             (Hc: correct_qlock_status l' (ZMap.get z k) c)
             (Hl: MatchLock k' (ZMap.get z k)),
        correct_qlock_pool_status (ZMap.set z (l') l) (ZMap.set z k' k) c.
    Proof.
      intros. eapply correct_qlock_pool_status_gss; eauto.
      eapply correct_qlock_status_Match; eauto.
    Qed.


    Lemma Q_CalLock_unique:
      forall l self_c other_c b q tq
             (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
        forall i, In i q -> count_occ zeq q i = 1%nat.
    Proof.
      induction l; simpl; intros.
      { inv Hcal. inv H. }
      subdestruct
      ; inv Hcal
      ; try (exploit IHl; now eauto)
      ; try (match goal with H: ~In ?z (?z::?q) |- _ => contradiction H end;
            left; reflexivity
        )
      .
      - simpl in H. destruct H as [HF|HF]; inv HF.
        simpl. rewrite zeq_true. trivial.
      - specialize (IHl _ _ _ _ _ refl_equal).
        exploit (IHl i).
        { right; trivial. }
        simpl. destruct (zeq i z); subst.
        + rewrite zeq_true. intros.
          eapply (count_occ_In zeq) in H.
          omega.
        + rewrite zeq_false; auto.
      - specialize (IHl _ _ _ _ _ refl_equal).
        destruct (zeq i cpuid); subst.
        + rewrite app_comm_cons.
          rewrite count_occ_append.
          replace (count_occ zeq (z :: l3) cpuid) with O.
          { simpl. f_equal. rewrite zeq_true. trivial. }
          destruct (count_occ zeq (z :: l3) cpuid) eqn: Hpos; trivial.
          assert (Hpos': (count_occ zeq (z :: l3) cpuid > O)%nat) by omega.
          eapply count_occ_In in Hpos'.
          destruct Hpos'.
          * subst; congruence.
          * match goal with H: ~In cpuid (_::l3) |- _ => contradiction H end.
            right. assumption.

        + rewrite app_comm_cons.
          rewrite count_occ_append.
          rewrite IHl.
          { simpl. rewrite zeq_false; auto. }
          {
            rewrite app_comm_cons in H.
            apply in_app_or in H.
            destruct H as [HF| HF]; trivial.
            destruct HF as [HF'|HF']; inv HF'. congruence.
          }
    Qed.

    Lemma correct_status_HOLD_LOCK:
      forall l c b,
        correct_qlock_status (TEVENT c (TTICKET HOLD_LOCK) :: l) (LockOwn b) c.
    Proof.
      unfold correct_qlock_status.
      simpl; intros.
      subdestruct; inv Hcal.
      split; intros. inv H. inv H.
      refine_split'; trivial.
      intro HF.
      assert (Hin: In z (z :: l3)).
      { left; trivial. }
      eapply Q_CalLock_unique in Hdestruct; eauto.
      simpl in Hdestruct. rewrite zeq_true in Hdestruct.
      inv Hdestruct. eapply (count_occ_In zeq) in HF. omega.
    Qed.

    Lemma correct_status_INC_NOW:
      forall l c lb
             (Hc: correct_qlock_status l (LockOwn lb) c),
        correct_qlock_status (TEVENT c (TTICKET INC_NOW) :: l) LockFalse c.
    Proof.
      unfold correct_qlock_status.
      simpl; intros.
      subdestruct; inv Hcal.
      exploit Hc; eauto.
      intros (_ & HL). specialize (HL _ refl_equal).
      destruct HL as (q' & Heq & _ & Hnot). inv Heq.
      split; intros; trivial. inv H.
    Qed.

  End CORRECT_QLOCK_POOL_STATUS_INV.

  Section VALID_QLOCK_POOL_INV.

    Definition valid_qlock (l: MultiLog) :=
      exists self_c other_c b q tq,
        Q_CalLock l = Some (self_c, other_c, b, q, tq).

    Definition valid_qlock_pool (l: MultiLogPool):=
      forall r q (Hdef: ZMap.get r l = q),
        valid_qlock q.

    Lemma valid_qlock_pool_init:
      valid_qlock_pool (ZMap.init nil).
    Proof.
      unfold valid_qlock_pool; intros.
      rewrite ZMap.gi in Hdef.
      unfold valid_qlock. inv Hdef.
      repeat eexists.
    Qed.

    Lemma valid_qlock_pool_gss:
      forall t l p
             (Hvalid: valid_qlock_pool t)
             (Hlock: valid_qlock l),
        valid_qlock_pool (ZMap.set p (l) t).
    Proof.
      unfold valid_qlock_pool; intros.
      destruct (zeq p r); subst.
      - rewrite ZMap.gss in *. trivial.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma valid_qlock_pool_gss':
      forall t l p x
             (Hvalid: valid_qlock_pool t)
             (Hlock: Q_CalLock l = Some x),
        valid_qlock_pool (ZMap.set p (l) t).
    Proof.
      intros. eapply valid_qlock_pool_gss; eauto.
      unfold valid_qlock.
      destruct x. repeat destruct p0. eauto 20.
    Qed.

  End VALID_QLOCK_POOL_INV.

  Section VALID_MULTI_ORACLE_POOL_INV.

    Definition valid_multi_oracle_domain (o: MultiOracle) :=
      forall i i0 e l (Hin: In (TEVENT i0 e) (o i l)),
      i0 <> i /\ 0 <= i0 < TOTAL_CPU.

    Definition valid_multi_oracle_queue (o: MultiOracle):=
      forall i l
             (Hin': forall i1 e1, In (TEVENT i1 e1) l -> 0 <= i1 < TOTAL_CPU)
             (Hin: valid_qlock l)
             (Hlast: match l with TEVENT c0 e0 :: l' => c0 = i | _ => True end),
      exists self_c other_c b q tq,
        Q_CalLock ((o i l) ++ l) = Some (self_c, other_c, b, q, tq) /\
        other_c <> O.

    Definition valid_multi_oracle_pool (o: MultiOraclePool):=
      forall r,
        valid_multi_oracle_domain (ZMap.get r o) /\
        valid_multi_oracle_queue (ZMap.get r o).

    Lemma Q_CalWait_valid_last:
      forall n l l' i to
             (Hvalid: forall i1 e1,
                        In (TEVENT i1 e1) l -> 0 <= i1 < TOTAL_CPU)
             (Hto: valid_multi_oracle_domain to)
             (Hwait: Q_CalWait n i l to = Some l')
             (Hi: 0 <= i < TOTAL_CPU),
      (forall i1 e1,
         In (TEVENT i1 e1) l' -> 0 <= i1 < TOTAL_CPU).
    Proof.
      induction n; simpl; intros; try congruence.
      subdestruct; subst.
      - inv Hwait.
        inv H.
        + inv H0. eauto.
        + eapply in_app_or in H0. inv H0.
          * eapply Hto. eauto.
          * eapply Hvalid. eauto.
      - eapply IHn; try eapply Hwait; eauto.
        intros. inv H0.
        + inv H1. eauto.
        + eapply in_app_or in H1. inv H1.
          * eapply Hto. eauto.
          * eapply Hvalid. eauto.
    Qed.

  End VALID_MULTI_ORACLE_POOL_INV.

  Section VALID_LAST_POOL_INV.

    Definition valid_last (c: Z) (q: MultiLog) :=
      (forall i1 e1, In (TEVENT i1 e1) q -> 0 <= i1 < TOTAL_CPU) /\
      (match q with nil => True | TEVENT c0 _ :: _ => c0 = c end).

    Definition valid_last_pool (c: Z) (l: MultiLogPool) :=
      forall lk q (Hdef: ZMap.get lk l = q),
      valid_last c q.

    Lemma valid_last_pool_gss:
      forall c l l' z (HP: valid_last_pool c l) (Hc: valid_last c l'),
      valid_last_pool c (ZMap.set z (l') l).
    Proof.
      intros. unfold valid_last_pool in *; intros.
      destruct (zeq lk z); subst.
      - rewrite ZMap.gss in *. trivial.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma valid_last_event:
      forall c l e (Hc: 0 <= c < TOTAL_CPU)
             (Hvalid: valid_last c l),
        valid_last c (TEVENT c e :: l).
    Proof.
      unfold valid_last. intros. destruct Hvalid as (Hvalid1 & Hvalid2).
      split; trivial. intros. inv H.
      - inv H0. eauto.
      - eauto.
    Qed.

  End VALID_LAST_POOL_INV.

End Invariants.
```
