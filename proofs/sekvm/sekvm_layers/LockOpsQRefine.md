# ProofHigh

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

Require Import RData.
Require Import CalLock.
Require Import Constants.
Require Import LockOpsQ.Spec.
Require Import HypsecCommLib.
Require Import LockOpsQ.Layer.
Require Import LockOps.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsQProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := LockOpsQ_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := LockOps_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
        icore_rel         : icore hadt = icore ladt;
        ihost_rel         : ihost hadt = ihost ladt;
        tstate_rel        : tstate hadt = tstate ladt;
        curid_rel         : curid hadt = curid ladt;
        cur_vmid_rel      : cur_vmid hadt = cur_vmid ladt;
        cur_vcpuid_rel    : cur_vcpuid hadt = cur_vcpuid ladt;
        regs_rel          : regs hadt = regs ladt;
        (* lock_rel          : lock hadt = lock ladt; *)
        region_cnt_rel    : region_cnt hadt = region_cnt ladt;
        regions_rel       : regions hadt = regions ladt;
        shadow_ctxts_rel  : shadow_ctxts hadt = shadow_ctxts ladt;
        smmu_conf_rel     : smmu_conf hadt = smmu_conf ladt;
        log_rel           : log hadt = log ladt;
        oracle_rel        : oracle hadt = oracle ladt;
        doracle_rel       : doracle hadt = doracle ladt;
        core_doracle_rel  : core_doracle hadt = core_doracle ladt;
        data_log_rel      : data_log hadt = data_log ladt;
        core_data_log_rel : core_data_log hadt = core_data_log ladt;
        shared_rel        : shared hadt = shared ladt
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

    Section NUM_LEMMA. (* FIXME: put in HypsecCommLib *)

      Lemma l_len_cons:
        forall {A:Type} (z: A) l,
          Z.of_nat (length (z :: l)) = Z.of_nat (length l) + 1.
      Proof.
        Local Opaque Z.of_nat.
        simpl; intros.
        rewrite Nat2Z.inj_succ. omega.
      Qed.

      Local Transparent Z.of_nat.
      Lemma count_occ_append:
        forall l l' x,
          (count_occ zeq (l ++ l') x = count_occ zeq l x + count_occ zeq l' x) % nat.
      Proof.
        induction l; simpl; intros; auto.
        destruct (zeq a x); subst.
        - erewrite IHl. omega.
        - eauto.
      Qed.

      Lemma q_unique:
        forall n q (Hrange: forall i, In i q -> 0 <= i < Z.of_nat n)
               (Hcount: forall i, In i q -> count_occ zeq q i = 1%nat),
          Z.of_nat (length q) < Z.of_nat n + 1.
      Proof.
        induction n; intros.
        {
          destruct q.
          - simpl; omega.
          - exploit (Hrange z); eauto.
            left; trivial. simpl; intros. omega.
        }
        {
          destruct (in_dec zeq (Z.of_nat (n)) q).
          - eapply in_split in i.
            destruct i as (l1 & l2 & Heq); subst.
            assert (Hlen: Z.of_nat (length (l1 ++ l2)) < Z.of_nat n + 1).
            {
              assert (Hnot: ~ In (Z.of_nat n) (l1 ++ l2)).
              {
                intro HF.
                exploit (Hcount (Z.of_nat n)).
                - eapply in_or_app. right.
                  left. trivial.
                - rewrite count_occ_append.
                  rewrite count_occ_cons_eq; trivial.
                  intros.
                  eapply in_app_or in HF.
                  destruct HF;
                  eapply (count_occ_In zeq) in H0;
                  omega.
              }
              eapply IHn; eauto.
              - intros. destruct (zeq i (Z.of_nat n)); subst; [congruence|].
                exploit (Hrange i).
                + eapply in_app_or in H. destruct H.
                  * eapply in_or_app. left. trivial.
                  * eapply in_or_app. right. right. trivial.
                + rewrite Nat2Z.inj_succ. 
                  intros. omega.
              - intros. rewrite count_occ_append.
                destruct (zeq i (Z.of_nat n)); subst. congruence.
                exploit (Hcount i); eauto.
                + eapply in_app_or in H. destruct H.
                  * eapply in_or_app. left. trivial.
                  * eapply in_or_app. right. right. trivial.
                + rewrite count_occ_append.
                  rewrite count_occ_cons_neq; auto. 
            }
            rewrite Nat2Z.inj_succ.
            rewrite app_length in *.
            rewrite Nat2Z.inj_add in *.
            rewrite l_len_cons. omega.
          - exploit IHn; eauto.
            + intros. exploit Hrange; eauto.
              rewrite Nat2Z.inj_succ.
              intros.
              destruct (zeq i (Z.of_nat n)); subst.
              * elim n0; trivial.
              * omega.
            + intros.
              rewrite Nat2Z.inj_succ.
              omega.
        }
      Qed.

    End NUM_LEMMA.

    Section CALLOCK_LEMMA.

      Local Transparent Q_CalTicketLock Q_CalLock Q_CalTicketWait Q_CalWait CalTicketLock CalTicketWait.

      Lemma Q_CalLock_imply_ticket:
        forall l self_c other_c b q tq
               (Hqcal_lock: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
        exists n, Q_CalTicketLock l = Some (n, self_c, other_c, b, q, tq).
      Proof.
        induction l; intros.
        { inv Hqcal_lock; simpl; eauto. }
        simpl in *.  destruct a; contra_inv.
        destruct (Q_CalLock l) eqn: Hlock; contra_inv.
        repeat destruct p.
        exploit IHl; eauto.
        intros (n1 & ->).
        subdestruct; inv Hqcal_lock; eauto.
      Qed.

      Lemma Q_CalWait_imply_ticket:
        forall wait_time curid l o l0
               (Hqcal_wait: Q_CalWait wait_time curid l o = Some l0),
          Q_CalTicketWait wait_time curid l o = Some l0.
      Proof.
        induction wait_time; intros.
        - inv Hqcal_wait.
        - simpl in *.
          destruct (Q_CalLock (o curid l ++ l)) eqn: Hlock; contra_inv.
          repeat (destruct p).
          eapply Q_CalLock_imply_ticket in Hlock.
          destruct Hlock as (n1 & ->).
          subdestruct; eauto.
      Qed.

      Lemma CalTicketLock_Q_imply:
        forall l n self_c other_c b q tq
               (Hqlock: Q_CalTicketLock l = Some (n, self_c, other_c, b, q, tq)),
          CalTicketLock l = Some (n + Z.of_nat (length q), n, tq).
      Proof.
        induction l; intros.
        { inv Hqlock. simpl. trivial. }
        simpl in *.
        destruct a; contra_inv.
        destruct (Q_CalTicketLock l); contra_inv.
        repeat (destruct p).
        exploit IHl; eauto; clear IHl.
        intros Heq; rewrite Heq; clear Heq.
        subdestruct; inversion Hqlock; subst; eauto;
        try match goal with
          |- context[Z.pos (Pos.of_succ_nat ?n)] =>
            replace (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)) by
            reflexivity
          end.
        - replace (n + 0 + 1) with (n + 1) by omega; eauto.
        - f_equal. f_equal. f_equal.
          rewrite Nat2Z.inj_succ.
          omega.
        - f_equal. f_equal. f_equal.
          rewrite (List.app_comm_cons _ (_::nil) _).
          rewrite (List.app_length (_::_) (_::nil)).
          simpl (length _).
          rewrite Nat2Z.inj_succ.
          rewrite plus_comm.
          rewrite Nat2Z.inj_succ.
          rewrite Nat2Z.inj_succ.
          omega.
        - f_equal. f_equal. f_equal.
          rewrite Nat2Z.inj_succ.
          omega.
        - f_equal. f_equal. f_equal.
          rewrite (List.app_comm_cons _ (_::nil) _).
          rewrite (List.app_length (_::_) (_::nil)).
          simpl (length _).
          rewrite Nat2Z.inj_succ.
          rewrite plus_comm.
          rewrite Nat2Z.inj_succ.
          rewrite Nat2Z.inj_succ.
          omega.
      Qed.

      Lemma Q_CalTicketLock_in_head':
        forall l' l n n' b b' q q0 q1 curid self_c self_c' other_c other_c' tq tq'
               (Hqlock : Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (HnotIn: ~ In curid q)
               (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid)
               (Hqlock1 : Q_CalTicketLock (l' ++ l) = Some (n', self_c', other_c', b', q1, tq')),
          In curid q1.
      Proof.
        induction l'; intros.
        {
          simpl in Hqlock1. rewrite Hqlock in Hqlock1. inv Hqlock1.
          eapply list_In_middle.
        }
        rewrite <- app_comm_cons in Hqlock1.
        destruct a. simpl in Hqlock1.
        destruct (Q_CalTicketLock (l' ++ l)) eqn: Hqlock2; contra_inv.
        assert (Hin_append: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid).
        { intros i0 e0 Hin'. eapply Hin. right. apply Hin'. }
        repeat destruct p.
        subdestruct; inv Hqlock1; eauto;
        try match goal with
        |- context[?x::?l++?y::nil] =>
            replace (x::l++y::nil) with ((x::l)++(y::nil)) by auto
        end;
        try ( try match goal with H:context[in_dec] |- _ => clear H end;
              match goal with H:context[~In ?z (?z::_)] |- _ => contradict H end;
              left; reflexivity
            );
        exploit IHl'; try eassumption.
        - inversion 1.
        - specialize (Hin z0 (TTICKET INC_NOW)).
          destruct 1; eauto; subst.
          exploit Hin; [left| |intro]; easy.
        - intros; apply List.in_or_app; left; assumption.
      Qed.

      Lemma Q_CalTicketLock_neq_head':
        forall l' l n n' b b' q q0 q1 curid head self_c self_c' other_c other_c' tq tq'
               (Hqlock : Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (HnotIn: ~ In curid q)
               (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid)
               (Hqlock1 : Q_CalTicketLock (l' ++ l) = Some (n', self_c', other_c', b', head :: q1, tq'))
               (Hnot_head: head <> curid),
        exists q2 q3, q1 = q2 ++ curid :: q3
                      /\ n' + Z.of_nat (length (head :: q2)) = n + Z.of_nat (length q)
                      /\ ~ In curid q2.
      Proof.
        induction l'; intros.
        { simpl in Hqlock1. rewrite Hqlock in Hqlock1. inv Hqlock1.
          destruct q.
          { inv H4. elim Hnot_head. trivial. }
          rewrite <- list_append_trans in H4. inv H4.
          refine_split'; trivial.
          eapply list_not_in_append_re; eauto.
        }
        rewrite <- app_comm_cons in Hqlock1.
        destruct a. simpl in Hqlock1.
        destruct (Q_CalTicketLock (l' ++ l)) eqn: Hqlock2; contra_inv.
        assert (Hin_append: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid).
        { intros i0 e0 Hin'. eapply Hin. right. apply Hin'. }
        repeat destruct p.
        subdestruct
        ; inv Hqlock1
        ; eauto
        ; try match goal with
          |- context[?x::?l++?y::nil] =>
              replace (x::l++y::nil) with ((x::l)++(y::nil)) by auto
          end
        ; try ( try match goal with H:context[in_dec] |- _ => clear H end;
                match goal with H:context[~In ?z (?z::_)] |- _ => contradict H end;
                left; reflexivity
            )
        ; try ( exploit IHl'; try eassumption;
                intros (q2 & q3 & Heq & Heq' & HnotIn1); subst;
                refine_split'; trivial ; fail
            )
        .
        - exploit Q_CalTicketLock_in_head'; try eapply Hqlock2; eauto; inversion 1.
        - exploit IHl'; try eassumption.
          { specialize (Hin z0 (TTICKET INC_NOW)). eapply Hin; left; easy. }
          intros (q2 & q3 & Heq & Heq' & HnotIn1). subst.
          destruct q2; inv Heq.
          { elim Hnot_head. easy. }
          refine_split'; trivial.
          { rewrite <- Heq'. simpl. now xomega. }
          eapply list_not_in_append_re; eauto.
        - exploit IHl'; try eassumption.
          intros (q2 & q3 & Heq & Heq' & HnotIn1); subst.
          rewrite <- List.app_assoc.
          rewrite <- List.app_comm_cons.
          refine_split'; trivial.
      Qed.

      Lemma Q_CalTicketLock_eq_head':
        forall l' l n n' b b' q q0 q1 curid self_c self_c' other_c other_c' tq tq'
               (Hqlock : Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (HnotIn: ~ In curid q)
               (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid)
               (Hqlock1 : Q_CalTicketLock (l' ++ l) = Some (n', self_c', other_c', b', curid :: q1, tq')),
          n' = n + Z.of_nat (length q).
      Proof.
        induction l'; intros.
        { simpl in Hqlock1. rewrite Hqlock in Hqlock1. inv Hqlock1.
          eapply list_prefix_nil in HnotIn; eauto. subst. simpl.
          Local Transparent Z.of_nat. xomega.
        }
        rewrite <- app_comm_cons in Hqlock1.
        destruct a. simpl in Hqlock1.
        destruct (Q_CalTicketLock (l' ++ l)) eqn: Hqlock2; contra_inv.
        assert (Hin_append: forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid).
        { intros i0 e0 Hin'. eapply Hin. right. apply Hin'. }
        repeat destruct p.
        subdestruct
        ; inv Hqlock1
        ; eauto
        ; try ( try match goal with H:context[in_dec] |- _ => clear H end;
                match goal with H:context[~In ?z (?z::_)] |- _ => contradict H end;
                left; reflexivity
            )
        .
        - exploit Q_CalTicketLock_in_head'; try eapply Hqlock2; eauto.
          inversion 1.
        - exploit Q_CalTicketLock_neq_head'; try eapply Hqlock2; eauto.
          { specialize (Hin z0 (TTICKET INC_NOW)). eapply Hin; left; trivial. }
          intros (q2 & q3 & Heq & Heq' & Hin').
          eapply list_prefix_nil in Hin'; eauto; subst.
          simpl in Heq'; assumption.
      Qed.

      Lemma Q_CalTicketLock_eq_head:
        forall l n n' b b' q q0 q1 curid self_c self_c' other_c other_c' tq tq' o
               (Hqlock : Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (HnotIn: ~ In curid q)
               (Horacle_domain : valid_multi_oracle_domain o)
               (Hqlock1 : Q_CalTicketLock (o curid l ++ l) = Some (n', self_c', other_c', b', curid :: q1, tq')),
          n' = n + Z.of_nat (length q).
      Proof.
        intros. eapply Q_CalTicketLock_eq_head'; eauto.
        intros. eapply Horacle_domain; eauto.
      Qed.

      Lemma Q_CalTicketLock_neq_head:
        forall l n n' b b' q q0 q1 curid head self_c self_c' other_c other_c' tq tq' o
               (Hqlock : Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (HnotIn: ~ In curid q)
               (Horacle_domain : valid_multi_oracle_domain o)
               (Hqlock1 : Q_CalTicketLock (o curid l ++ l) = Some (n', self_c', other_c', b', head :: q1, tq'))
               (Hnot_head: head <> curid),
        n' < n + Z.of_nat (length q)
        /\ (exists q2 q3, q1 = q2 ++ curid :: q3
                      /\ n' + Z.of_nat (length (head :: q2)) = n + Z.of_nat (length q)
                      /\ ~ In curid q2).
      Proof.
        intros. exploit Q_CalTicketLock_neq_head'; eauto.
        {
          intros. eapply Horacle_domain; eauto.
        }
        intros (q2 & q3 & Heq & Hn' & HnotIn1).
        refine_split'; eauto.
        rewrite <- Hn'. simpl. xomega.
      Qed.

      Lemma CalTicketWait_Q_imply:
        forall wait_time curid l o l0 n self_c other_c b q q0 tq t
               (Hqlock: Q_CalTicketLock l = Some (n, self_c, other_c, b, q ++ curid :: q0, tq))
               (Hwait: Q_CalTicketWait wait_time curid l o = Some l0)
               (HnotIn: ~ In curid q)
               (Ht: t = n + Z.of_nat (length (q)))
               (Horacle_domain : valid_multi_oracle_domain o),
          CalTicketWait wait_time curid t l o = Some l0.
      Proof.
        induction wait_time; intros; simpl in *; try (inv Hwait; fail).
        destruct (Q_CalTicketLock (o curid l ++ l)) eqn: Hqlock1; contra_inv.
        repeat (destruct p).
        exploit CalTicketLock_Q_imply; eauto.
        intros Heq; rewrite Heq; clear Heq.
        subdestruct; inv Hwait.
        - exploit Q_CalTicketLock_eq_head; eauto.
          intros; subst; rewrite zeq_true; easy.
        - exploit Q_CalTicketLock_neq_head; eauto.
          match goal with
            H: Q_CalTicketWait _ _ _ _ = Some _ |- _ => rename H into Hwait
          end.
          rewrite Hwait.
          intros (Hlt & (q2 & q3 & Heq & Hz & HnotIn1)); subst.
          eapply list_not_in_append in HnotIn1; eauto.
          rewrite zeq_false by omega.
          exploit IHwait_time; try eapply Hwait; eauto.
          { simpl. rewrite Hqlock1. rewrite zeq_false; auto. }
          rewrite <- Hz. trivial.
      Qed.

      Lemma CalTicketWait_Q_imply':
        forall wait_time curid l l' o l0 n self_c other_c b q  tq t bound
               (Hl: l = TEVENT curid (TTICKET (INC_TICKET bound)) :: l')
               (Hqlock: Q_CalTicketLock l = Some (n, self_c, other_c, b, q, tq))
               (Hwait: Q_CalTicketWait wait_time curid l o = Some l0)
               (Ht: t = n + Z.of_nat (length (q)) - 1)
               (Horacle_domain : valid_multi_oracle_domain o),
          CalTicketWait wait_time curid t l o = Some l0.
      Proof.
        intros. subst. 
        assert (Hq: exists q0, q = q0 ++ (curid::nil) /\ ~ In curid q0).
        {
          simpl in Hqlock. subdestruct; inv Hqlock
          ; try (exists nil; split; [reflexivity|inversion 1])
          ; try (exists (z :: l2)
                ; split; [reflexivity|inversion 1; congruence])
          ; try (exists (z :: l3)
                ; split; [reflexivity|inversion 1; congruence])
          .
        }
        destruct Hq as (q0 & Hq & HnotIn); subst.
        eapply CalTicketWait_Q_imply; eauto.
        rewrite app_length. simpl.
        replace ((length q0 + 1)%nat) with (S (length q0)) by omega.
        repeat rewrite Nat2Z.inj_succ.
        omega.
      Qed.

    End CALLOCK_LEMMA.

    Section FreshPrim.

      Lemma wait_qlock_spec_exists:
        forall habd habd' labd lk f
               (Hhigh: Layer.high_level_invariant habd)
               (Hspec: wait_qlock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
        exists labd', wait_qlock_spec0 lk labd = Some labd' /\
                      relate_RData f habd' labd'.
      Proof.
        unfold wait_qlock_spec0, Spec.wait_lock_spec, wait_qlock_spec.
        intros.
        inversion Hrel.
        revert Hspec.
        replace (log habd)    with (log labd)     by assumption.
        replace (curid habd)  with (curid labd)   by assumption.
        replace (oracle habd) with (oracle labd)  by assumption.
        intro Hspec.
        remember (lk @ (log labd)) as m.
        destruct (lk @ (lock habd)); try discriminate.
        destruct (
            Q_CalLock
              (TEVENT (curid labd)
                  (TTICKET (INC_TICKET (Z.to_nat lock_bound))) ::
              lk @ (oracle labd) (curid labd) m ++ m))
            eqn:Hdestruct4;
          try discriminate.
        repeat destruct p.
        destruct (
            Q_CalWait (CalWaitTime l) (curid labd)
              (TEVENT (curid labd)
                (TTICKET (INC_TICKET (Z.to_nat lock_bound))) ::
              lk @ (oracle labd) (curid labd) m ++ m) lk @ (oracle labd))
            eqn:Hdestruct9;
          try discriminate.
        destruct (Q_CalLock (TEVENT (curid labd) (TTICKET HOLD_LOCK) :: l1));
          try discriminate.
        inv Hspec.
        assert (Hlt: TOTAL_CPU + 1 > Z.of_nat (length l0)).
        {
          inversion Hhigh.
          remember (lk @ (log labd)) as m.
          assert (Hlen: qlock_length (TEVENT (curid habd) (TTICKET (INC_TICKET (Z.to_nat lock_bound)))
                                             :: ZMap.get lk (oracle habd) (curid habd) m ++ m)).
          {
            eapply qlock_length_cons; eauto.
            eapply qlock_length_append; eauto.
            - eapply qlock_pool_length_inv.
              replace (log habd) with (log labd) by assumption.
              rewrite Heqm. reflexivity.
            - intros. eapply valid_multi_oracle_pool_inv; eauto.
          }
          unfold qlock_length in Hlen.
          replace (curid labd) with (curid habd) in Hdestruct4 by assumption.
          replace (oracle labd) with (oracle habd) in Hdestruct4 by assumption.
          specialize (Hlen _ _ _ _ _ Hdestruct4).
          pose proof (Q_CalLock_unique _ _ _ _ _ _ Hdestruct4).
          specialize (q_unique (8%nat)). simpl.
          intros HF.
          apply Zle_succ_gt.
          apply Zlt_le_succ.
          eapply HF; eauto.
        }
        eapply Q_CalLock_imply_ticket in Hdestruct4.
        destruct Hdestruct4 as (n2 & HCalTL).
        eapply Q_CalWait_imply_ticket in Hdestruct9.
        exploit CalTicketWait_Q_imply'; eauto.
        {
          replace (oracle labd) with (oracle habd) by assumption.
          eapply valid_multi_oracle_pool_inv; eauto.
        }
        intros Heq.
        eapply CalTicketLock_Q_imply in HCalTL. rewrite HCalTL.
        rewrite zle_false by omega.
        rewrite Heq; clear Heq.
        refine_split'; constructor; simpl; trivial.
      Qed.

      Lemma pass_qlock_spec_exists:
        forall habd habd' labd lk f
               (Hspec: pass_qlock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', pass_qlock_spec0 lk labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold pass_qlock_spec, pass_qlock_spec0, Spec.pass_lock_spec.
        intros. inversion Hrel.
        subdestruct; inversion Hspec; subst.
        replace (log habd) with (log labd) in * by assumption.
        remember (ZMap.get lk labd.(log)) as m.
        replace (curid habd) with (curid labd) by assumption.
        refine_split'; simpl; trivial.
        constructor; simpl; trivial.
      Qed.

      Lemma pass_qlock_spec_ref:
        compatsim (crel RData RData) (gensem pass_qlock_spec) pass_qlock_spec_low.
      Proof.
        Opaque pass_qlock_spec.
        compatsim_simpl (@match_RData).
        exploit pass_qlock_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

    End FreshPrim.

  End WITHMEM.

End LockOpsQProofHigh.
```
