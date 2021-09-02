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
Require Import HypsecCommLib.
Require Import LockOpsH.Spec.
Require Import LockOpsH.Layer.
Require Import LockOpsQ.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsHProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := LockOpsH_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := LockOpsQ_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Section RelationHelpers. (* Ported from HTicketLockOpGenDef *)

      Fixpoint relate_log (l: MultiLog): option (MultiLog * list nat) :=
        match l with
        | nil => Some (nil, nil)
        | TEVENT i e :: l' =>
            match relate_log l', e with
            | Some (ll, tq), TTICKET (INC_TICKET p) =>
                Some (ll, tq ++ (p::nil))
            | Some (ll, tq), TTICKET GET_NOW =>
                Some (ll, tq)
            | Some (ll, (p::_) as tq), TTICKET HOLD_LOCK =>
                Some (TEVENT i (TTICKET (WAIT_LOCK p))::ll, tq)
            | Some (ll, _::tq'), TTICKET INC_NOW =>
                Some (TEVENT i (TTICKET REL_LOCK)::ll, tq')
            | Some (ll, tq), TSHARED _ => Some ((TEVENT i e) :: ll, tq)
            | _, _ => None
            end
        end.

      Inductive relate_ticket_log_option:
        MultiLog -> MultiLog -> Prop :=
      | RELATE_TICKET_LOG_POOL_SOME:
          forall hl ll tq (Hrelate_ticket_log: relate_log ll = Some (hl, tq)),
          relate_ticket_log_option (hl) (ll).

      Inductive relate_ticket_log_pool: MultiLogPool -> MultiLogPool -> Prop :=
      | RELATE_TICKET_LOG_POOL:
          forall hlp llp
          (Hrelate_ticket_log_option:
            forall lk, relate_ticket_log_option (ZMap.get lk hlp) (ZMap.get lk llp))
          , relate_ticket_log_pool hlp llp
      .

      Inductive relate_ticket_oracle: MultiOracle -> MultiOracle -> Prop :=
      | RELATE_ORACLE:
          forall ho lo
            (Hrelate_ticket_oracle_res:
              forall c hl ll tq bound (Hrelate_log: relate_log ll = Some (hl, tq)),
                let ll' := TEVENT c (TTICKET (INC_TICKET bound)) :: lo c ll ++ ll in
                forall self_c other_c b q tq' ll''
                    (HCal: Q_CalLock ll' = Some (self_c, other_c, b, q, tq'))
                    (HWait: Q_CalWait (CalWaitTime tq') c ll' lo = Some ll''),
                  exists tq', relate_log ll'' = Some (ho c hl ++ hl, tq')
            ),
            relate_ticket_oracle ho lo
      .

      Inductive relate_ticket_oracle_pool: MultiOraclePool -> MultiOraclePool -> Prop :=
      | RELATE_ORACLE_POOL:
          forall ho lo (Hrelate_ticket_oracle:
              forall lk, relate_ticket_oracle (ZMap.get lk ho) (ZMap.get lk lo)),
            relate_ticket_oracle_pool ho lo.

    End RelationHelpers.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
        icore_rel         : icore hadt = icore ladt;
        ihost_rel         : ihost hadt = ihost ladt;
        tstate_rel        : tstate hadt = tstate ladt;
        curid_rel         : curid hadt = curid ladt;
        cur_vmid_rel      : cur_vmid hadt = cur_vmid ladt;
        cur_vcpuid_rel    : cur_vcpuid hadt = cur_vcpuid ladt;
        regs_rel          : regs hadt = regs ladt;
        lock_rel          : lock hadt = lock ladt;
        region_cnt_rel    : region_cnt hadt = region_cnt ladt;
        regions_rel       : regions hadt = regions ladt;
        shadow_ctxts_rel  : shadow_ctxts hadt = shadow_ctxts ladt;
        smmu_conf_rel     : smmu_conf hadt = smmu_conf ladt;
        log_rel           : relate_ticket_log_pool (log hadt) (log ladt);
        oracle_rel        : relate_ticket_oracle_pool (oracle hadt) (oracle ladt);
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

    (** Prove that after taking one step, the refinement relation still holds*)
    (* TODO: what is this used for?? *)
    Lemma relate_incr:
      forall abd abd' f f',
        relate_RData f abd abd'
        -> inject_incr f f'
        -> relate_RData f' abd abd'.
    Proof.
      inversion 1; subst; intros; inv H; constructor; eauto.
      (* eapply tfs_inj_incr; eauto. *)
    Qed.

    Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
    Proof.
      constructor; intros; simpl; trivial.
      constructor; inv H; trivial.
    Qed.

    (* Ported from StarvationFreedomTicketLock *)
    Section StarvationFreedomLemmas.

      Lemma relate_log_shared:
        forall l1 l0 tq (Hre: relate_log l1 = Some (l0, tq)),
          GetSharedMemEvent l0 = GetSharedMemEvent l1.
      Proof.
        induction l1; simpl; intros.
        - inv Hre. trivial.
        - subdestruct; inv Hre; simpl; eauto.
      Qed.

      Lemma relate_ticket_log_pool_gss:
        forall l l' o o' p
               (Hrelate_log: relate_ticket_log_option l l')
               (Hrelate:relate_ticket_log_pool o o'),
          relate_ticket_log_pool (ZMap.set p l o) (ZMap.set p l' o').
      Proof.
        intros. constructor. intros.
        destruct (zeq p lk); subst.
        - repeat rewrite ZMap.gss. trivial.
        - inv Hrelate. repeat rewrite ZMap.gso; eauto.
      Qed.

      Lemma relate_ticket_log_shared:
        forall curid l l' tq e
               (Hlog: relate_log l = Some (l', tq)),
          relate_log (TEVENT curid (TSHARED e) :: l) =
          Some (TEVENT curid (TSHARED e) :: l', tq).
      Proof. intros. simpl. rewrite Hlog. now destruct tq. Qed.

      Lemma relate_ticket_log_pool_shared:
        forall curid p l l' t t' tq e
               (Hlog: relate_log l' = Some (l,tq))
               (Hlog_pool: relate_ticket_log_pool t t'),
          relate_ticket_log_pool
            (ZMap.set p ((TEVENT curid (TSHARED e) :: l)) t)
            (ZMap.set p ((TEVENT curid (TSHARED e) :: l')) t').
      Proof.
        intros. eapply relate_ticket_log_pool_gss; eauto.
        econstructor. eapply relate_ticket_log_shared; eauto.
      Qed.

      Section WITH_WAIT.

        Local Transparent Q_CalLock Q_CalWait.

        Lemma Q_CalLock_q_length_same:
          forall l self_c other_c b q tq
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
            length tq = length q.
        Proof.
          induction l; simpl; intros.
          { inv HCal. trivial. }
          repeat match type of HCal with
          | context [match ?con with _ => _ end] => destruct con; try discriminate
          | context [if ?con then _ else _]      => destruct con; try discriminate
          end;
          inv HCal; exploit IHl; eauto;
          intro Hre; try inversion Hre;
          repeat rewrite app_comm_cons;
          repeat rewrite app_length;
          rewrite Hre; simpl; trivial.
        Qed.

        Lemma list_head_case:
          forall {A: Type} q' q q0 (z z0: A)
                 (Heq: z :: q = q' ++ z0 :: q0),
            (z = z0 /\ q' = nil /\ q0 = q)
            \/ (exists q1, q' = z :: q1 /\ q = q1 ++ z0 :: q0).
        Proof.
          induction q'; simpl; intros.
          - inv Heq. left. eauto.
          - destruct q.
            + inv Heq.
              symmetry in H1. apply list_not_e_nil in H1. inv H1.
            + inv Heq. exploit IHq'; eauto.
        Qed.

        Lemma list_valid_In_append':
          forall a l P,
            (forall i0 e, In (TEVENT i0 e) (a :: l) -> P i0 e) ->
            (forall i0 e, In (TEVENT i0 e) l -> P i0 e).
        Proof.
          intros; eauto. eapply X.
          right. trivial.
        Qed.

        Lemma CalLock_length:
          forall l' l tq q self_c self_c' other_c other_c' b b' z bound q0 q1 q' tq0 tq''
                 (Hlen: length tq = length q)
                 (Hqlock: Q_CalLock l = Some (self_c, other_c, b, q ++ z :: q0, tq ++ bound :: tq0))
                 (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> z \/ (forall n, e <> TTICKET (INC_TICKET n)))
                 (Hqlock0: Q_CalLock (l' ++ l) = Some (self_c', other_c', b', q' ++ z :: q1, tq''))
                 (Hnin: ~ In z q)
                 (Hnin0: ~ In z q0),
          exists tq' tq1, tq'' = tq' ++ bound :: tq1 /\ length tq' = length q'.
        Proof.
          induction l'; simpl; intros.
          {
            rewrite Hqlock in Hqlock0. inv Hqlock0.
            refine_split'; trivial.
            eapply list_unique_element in H3; eauto.
            destruct H3 as (? & ?); subst. trivial.
          }
          assert (Hin_append: forall i0 e,
                        In (TEVENT i0 e) l' -> i0 <> z \/ (forall n, e <> TTICKET (INC_TICKET n))).
          { eapply list_valid_In_append'; eauto. }

          destruct a, (Q_CalLock (l' ++ l)) eqn:HQ_CalLock; try discriminate.
          subdestruct; inv Hqlock0;
          try (rewrite H3 in HQ_CalLock; exploit IHl'; eauto);
          try (
            match type of Hin with context [INC_TICKET ?nnn] => rename nnn into nn end
            ; destruct q'; inv H3;
                [ specialize (Hin z (TTICKET (INC_TICKET nn)))
                ; elim Hin
                  ; [ intros HF; now contradict HF
                    | intros HF; specialize (HF nn); now contradict HF
                    | now left]
                | symmetry in H1; eapply list_not_e_nil in H1; inv H1
                ]
            );
          try (
            rewrite app_comm_cons in H3
            ; eapply list_tail_one_element in H3
            ; destruct H3 as [(? & ?) | HF]; subst
            ; [ match type of Hin with context [INC_TICKET ?nnn] => rename nnn into nn end
                ; specialize (Hin z (TTICKET (INC_TICKET nn)))
                ; elim Hin
                ; [ intros HF; now contradict HF
                  | intros HF; specialize (HF nn); now contradict HF
                  | now left]
              | destruct HF as (l2' & Heq)
              ; rewrite Heq in HQ_CalLock
              ; rewrite app_comm_cons
              ; (exploit IHl'; eauto)
              ; intros (tq' & tq1 & -> & Hlen1)
              ; rewrite <- app_assoc
              ; rewrite <- app_comm_cons
              ; refine_split'; trivial
              ]
            )
          .
          - rewrite app_comm_cons in HQ_CalLock.
            exploit IHl'; try eassumption.
            intros (tq' & tq1 & Heq1 & Hlen1).
            destruct tq'.
            + inv Hlen1.
            + rewrite <- app_comm_cons in Heq1.
              inv Heq1. inv Hlen1.
              refine_split'; trivial.
          - match goal with H:context[in_dec] |- _ => clear H end;
            match goal with H:context[~ In ?z (?z::_)] |- _ => contradict H end;
            now left.
        Qed.

        Lemma Q_CalLock_relate_log_exists:
          forall l self_c other_c b q tq
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
          exists l', relate_log l = Some (l', tq).
        Proof.
          induction l; simpl; intros.
          - inv Hcal. refine_split'; trivial.
          - subdestruct; inv Hcal;
            (exploit IHl; eauto; intros (l' & ->);
             refine_split'; trivial).
        Qed.

        Lemma Q_CalLock_relate_log_eq:
          forall l l'  self_c other_c b q tq tq'
                 (Hre: relate_log l = Some (l', tq))
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq')),
            tq = tq'.
        Proof.
          intros.
          eapply Q_CalLock_relate_log_exists in Hcal.
          destruct Hcal as (l0 & Heq).
          rewrite Hre in Heq. inv Heq.
          trivial.
        Qed.

        Lemma Q_CalLock_GET_NOW_imply:
          forall curid l self_c other_c b q tq,
            Q_CalLock (TEVENT curid (TTICKET GET_NOW) :: l) = Some (self_c, other_c, b, curid :: q, tq) ->
            b = LGET.
        Proof.
          simpl; intros.
          subdestruct; inversion H; try subst; eauto; try congruence.
        Qed.

        Lemma CalWait_exists:
          forall wait_time curid l o l0
                 (Hwait: Q_CalWait wait_time curid l o = Some l0),
          exists self_c other_c q tq,
            Q_CalLock l0 = Some (self_c, other_c, LGET, curid :: q, tq).
        Proof.
          Local Opaque Q_CalLock.
          induction wait_time; simpl; intros; try (inv Hwait; fail).
          subdestruct; try inv Hwait; eauto.
          exploit Q_CalLock_GET_NOW_imply; eauto.
          intros; subst.
          refine_split'; eauto.
        Qed.

        Lemma CalWait_exists_log:
          forall wait_time curid l o l0
                 (Hwait: Q_CalWait wait_time curid l o = Some l0)
                 (Horacle_domain : valid_multi_oracle_domain o),
          exists l', l0 = l' ++ l
                     /\ (forall i0 e, In (TEVENT i0 e) l' -> i0 <> curid \/ (forall n, e <> TTICKET (INC_TICKET n))).
        Proof.
          Local Opaque Q_CalLock.
          induction wait_time; simpl; intros; try (inv Hwait; fail).
          subdestruct; try inv Hwait; eauto.
          - rewrite app_comm_cons.
            refine_split'; eauto. intros.
            inv H.
            + right. inv H0. intros. intro HF; inv HF.
            + left. eapply Horacle_domain in H0; eauto. eapply H0.
          - exploit IHwait_time; eauto.
            intros (l' & ? & Hp); subst.
            rewrite app_comm_cons.
            rewrite app_assoc.
            refine_split'; eauto.
            intros.
            eapply in_app_or in H.
            destruct H as [Hin | Hin]; auto.
            inv Hin.
            + right. inv H. intros. intro HF; inv HF.
            + eapply Horacle_domain in H; eauto.
              left. eapply H.
        Qed.

        Lemma relate_ticket_log_pool_REL:
          forall curid p l l0 l' t t' tq tq0
                 (Hlog: relate_log l' = Some (l, tq))
                 (Hlog': relate_log (TEVENT curid (TTICKET INC_NOW) :: l') = Some (l0, tq0))
                 (Hlog_pool: relate_ticket_log_pool t t'),
            relate_ticket_log_pool
              (ZMap.set p ((TEVENT curid (TTICKET REL_LOCK) :: l)) t)
              (ZMap.set p ((TEVENT curid (TTICKET INC_NOW) :: l')) t').
        Proof.
          intros. eapply relate_ticket_log_pool_gss; eauto.
          econstructor. simpl in *. rewrite Hlog in *.
          destruct tq; contra_inv. inv Hlog'. trivial.
        Qed.

        Local Transparent Q_CalLock.

        Lemma Q_CalLock_HOLD_LOCK_exists:
          forall wait_time c l o l0
                 (Hwait: Q_CalWait wait_time c l o = Some l0),
          exists x,
            Q_CalLock (TEVENT c (TTICKET HOLD_LOCK) :: l0) = Some x.
        Proof.
          simpl; intros.
          eapply CalWait_exists in Hwait.
          destruct Hwait as (self_c & other_c & q & tq & Hcal).
          rewrite Hcal.
          exploit Q_CalLock_q_length_same; eauto. intros.
          destruct tq; inv H.
          rewrite zeq_true. eauto.
        Qed.

        Lemma Q_CalLock_INC_TICKET_exists:
          forall l self_c other_c b q tq n c
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Hnin: ~ In c q)
                 (Hpos: other_c <> O),
          exists x,
            Q_CalLock (TEVENT c (TTICKET (INC_TICKET n)) :: l) = Some x.
        Proof.
          simpl; intros. rewrite HCal.
          exploit Q_CalLock_q_length_same; eauto. intros.
          destruct q.
          - destruct tq; inv H. eauto.
          - destruct tq; inv H.
            destruct (zeq c z); subst.
            + elim Hnin. left; trivial.
            + destruct other_c.
              * elim Hpos. trivial.
              * destruct (in_dec zeq c (z::q)); eauto; elim Hnin; eauto.
        Qed.

        Lemma Q_CalLock_oracle_not_In:
          forall l' l self_c other_c b q tq self_c' other_c' b' q' tq' c
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> c)
                 (Hnin: ~ In c q)
                 (HCal': Q_CalLock (l' ++ l) = Some (self_c', other_c', b', q', tq')),
            ~ In c q'.
        Proof.
          induction l'; simpl; intros.
          - rewrite HCal in HCal'. inv HCal'. trivial.
          - assert (Hin_append: forall i0 e, In (TEVENT i0 e) l' -> i0 <> c).
            { eapply list_valid_In_append; eauto. }
            subdestruct; inv HCal'; try (eapply (IHl' l); eauto; fail).
            + specialize (Hin c (TTICKET (INC_TICKET n1))).
              red; intros. simpl in H. destruct H as [HF|HF]; inv HF.
              elim Hin. left; trivial. trivial.
            + red; intro. exploit (IHl' l); eauto.
              right. trivial.
            + red; intro HF. exploit (IHl' l); eauto.
              rewrite app_comm_cons in HF.
              eapply in_app_or in HF.
              destruct HF as [HF' | HF']; trivial.
              destruct HF' as [HF|HF]; inv HF.
              specialize (Hin c (TTICKET (INC_TICKET n3))).
              elim Hin; trivial. left; trivial.
            + match goal with H:context[in_dec] |- _ => clear H end.
              match goal with H:context[~ In ?z (?z::_)] |- _ => contradict H end.
              now left.
            + red; intro HF. exploit (IHl' l); eauto.
              rewrite app_comm_cons in HF.
              eapply in_app_or in HF.
              destruct HF as [HF' | HF']; trivial.
              destruct HF' as [HF|HF]; inv HF.
              specialize (Hin c (TTICKET (INC_TICKET n4))).
              elim Hin; trivial. left; trivial.
        Qed.

        Lemma Q_CalLock_oracle:
          forall l self_c other_c b q tq c o
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Horacle_domain : valid_multi_oracle_domain o
                                   /\ valid_multi_oracle_queue o)
                 (Hin': forall i1 e1,
                          In (TEVENT i1 e1) l -> 0 <= i1 < 8)
                 (Hlast: match l with
                           | nil => True
                           | TEVENT c0 _ :: _ => c0 = c
                         end)
                 (Hnin: ~ In c q),
          exists self_c' other_c' b' q' tq',
            Q_CalLock (o c l ++ l) = Some (self_c', other_c', b', q', tq')
            /\ ~ In c q'
            /\ other_c' <> O.
        Proof.
          intros.
          destruct Horacle_domain as (Horacle_domain0 & Horacle_domain1).
          unfold valid_multi_oracle_queue in *.
          specialize (Horacle_domain1 c l).
          exploit Horacle_domain1; eauto.
          {
            unfold valid_qlock.
            rewrite HCal. refine_split'; trivial.
          }
          intros (self_c' & other_c' & b' & q' & tq' & HCal' & Hnhead).
          assert (HnotIn: ~ In c q').
          {
            eapply (Q_CalLock_oracle_not_In (o c l) l); eauto.
            intros. eapply Horacle_domain0; eauto.
          }
          refine_split'; eauto.
        Qed.

        Lemma Q_CalLock_INC_TICKET_exists':
          forall l self_c other_c b q tq n c o
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Horacle_domain : valid_multi_oracle_domain o
                                   /\ valid_multi_oracle_queue o)
                 (Hin': forall i1 e1,
                          In (TEVENT i1 e1) l -> 0 <= i1 < 8)
                 (Hlast: match l with
                           | nil => True
                           | TEVENT c0 _ :: _ => c0 = c
                         end)
                 (Hnin: ~ In c q),
          exists x,
            Q_CalLock (TEVENT c (TTICKET (INC_TICKET n)) :: (o c l ++ l)) = Some x.
        Proof.
          intros.
          exploit Q_CalLock_oracle; eauto.
          intros (self_c' & other_c' & b' & q' & tq' & HCal' & HnotIn & Hother).
          eapply Q_CalLock_INC_TICKET_exists; eauto.
        Qed.

        Lemma Q_CalLock_INC_NOW_exists:
          forall l self_c other_c q tq c q'
                 (HCal: Q_CalLock l = Some (self_c, other_c, LHOLD, q, tq))
                 (HinQ: q = c :: q'),
          exists x,
            Q_CalLock (TEVENT c (TTICKET (INC_NOW)) :: l) = Some x.
        Proof.
          simpl; intros. rewrite HCal. subst.
          exploit Q_CalLock_q_length_same; eauto. intros.
          destruct tq; inv H.
          rewrite zeq_true. eauto.
        Qed.

        Lemma O_gt_false: forall n (Hgt: (O > n)%nat), False.
        Proof. intros. destruct n; omega. Qed.

        Lemma add_mult_assoc: forall (a b c: nat), (a * c + b * c = (a + b) * c)%nat.
        Proof. induction a; [easy|simpl; intros; rewrite <-(IHa b c); xomega]. Qed.

        Lemma lt_plus_trans' n m p : (n < m -> n < p + m)%nat.
        Proof. erewrite (plus_comm p). eapply lt_plus_trans. Qed.

        Lemma le_plus_trans' n m p : (n <= m -> n <= p + m)%nat.
        Proof. erewrite (plus_comm p). eapply le_plus_trans. Qed.

        Lemma lt_less_plus n m p : (n < m -> p + n < p + m)%nat.
        Proof. omega. Qed.

        Lemma lt_plus_r n m : 0 < n -> m < n + m.
        Proof. omega. Qed.

        Lemma CalLock_progress:
          forall l' l tq q self_c self_c' other_c other_c' b b' z bound q0 tq0 lq ltq
                 (Hlen: length tq = length q)
                 (Hqlock: Q_CalLock l = Some (self_c, other_c, b, q ++ z :: q0, tq ++ bound :: tq0))
                 (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> z)
                 (Hnin: ~ In z q)
                 (HCal: Q_CalLock (l' ++ l) = Some (self_c', other_c', b', lq, ltq)),
          exists q' q'' q1 tq' tq'' tq1,
            lq = q'' ++ z :: q1
            /\ ltq = tq''++ bound :: tq1
            /\ q = q' ++ q''
            /\ tq = tq' ++ tq''
            /\ length tq'' = length q''
            /\ (decrease_number self_c' other_c' b' tq'' <=
                decrease_number self_c other_c b tq)%nat.
        Proof.
          Local Opaque fairness.
          induction l'; simpl; intros.
          {
            exists nil, q, q0, nil, tq, tq0.
            rewrite Hqlock in HCal. inv HCal. refine_split'; eauto.
          }
          assert (Hin_append:
              forall i0 e, In (TEVENT i0 e) l' -> i0 <> z \/ e = TTICKET GET_NOW).
            { eapply list_valid_In_append'; eauto. }
          destruct a.
          subdestruct; inv HCal; try (exploit IHl'; eauto);
          try ( match goal with H:context[in_dec] |- _ => clear H end;
                match goal with H:context[~ In ?z (?z::_)] |- _ => contradict H end;
                left; easy);

          intros (q' & q'' & qq1 & tq' & tq'' & tq1 & Hlq & Hltq & Hq & htq & Hlen' & Hdec);
          subst.
          + symmetry in Hlq.
            apply list_not_e_nil in Hlq. inv Hlq.
          + eapply list_head_case in Hlq.
            destruct Hlq as [(? & ? & ?)| (q2 & ? & ?)]; subst.
            {
              specialize (Hin z (TTICKET INC_NOW)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
            }
            eapply list_head_case in Hltq.
            destruct Hltq as [(? & ? & ?)| (tq2 & ? & ?)]; subst.
            { inv Hlen'. }
            exists (q' ++ z0 :: nil), q2, qq1, (tq' ++ n :: nil), tq2, tq1.
            refine_split'; eauto.
            * rewrite <- app_assoc.
              rewrite <- app_comm_cons. simpl. trivial.
            * rewrite <- app_assoc.
              rewrite <- app_comm_cons. simpl. trivial.
            * etransitivity; try eapply Hdec.
              simpl.
              etransitivity.
              instantiate (1:=((n0 + CalSumWait tq2 + 1) * fairness)%nat).
              etransitivity.
              instantiate (1:=((CalSumWait tq2 + 1) * fairness)%nat).
              repeat rewrite mult_plus_distr_r. omega.
              repeat rewrite <- add_mult_assoc.
              rewrite plus_assoc_reverse. xomega. xomega.
          + refine_split'; eauto.
            etransitivity; try eapply Hdec.
            simpl.
            eapply list_head_case in Hlq.
            destruct Hlq as [(? & ? & ?)| (q2 & ? & ?)]; subst.
            {
              specialize (Hin z (TTICKET GET_NOW)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
            }
            eapply list_head_case in Hltq.
            destruct Hltq as [(? & ? & ?)| (tq2 & ? & ?)]; subst.
            { inv Hlen'. }
            simpl. apply le_plus_trans'.
            repeat rewrite mult_plus_distr_r. omega.

          + refine_split'; eauto.
            etransitivity; try eapply Hdec.
            simpl.
            repeat rewrite mult_plus_distr_r. omega.
          + refine_split'; eauto.
            etransitivity; try eapply Hdec.
            simpl.
            repeat rewrite mult_plus_distr_r. omega.

          + refine_split'; eauto.
            etransitivity; try eapply Hdec.
            unfold decrease_number.
            destruct b'; omega.

          + subst.
            exists q', q'', (qq1 ++ cpuid::nil), tq', tq'', (tq1 ++ n4 :: nil).
            refine_split'; eauto.
            * repeat rewrite app_comm_cons.
              rewrite Hlq.
              rewrite <- app_assoc. trivial.
            * repeat rewrite app_comm_cons.
              rewrite Hltq.
              rewrite <- app_assoc. trivial.
            * etransitivity; try eapply Hdec.
              destruct b'; simpl; omega.
          + refine_split'; eauto.
            etransitivity; try eapply Hdec.
            unfold decrease_number.
            destruct b'; omega.
        Qed.

        Lemma CalLock_progress_GET_NOW:
          forall l tq q self_c self_c' other_c other_c' b b' c n tq'
                 (Hqlock: Q_CalLock l = Some (self_c, other_c, b, q, tq++n::tq'))
                 (HCal: Q_CalLock (TEVENT c (TTICKET GET_NOW):: l) =
                        Some (self_c', other_c', b', q, tq++n::tq'))
                 (Hneq: tq <> nil),
            (decrease_number self_c' other_c' b' tq <
             decrease_number self_c other_c b tq)%nat.
        Proof.
          simpl; intros. rewrite Hqlock in HCal.
          subdestruct; inv HCal; simpl.
          - symmetry in Hdestruct.
            eapply list_head_case in Hdestruct.
            destruct Hdestruct as [(? & ? & ?)| (tq2 & ? & ?)]; subst.
            { elim Hneq. trivial. }
            simpl.
            apply lt_plus_trans'.
            pose proof positive_fairness.
            repeat rewrite mult_plus_distr_r. omega.
          - destruct b'; simpl; omega.
        Qed.

        Local Transparent H_CalLock.

        Lemma Q_CalLock_nil:
          forall l self_c other_c b tq
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, nil, tq)),
            b = LEMPTY.
        Proof.
          induction l; simpl; intros.
          - inv Hcal. trivial.
          - subdestruct; inv Hcal; trivial.
        Qed.

        Lemma Q_CalLock_get:
          forall l self_c other_c q b head tq
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, head :: tq)),
            match b with
              | LGET => head = self_c
              | _ => True
            end.
        Proof.
          induction l; simpl; intros.
          - inv Hcal.
          - subdestruct; inv Hcal; trivial;
            destruct b; trivial; exploit IHl; eauto.
        Qed.

        Definition get_head_lock (l: list Z) (b: qhead_status):=
          match b with
            | LHOLD =>
              match l with
                | nil => None
                | a :: _ => Some a
              end
            | _ => None
          end.

        Lemma Q_CalLock_relate_log:
          forall l l' self_c self_c' other_c b b' q tq tq0 h
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Hcal': H_CalLock l' = Some (self_c', b', h))
                 (Hre: relate_log l = Some (l', tq0)),
            match b with
              | LGET => True
              | _ => self_c' = self_c
            end
            /\ match b with
                 | LHOLD => b' = LHOLD
                 | _ => b' = LEMPTY
               end
            /\ h = get_head_lock q b.
        Proof.
          induction l; simpl; intros.
          { inv Hcal. inv Hre. inv Hcal'. simpl; eauto. }
          destruct a. destruct (relate_log l) eqn: Hre'; contra_inv.
          destruct (Q_CalLock l) eqn: Hcal0'; contra_inv.
          subdestruct; inv Hcal; inv Hre; eauto;
          exploit Q_CalLock_relate_log_exists; eauto;
          try rewrite Hre'; intros (l'0 & Heq); inv Heq;
          try (progress simpl in Hcal'; subdestruct; inv Hcal');
          try (exploit IHl; now eauto);
          try (exploit IHl; eauto; simpl; intros (?&?&?); refine_split'; now eauto);
          try (exploit IHl; eauto; eapply Q_CalLock_nil in Hcal0'; eauto; now subst).
          rewrite H0 in Hre'; inv Hre'.
          apply Q_CalLock_get in Hcal0'; inv Hcal0'.
          auto.
        Qed.

        Lemma CalSumWait_append:
          forall l l', CalSumWait (l ++ l') = (CalSumWait l + CalSumWait l')% nat.
        Proof.
          induction l; simpl; intros; trivial.
          rewrite IHl. omega.
        Qed.

        Lemma Q_CalLock_other_c:
          forall l self_c other_c q b tq
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
            (other_c <= fairness)%nat.
        Proof.
          induction l; simpl; intros.
          - inv Hcal. trivial.
          - subdestruct; inv Hcal; trivial; exploit IHl; eauto; intros; try omega.
        Qed.

        Lemma Q_CalLock_self_c:
          forall l self_c other_c q b tq
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq)),
            match tq with
              | nil => self_c = O
              | a :: _ => (self_c <= a)%nat
            end.
        Proof.
          induction l; simpl; intros.
          - inv Hcal. trivial.
          - subdestruct; inv Hcal; trivial; exploit IHl; eauto; intros Hs;
            try ( match goal with H:context[in_dec] |- _ => clear H end;
                  match goal with H:context[~ In ?z (?z::_)] |- _ => contradict H end;
                  left; easy).
            + simpl in Hs. subst. omega.
            + destruct tq; omega.
            + simpl in Hs. omega.
        Qed.

        Lemma Q_CalLock_INC_TICKET_status:
          forall l self_c other_c q b tq self_c' other_c' q' b' tq' c n
                 (Hcal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Hcal': Q_CalLock (TEVENT c (TTICKET (INC_TICKET n)) :: l)  = Some (self_c', other_c', b', q', tq')),
            match q with
              | nil => b' = LEMPTY
              | _ => True
            end.
        Proof.
          simpl; intros. rewrite Hcal in Hcal'.
          subdestruct; inv Hcal'; trivial.
        Qed.

        Lemma CalLock_status:
          forall l' l tq q self_c self_c' other_c other_c' b b' z q0 lq ltq
                 (Hqlock: Q_CalLock l = Some (self_c, other_c, b, q ++ z :: q0, tq))
                 (Hin: forall i0 e, In (TEVENT i0 e) l' -> i0 <> z)
                 (Hnin: ~ In z q)
                 (Hq: match q with
                        | nil => b = LEMPTY
                        | _ => True
                      end)
                 (HCal: Q_CalLock (l' ++ l) = Some (self_c', other_c', b', z ::lq, ltq)),
            b' = LEMPTY.
        Proof.
          induction l'; simpl; intros.
          - rewrite Hqlock in HCal. inv HCal.
            destruct q.
            + elim Hq. trivial.
            + inv H3. elim Hnin. left; trivial.
          - assert (Hin_append:
                      forall i0 e,
                        In (TEVENT i0 e) l' -> i0 <> z).
            { eapply list_valid_In_append'; eauto. }
            subdestruct; inv HCal;
            try (exploit IHl'; eauto; simpl; trivial; intros; congruence);
            try ( match goal with H:context[in_dec] |- _ => clear H end;
                  match goal with H:context[~ In ?z (?z::_)] |- _ => contradict H end;
                  left; easy);
            trivial.
            + specialize (Hin z (TTICKET GET_NOW)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
            + specialize (Hin z (TTICKET HOLD_LOCK)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
            + specialize (Hin z (TTICKET GET_NOW)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
            + specialize (Hin z (TTICKET HOLD_LOCK)).
              elim Hin; try (intros HF; congruence); trivial.
              left; trivial.
        Qed.

        Lemma Q_CalLock_TSHARED_exists:
          forall l l' self_c self_c' other_c b b' q tq  e c h tq0
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q, tq))
                 (Hcal': H_CalLock (TEVENT c (TSHARED e) :: l') = Some (self_c', b', h))
                 (Hre: relate_log l = Some (l', tq0)),
          exists x,
            Q_CalLock (TEVENT c (TSHARED e) :: l) = Some x.
        Proof.
          simpl; intros. rewrite HCal. subst.
          subdestruct; inv Hcal'.
          exploit Q_CalLock_relate_log; eauto.
          intros (Hself & Hb & Hz).
          destruct b; inv Hb.
          exploit Q_CalLock_q_length_same; eauto.
          intros Hlen.
          destruct q; inv Hz.
          destruct tq; inv Hlen.
          rewrite negb_false_iff in Hdestruct2; destruct(zeq c z0); contra_inv.
          eauto.
        Qed.

        Lemma decrease_number_lt_Wait:
          forall self_c other_c b tq n
                 (Hother: (other_c <= fairness)%nat)
                 (Hself: match tq with
                           | nil => self_c = O
                           | a :: _ => (self_c <= a)%nat
                         end),
            (decrease_number self_c other_c b tq <
             S (fairness + CalSumWait (tq ++ n :: nil) * fairness)) %nat.
        Proof.
          unfold decrease_number; intros.
          rewrite CalSumWait_append.
          destruct b.
          - rewrite <- add_mult_assoc. xomega.
          - destruct tq; subst; simpl.
            + xomega.
            + simpl. repeat rewrite <- add_mult_assoc.
              eapply le_lt_n_Sm.
              rewrite (plus_comm fairness ((fairness + (n0 * fairness + CalSumWait tq * fairness + S (S (S (S (n + 0)))) * fairness)))%nat).
              eapply plus_le_compat; eauto.
              eapply le_plus_trans'.
              eapply le_plus_trans'.
              eapply le_plus_trans.
              eapply le_plus_trans'.
              eapply plus_le_compat; eauto.
              * eapply plus_le_compat_r.
                apply mult_le_compat_r. omega.
              * simpl. xomega.
          - destruct tq; subst; simpl.
            + xomega.
            + simpl. repeat rewrite <- add_mult_assoc.
              eapply le_lt_n_Sm.
              rewrite (plus_comm fairness ((fairness + (n0 * fairness + CalSumWait tq * fairness +  S (S (S (S (n + 0)))) * fairness)))%nat).
              eapply plus_le_compat; eauto.
              eapply le_plus_trans'.
              eapply le_plus_trans'.
              eapply le_plus_trans.
              eapply le_plus_trans'.
              eapply plus_le_compat; eauto.
              * eapply plus_le_compat_r.
                apply mult_le_compat_r. omega.
              * simpl. xomega.
        Qed.

        Lemma starvation_freedom:
          forall wait_time l self_c other_c b q tq n c o q' tq'
                 (HCal: Q_CalLock l = Some (self_c, other_c, b, q ++ c :: q', tq ++ n :: tq'))
                 (Hlen: length q = length tq)
                 (Hgt: (decrease_number self_c other_c b tq < wait_time)%nat)
                 (Horacle_domain : valid_multi_oracle_domain o
                                   /\ valid_multi_oracle_queue o)
                 (Hnin: ~ In c q)
                 (Hq: match q with
                        | nil => b = LEMPTY
                        | _ => True
                      end)
                 (Hin': forall i1 e1,
                          In (TEVENT i1 e1) l -> 0 <= i1 < 8)
                 (Hlast: match l with
                           | nil => True
                           | TEVENT c0 _ :: _ => c0 = c
                         end)
                 (Hc: 0 <= c < TOTAL_CPU),
          exists l', Q_CalWait wait_time c l o = Some l'.
        Proof.
          Local Opaque Q_CalLock.
          induction wait_time; simpl; intros.
          - eapply O_gt_false in Hgt. inv Hgt.
          - pose proof Horacle_domain as (Horacle_domain1 & Horacle_domain2).
            exploit (Horacle_domain2 c l); eauto.
            {
              unfold valid_qlock. refine_split'; eauto.
            }
            intros (self_c' & other_c' & b' & q0 & tq0 & HCal' & nothead).
            exploit (CalLock_progress (o c l)); eauto.
            {
              intros. eapply Horacle_domain; eauto.
            }

            intros (q'0 & q'' & q1 & tq'0 & tq'' & tq1 & ? &? & ? &? & Hlen1 & Hlt); subst.
            assert (HCal_Get:
                      exists self_c0 other_c0 b0,
                        Q_CalLock (TEVENT c (TTICKET GET_NOW) :: o c l ++ l)
                        = Some (self_c0, other_c0, b0, q'' ++ c :: q1, tq'' ++ n :: tq1)).
            {
              Local Transparent Q_CalLock.
              simpl. rewrite HCal'.
              destruct (q'' ++ c :: q1) eqn: Hlq.
              {
                apply list_not_e_nil in Hlq. inv Hlq.
              }
              destruct (tq'' ++ n :: tq1) eqn: Hltq.
              {
                apply list_not_e_nil in Hltq. inv Hltq.
              }
              symmetry in Hlq.
              eapply list_head_case in Hlq.
              destruct Hlq as [(? & ? & ?)| (q2 & ? & ?)]; subst.
              {
                rewrite zeq_true.
                assert (Hb': b' = LEMPTY).
                {
                  eapply CalLock_status; eauto.
                  intros. eapply Horacle_domain1; eauto.
                }
                subst.
                destruct other_c'.
                - elim nothead. trivial.
                - eauto.
              }
              {
                assert (Hneq: c <> z).
                {
                  intro HF; subst. elim Hnin.
                  eapply in_or_app. right.
                  simpl. left; trivial.
                }
                rewrite zeq_false; trivial.
                destruct other_c'.
                {
                  elim nothead; trivial.
                }
                refine_split'; trivial.
              }
            }
            destruct HCal_Get as (self_c0 & other_c0 & b0 &  HCal'').
            rewrite HCal''.
            destruct (q'' ++ c :: q1) eqn: Hlq.
            {
              apply list_not_e_nil in Hlq. inv Hlq.
            }
            destruct (zeq z c).
            { rewrite e; rewrite zeq_true. eauto. }
            rewrite <- Hlq in HCal''.
            exploit (IHwait_time (TEVENT c (TTICKET GET_NOW) :: o c l ++ l)); eauto.
            + rewrite Hlq  in HCal''.
              exploit (CalLock_progress_GET_NOW (o c l ++ l)); eauto.
              {
                destruct tq''.
                - destruct q''; inv Hlen1. inv Hlq. elim n0; trivial.
                - intro HF; inv HF.
              }
              intros Hlt'.
              xomega.
            + intro HF. elim Hnin.
              eapply in_or_app. right; trivial.
            + destruct q''.
              * inv Hlq. elim n0; trivial.
              * trivial.
            + intros. inv H.
              * inv H0. eauto.
              * destruct Horacle_domain as (Hd & _).
                unfold valid_multi_oracle_domain in *.
                apply in_app_iff in H0. inv H0; eauto.
                eapply Horacle_domain1; eauto.
            + rewrite zeq_false; eauto.
        Qed.

      End WITH_WAIT.

    End StarvationFreedomLemmas.

    Section FreshPrim.

      Lemma pass_hlock_spec_exists:
        forall habd habd' labd lk f
              (Hhigh: LockOpsQ.Layer.high_level_invariant labd)
               (Hspec: pass_hlock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', pass_hlock_spec0 lk labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold pass_hlock_spec, pass_hlock_spec0, Spec.pass_qlock_spec.
        intros. inversion Hrel.
        remember  (lk @ (log habd)) as m;
        destruct (lk @ (lock habd)) eqn:Hdestruct3
        ; try discriminate.
        destruct  b
                , (CalLock.H_CalLock (TEVENT (curid habd) (TTICKET REL_LOCK)::m))
        ; try discriminate.
        inv Hspec.

        inversion log_rel0; subst.
        pose proof Hrelate_ticket_log_option.
        specialize (Hrelate_ticket_log_option lk).
        inv Hrelate_ticket_log_option.
        remember  (lk @ (log labd)) as ll;
        assert (He: exists x, Q_CalLock (TEVENT labd.(curid) (TTICKET INC_NOW) :: ll) = Some x).
        {
          exploit valid_qlock_pool_inv; eauto.
          instantiate (1:=lk).
          unfold valid_qlock.
          intros (self_c & other_c & b & q & tq0 & Hcal).
          exploit valid_qlock_pool_status_inv; eauto.
          replace (lock labd) with (lock habd) by (symmetry; assumption).
          erewrite Hdestruct3.
          intros (_ & HP). specialize (HP _ eq_refl).
          destruct HP as (q' & HP & Hhold & Hnin); subst.
          eapply Q_CalLock_INC_NOW_exists; eauto.
        }
        destruct He as (x & Hcal).
        rewrite Hcal.
        pose proof Hdestruct3 as Hlock_perm.
        replace (lock habd) with (lock labd) in Hlock_perm by assumption.
        rewrite Hlock_perm.
        refine_split'; simpl; trivial.
        replace (lock habd) with (lock labd) by assumption.
        constructor; simpl; trivial.
        destruct x as ((((self_c, other_c), b), q), tq0).
        eapply Q_CalLock_relate_log_exists in Hcal.
        destruct Hcal as (l' & Hcal).
        replace (curid habd) with (curid labd) by assumption.
        eapply relate_ticket_log_pool_REL; eauto.
      Qed.

      Lemma wait_hlock_spec_exists:
        forall habd habd' labd lk f
               (Hhigh: LockOpsQ.Layer.high_level_invariant labd)
               (Hspec: wait_hlock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', wait_hlock_spec0 lk labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold wait_hlock_spec, wait_hlock_spec0, Spec.wait_qlock_spec.
          Local Opaque Z.to_nat lock_bound fairness.
          intros. subdestruct; inv Hspec.

          inv Hrel. inv log_rel0.
          pose proof Hrelate_ticket_log_option.
          specialize (Hrelate_ticket_log_option lk).
          inv Hrelate_ticket_log_option.
          replace (lock labd) with (lock habd) by assumption.
          replace (lk @ (lock habd)) with LockFalse by assumption.
          remember (lk @ (log labd)) as ll in *.
          assert (He: exists x,
                        Q_CalLock (TEVENT (curid labd)
                                  (TTICKET (INC_TICKET (Z.to_nat lock_bound)))
                                  :: ZMap.get lk (oracle labd)
                                  (curid labd) ll ++ ll) = Some x).
          {
            exploit valid_qlock_pool_inv; eauto.
            instantiate(1:=lk).
            unfold valid_qlock.
            intros (self_c & other_c & b & q & tq0 & Hcal).
            eapply Q_CalLock_INC_TICKET_exists'; eauto.
            - rewrite Heqll. eauto.
            - eapply valid_multi_oracle_pool_inv; eauto.
            - eapply valid_last_pool_inv; eauto.
            - eapply valid_last_pool_inv; eauto.
            - exploit valid_qlock_pool_status_inv; eauto.
              replace (lock labd) with (lock habd) by (symmetry; assumption).
              rewrite Hdestruct.
              intros (HP &_). eapply HP. trivial.
          }
          destruct He as (x & HCal).
          destruct x as ((((self_c, other_c), b), q), tq0).
          pose proof HCal as HCalSimp; simpl in HCalSimp; rewrite HCalSimp;
          clear HCalSimp.
          assert (Heq: exists q' tq0',
                         q = q' ++ (curid labd) :: nil
                         /\ tq0 = tq0' ++ ((Z.to_nat lock_bound)) :: nil
                         /\ ~ In (curid labd) q'
                         /\ exists lother_c lb,
                              Q_CalLock (ZMap.get lk (oracle labd) (curid labd) ll ++ ll)
                              = Some (self_c, lother_c, lb, q', tq0')).
          {
            Local Transparent Q_CalLock.
            simpl in HCal.
            subdestruct; inv HCal.
            - exists nil, nil.
              refine_split'; trivial.
              simpl. intros HF; inv HF.
            - exists (z :: l2), (n0 :: l0).
              refine_split'; trivial.
              intros HF. inv HF.
              + now elim n1. (* n1: curid labbd <> curid labd *)
              + now elim n2. (* n2: ~In (curid labd) l2; H0: In (curid labd) l2 *)
            Local Opaque Q_CalLock.
          }
          destruct Heq as (q' & tq0' & ? & ? & Hnotin & Hlcal); subst.
          remember (lk @ (log labd)) as ll in *.
          assert (He: exists l',
                        Q_CalWait (CalWaitTime (tq0' ++ Z.to_nat lock_bound :: nil)) (curid labd)
                                  (TEVENT (curid labd)
                                          (TTICKET (INC_TICKET (Z.to_nat lock_bound)))
                                          :: ZMap.get lk (oracle labd)
                                          (curid labd) ll ++ ll)
                                  (ZMap.get lk (oracle labd)) = Some l').
          {
            eapply starvation_freedom; eauto.
            - eapply Q_CalLock_q_length_same in HCal.
              repeat rewrite app_length in HCal. simpl in HCal. xomega.
            - unfold CalWaitTime.
              eapply decrease_number_lt_Wait; eauto.
              + eapply Q_CalLock_other_c; eauto.
              + destruct Hlcal as (lother_c & lb & Hlcal).
                eapply Q_CalLock_self_c; eauto.
            - eapply valid_multi_oracle_pool_inv; eauto.
            - destruct Hlcal as (lother_c & lb & Hlcal).
              eapply Q_CalLock_INC_TICKET_status; eauto.
            - intros. inv H0.
              + inv H1. eapply CPU_ID_range; eauto.
              + eapply in_app_or in H1. inv H1.
                * eapply valid_multi_oracle_pool_inv; eauto.
                * eapply valid_last_pool_inv; eauto.
            - eapply CPU_ID_range; eauto.
          }
          destruct He as (l' & HWait).
          Transparent Q_CalLock.
          pose proof HWait as HWaitSimp; simpl in HWaitSimp;
          rewrite HWaitSimp; clear HWaitSimp.
          Opaque Q_CalLock.
          inv oracle_rel0.
          pose proof Hrelate_ticket_oracle.
          specialize (Hrelate_ticket_oracle lk).
          pose proof Hrelate_ticket_oracle as Hrelate_ticket_oracle'.
          inv Hrelate_ticket_oracle.
          Opaque Q_CalWait.
          simpl in Hrelate_ticket_oracle_res.
          specialize (Hrelate_ticket_oracle_res (curid labd) _ _ _ _
                        Hrelate_ticket_log _ _ _ _ _ l' HCal HWait).
          destruct Hrelate_ticket_oracle_res as (tq' & Hrelate).
          assert (He: exists tq0', tq' = (Z.to_nat lock_bound) :: tq0').
          {
            exploit Q_CalLock_q_length_same; eauto. intros Hlen.
            repeat rewrite app_length in Hlen. simpl in Hlen.
            exploit CalWait_exists; eauto.
            intros (self_c0 & other_c0 & q & tq0 & HCal1).
            exploit Q_CalLock_relate_log_eq; eauto. intro; subst.
            exploit CalWait_exists_log; eauto.
            {  eapply valid_multi_oracle_pool_inv; eauto. }
            intros (l'0 & ? & Hp); subst.
            rewrite <- (app_nil_l ((curid labd) :: q)) in HCal1.
            exploit CalLock_length; try eapply HCal; eauto.
            { omega. }
            intros (tq' & tq1 & Heq & Hlen1); subst.
            destruct tq'.
            - refine_split'; simpl; trivial.
            - inv Hlen1.
          }
          destruct He as (tq0'' & He); subst.
          assert (Hhold:
                    exists x, Q_CalLock (TEVENT (curid labd) (TTICKET HOLD_LOCK) :: l') = Some x).
          { eapply Q_CalLock_HOLD_LOCK_exists; eauto. }
          Transparent Q_CalLock.
          simpl Q_CalLock in Hhold.
          Opaque Q_CalLock.
          destruct Hhold as (x & ->).
          refine_split'; trivial.
          replace (curid habd) with (curid labd) by assumption.
          constructor; simpl; try eassumption; eauto.
          - eapply relate_ticket_log_pool_gss; econstructor; eauto.
            simpl. rewrite Hrelate. reflexivity.
          - econstructor; trivial.
        Qed.

    End FreshPrim.

  End WITHMEM.

End LockOpsHProofHigh.
```
