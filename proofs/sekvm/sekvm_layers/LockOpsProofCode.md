# LockOpsProofCode

```coq
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import MemoryX.
Require Import Events.
Require Import EventsX.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import Locations.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import LoopProof.
Require Import VCGen.
Require Import Errors.
Require Import Op.
Require Import Smallstep.
Require Import AuxLemma.
Require Import AuxStateDataType.
Require Import GenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import Conventions.
Require Import Clight.
Require Import CDataTypes.
Require Import CLemmas.
Require Import NArith.
Require Import XOmega.
Require Import ZArith.
Require Import NPeano.
Require Import NArith.
Require Import TacticsForTesting.
Require Import CommonTactic.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import Ctypes.

Require Import RData.
Require Import CalLock.
Require Import LockOps.Code.
Require Import Constants.
Require Import Ident.
Require Import AbstractMachine.Spec.
Require Import HypsecCommLib.
Require Import LockOps.Spec.
Require Import AbstractMachine.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsProofLow.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Section wait_lock_proof.

    Let L : compatlayer (cdata RData) :=
      incr_ticket ↦ gensem incr_ticket_spec ⊕
      get_now     ↦ gensem get_now_spec     ⊕
      barrier     ↦ gensem barrier_spec     ⊕
      log_hold    ↦ gensem log_hold_spec.

    Local Instance: ExternalCallsOps mem :=
      CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem :=
      CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_incr_ticket: block.
      Hypothesis h_incr_ticket_s : Genv.find_symbol ge incr_ticket = Some b_incr_ticket.
      Hypothesis h_incr_ticket_p : Genv.find_funct_ptr ge b_incr_ticket =
        Some (External (EF_external incr_ticket (signature_of_type
          (Tcons tuint (Tcons tuint Tnil)) tuint cc_default))
          (Tcons tuint (Tcons tuint Tnil)) tuint cc_default).

      Variable b_get_now: block.
      Hypothesis h_get_now_s : Genv.find_symbol ge get_now = Some b_get_now.
      Hypothesis h_get_now_p : Genv.find_funct_ptr ge b_get_now =
        Some (External (EF_external get_now (signature_of_type
          (Tcons tuint Tnil) tuint cc_default))
          (Tcons tuint Tnil) tuint cc_default).

      Variable b_log_hold: block.
      Hypothesis h_log_hold_s : Genv.find_symbol ge log_hold = Some b_log_hold.
      Hypothesis h_log_hold_p : Genv.find_funct_ptr ge b_log_hold =
        Some (External (EF_external log_hold (signature_of_type
        (Tcons tuint Tnil) tvoid cc_default))
        (Tcons tuint Tnil) tvoid cc_default).

      Variable b_barrier: block.
      Hypothesis h_barrier_s : Genv.find_symbol ge barrier = Some b_barrier.
      Hypothesis h_barrier_p : Genv.find_funct_ptr ge b_barrier =
        Some (External (EF_external barrier (signature_of_type
        Tnil tvoid cc_default))
        Tnil tvoid cc_default).

      Section WaitIter.
        Lemma IntUnsignedRange:
          forall i, 0 <= Int.unsigned i <= Int.max_unsigned.
        Proof.
          intros.
          generalize (Int.unsigned_range i).
          generalize max_unsigned_val; intro muval.
          unfold Int.modulus, two_power_nat, shift_nat; simpl.
          intro.
          omega.
        Qed.

        (* Lemma halt_remain: *)
        (*   forall d l, d.(shared).(halt) = (d {log: l}).(shared).(halt). *)
        (* Proof. intros; simpl; auto. Qed. *)

        Lemma multi_log_double_update:
          forall d ml1 ml2, d {log: ml1} {log: ml2} = d {log: ml2}.
        Proof.
          reflexivity.
        Qed.

        Fixpoint CalWaitIter (i: nat) (c t: Z)
                             (l: MultiLog) (to: MultiOracle):
                             option MultiLog :=
          match i with
          | O    => Some l
          | S i' => let l' := TEVENT c (TTICKET GET_NOW) :: to c l ++ l in
                    match CalTicketLockWraparound l' with
                    | Some (_, n, _) => if zeq t n then Some l' else
                                        CalWaitIter i' c t l' to
                    | _ => None
                    end
          end.

        Lemma CalTicketLockWraparoundRange:
          forall l l' t n,
          CalTicketLockWraparound l = Some (t, n, l') ->
          0 <= t <= Int.max_unsigned /\ 0 <= n <= Int.max_unsigned.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          destruct l.
          simpl in H.
          inv H.
          split; omega.
          simpl in H;
          subdestruct; inv H; simpl in *;
          split; eapply IntUnsignedRange.
        Qed.

        Lemma CalTicketWaitWraparoundStops:
          forall m i t l to l',
          CalTicketWaitWraparound m i t l to = Some l' ->
          exists k,
          (k <= m)%nat /\
          (forall n, (0 <= n < k)%nat -> CalTicketWaitWraparound n i t l to = None) /\
          CalTicketWaitWraparound k i t l to = Some l' /\
          forall j, (k <= j)%nat -> CalWaitIter j i t l to = Some l'.
        Proof.
          induction m; simpl; intros; [inv H |].
          subdestruct.
          - subst.
            inv H.
            exists 1%nat.
            split; [apply Arith.Le.le_n_S, Nat.le_0_l|].
            split; intros.
            + replace n with O by
              ( destruct H as [[] contra]
              ; [reflexivity
                | inversion contra as [|? contra']; inversion contra'
                ]
              ).
              reflexivity.
            + simpl.
              rewrite Hdestruct.
              rewrite Hdestruct2.
              split.
              * reflexivity.
              * intros.
                assert (j <> O) by omega.
                eapply NPeano.Nat.succ_pred in H0.
                rewrite <- H0.
                simpl.
                rewrite Hdestruct.
                rewrite Hdestruct2.
                reflexivity.
          - eapply IHm in H; eauto.
            destruct H.
            destruct H.
            destruct H0.
            destruct H1.
            exists (S x).
            split; [now apply Arith.Le.le_n_S|].
            split.
            + intros ? Hlelt.
              destruct Hlelt.
              assert(n0case: n0 = O \/ n0 <> O) by omega.
              Caseeq n0case; intros.
              subst.
              reflexivity.
              eapply NPeano.Nat.succ_pred in H5.
              rewrite <- H5.
              simpl.
              rewrite Hdestruct.
              rewrite Hdestruct2.
              eapply H0; eauto.
              split
              ; [ replace O with (pred O) by reflexivity
                ; now apply Arith.Le.le_pred
                |]
              .
              omega.
            + simpl.
              rewrite Hdestruct.
              rewrite Hdestruct2.
              split.
              apply H1.
              intros.
              assert (j <> O) by omega.
              eapply NPeano.Nat.succ_pred in H4.
              rewrite <- H4.
              simpl.
              rewrite Hdestruct.
              rewrite Hdestruct2.
              eapply H2; eauto.
              omega.
        Qed.

        Lemma CalTicketWaitWraparoundToIter:
          forall m i t l to l',
            CalTicketWaitWraparound m i t l to = Some l' ->
            CalWaitIter m i t l to = Some l'.
        Proof.
          induction m; simpl; intros; [inv H |].
          simpl.
          intros.
          subdestruct.
          apply H.
          eapply IHm; eauto.
        Qed.

        Lemma CalTicketWaitWraparoundToIterCons:
          forall m m' i t l to l',
            CalWaitIter m i t l to = Some l' ->
            (m' <= m)%nat ->
            exists l'', CalWaitIter m' i t l to = Some l''.
        Proof.
          induction m.
          - simpl.
            intros.
            assert(m' = O) by omega.
            subst.
            esplit.
            reflexivity.
          - simpl.
            intros.
            subdestruct.
            + inv H.
              assert(m' = O \/ m' <> O) by omega.
              Caseeq H; intros.
              subst.
              simpl.
              esplit; reflexivity.
              eapply NPeano.Nat.succ_pred in H.
              rewrite <- H.
              simpl.
              rewrite Hdestruct, Hdestruct2.
              esplit.
              reflexivity.
            + assert(m' = O \/ m' <> O) by omega.
              Caseeq H1; intros.
              subst.
              simpl.
              esplit; reflexivity.
              eapply NPeano.Nat.succ_pred in H1.
              rewrite <- H1.
              simpl.
              rewrite Hdestruct, Hdestruct2.
              eapply IHm; eauto.
              omega.
        Qed.

        Lemma CalWaitIterInv:
          forall m i t l to l',
          CalWaitIter (S m) i t l to = Some l' ->
          (forall j, (j < S m)%nat -> CalTicketWaitWraparound j i t l to = None) ->
          exists l'', CalWaitIter m i t l to   = Some l'' /\
                      CalWaitIter 1 i t l'' to = Some l'.
        Proof.
          induction m; simpl; intros.
          -  subdestruct.
             + inv H; esplit; split; [reflexivity | ].
               rewrite Hdestruct.
               rewrite Hdestruct2.
               reflexivity.
             + inv H; esplit; split; [reflexivity | ].
               rewrite Hdestruct.
               rewrite Hdestruct2.
               reflexivity.
          - simpl in *.
            intros; subdestruct.
            { inv H.
              assert ((1 < S (S m))%nat) by omega.
              eapply H0 in H.
              simpl in H.
              rewrite Hdestruct in H.
              rewrite Hdestruct2 in H.
              inv H. }
            { inv H.
              eapply IHm.
              - rewrite Hdestruct3.
                rewrite Hdestruct6.
                reflexivity.
              - intros.
                assert ((S j < S (S m))%nat) by omega.
                eapply H0 in H1.
                simpl in H1.
                rewrite Hdestruct in H1.
                rewrite Hdestruct2 in H1.
                apply H1. }
            { eapply IHm.
              - rewrite Hdestruct3.
                rewrite Hdestruct6.
                apply H.
              - intros.
                assert ((S j < S (S m))%nat) by omega.
                eapply H0 in H2.
                simpl in H2.
                rewrite Hdestruct in H2.
                rewrite Hdestruct2 in H2.
                apply H2. }
        Qed.

        Lemma CalWaitIterNeq:
          forall m i ticket l l' to t n tl,
          CalTicketWaitWraparound m i ticket l to = None ->
          CalWaitIter m i ticket l to = Some l' ->
          (m > 0)%nat ->
          CalTicketLockWraparound l' = Some (t, n, tl) ->
          n <> ticket.
        Proof.
          induction m; simpl; intros; try omega.
          subdestruct; subst.
          assert (mcase: m = O \/ (m > O)%nat) by omega.
          Caseeq mcase; intros; subst.
          - simpl in *.
            inv H0. 
            simpl in H2. 
            rewrite Hdestruct in H2.
            inv H2.
            intros contra; elim n0; symmetry; auto.
          - eapply IHm; eauto.
        Qed.

        Lemma CalTicketWaitWraparoundEq:
          forall m i t l to l' t' n' tl,
          CalTicketWaitWraparound m i t l to = Some l' ->
          CalTicketLockWraparound l' = Some (t', n', tl) ->
          n' = t.
        Proof.
          induction m; simpl; intros; [inv H | ].
          subdestruct; subst.
          - inv H.
            simpl in H0.
            rewrite Hdestruct in H0.
            inv H0.
            auto.
          - eapply IHm; eauto.
        Qed.

      End WaitIter.

      Section LoopProof.

        Variable minit: memb.
        Variable adt: RData.

        Variable my_ticket : Z.
        Variable init_now : Z.
        Variable prev_ticket : Z.
        Variable prev_now : Z.
        Variable bound : int.
        Variable cal_time: nat.

        Variable tq_init: list nat.
        Variable tq_prev: list nat.

        Variable lock_id : int.
        (* Variable offset : int. *)
        Variable lock_index : Z.

        Variable l : MultiLog.
        Variable K: nat.
        Variable l1: MultiLog.

        Local Notation Query l :=
          (ZMap.get lock_index adt.(oracle) adt.(curid) l)%list
          (only parsing).

        Local Notation nbound :=
          (Z.to_nat (Int.unsigned bound))
          (only parsing).

        Local Notation LogToIncrT l0 := (
          let l1 := (Query l0) ++ l0 in
          let l2 := TEVENT adt.(curid) (TTICKET (INC_TICKET nbound)) :: l1 in
          l2
        ) (only parsing).

        Local Notation LogToLoop l0 := (
          let l2 := LogToIncrT l0 in
          let l3 := Query l2 ++ l2 in
          let l4 := TEVENT adt.(curid) (TTICKET GET_NOW) :: l3 in
          l4
        ) (only parsing).

        Hypothesis init_neq: my_ticket <> prev_now.

        Hypothesis id2z: Int.unsigned lock_id = lock_index.
        (* Hypothesis index2zp: index2Z (Int.unsigned lock_id) (Int.unsigned offset) = Some lock_index. *)
        Hypothesis initlist: ZMap.get lock_index adt.(log) = l.

        Hypothesis initlock: 
          CalTicketLockWraparound
                  (ZMap.get lock_index adt.(oracle) adt.(curid) l ++ l) =
          Some (my_ticket, init_now, tq_init).

        Hypothesis lock_after_inc:
          CalTicketLockWraparound (Query (LogToIncrT l) ++ LogToIncrT l) =
          Some (prev_ticket, prev_now, tq_prev).

        Hypothesis Krange: (0 < K < cal_time)%nat.

        Hypothesis calcWait:
          CalTicketWaitWraparound (pred cal_time) adt.(curid) my_ticket
              (LogToLoop l) (ZMap.get lock_index adt.(oracle)) =
          Some l1.

        Hypothesis KPre: forall n, (0 <= n < K)%nat ->
          CalTicketWaitWraparound n adt.(curid) my_ticket
            (LogToLoop l) (ZMap.get lock_index adt.(oracle)) =
          None.

        Hypothesis KPost:
          CalTicketWaitWraparound K adt.(curid) my_ticket
            (LogToLoop l) (ZMap.get lock_index adt.(oracle)) =
          Some l1.

        Hypothesis  KPostPre: forall j, (K <= j)%nat ->
          CalWaitIter j adt.(curid) my_ticket
            (LogToLoop l) (ZMap.get lock_index adt.(oracle)) =
          Some l1.

        (* Hypothesis iihalt: adt.(shared).(halt) = false. *)
        (* Hypothesis iihost: adt.(ihost) = true. *)
        (* Hypothesis iikern: adt.(ikern) = true. *)
        Hypothesis my_ticket_range: 0 <= my_ticket <= Int.max_unsigned.
        Hypothesis prev_now_range:  0 <= prev_now  <= Int.max_unsigned.


        Definition calculate_wait_lock (i: nat) :=
          match CalWaitIter i adt.(curid) my_ticket (LogToLoop l)
                            (ZMap.get lock_index adt.(oracle)) with
          | Some l' => Some adt {log: ZMap.set lock_index (l') adt.(log)}
          | _ => None
          end.

        Definition get_cur_ticket (d: RData) := 
          match ZMap.get lock_index d.(log) with 
          | l' =>  match CalTicketLockWraparound l' with
                        | Some (_, n, _) => Some n
                        | _ => None
                        end
          end.

        Definition wait_lock_loop_body_P (le: temp_env) (m : mem): Prop :=
          le ! _cur_ticket = Some (Vint (Int.repr prev_now)) /\
          le ! _my_ticket = Some (Vint (Int.repr (my_ticket))) /\
          le ! _lk = Some (Vint lock_id) /\
          m = (minit,
               adt {log: ZMap.set lock_index ((LogToLoop l)) adt.(log)}) /\
          bars adt = BarrierValid.

        Definition wait_lock_loop_body_Q (le: temp_env) (m : mem): Prop :=
          exists d,
          le ! _cur_ticket = Some (Vint (Int.repr my_ticket)) /\
          le ! _my_ticket = Some (Vint (Int.repr (my_ticket))) /\
          le ! _lk = Some (Vint lock_id) /\
          calculate_wait_lock (pred cal_time) = Some d /\
          m = (minit, d) /\
          bars d = BarrierValid.

        Local Transparent CalTicketLockWraparound CalTicketWaitWraparound
                          CalWaitIter.

        Set Printing Projections.
        Lemma wait_lock_loop_correct_aux:
          LoopProofSimpleWhile.t wait_lock_loop_condition
                                 wait_lock_loop_body
                                 ge (PTree.empty _)
                                 wait_lock_loop_body_P
                                 wait_lock_loop_body_Q.
        Proof.
          pose proof max_unsigned_val as muval.
          apply LoopProofSimpleWhile.make with
            (W  := Z)
            (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
            (I  := fun le m w =>
                      exists i (* iteration *) new_now d',
                      (* local environment *)
                      le ! _cur_ticket = Some (Vint (Int.repr new_now)) /\
                      le ! _my_ticket = Some (Vint (Int.repr (my_ticket))) /\
                      le ! _lk = Some (Vint lock_id) /\

                      ( (* before while loop *)
                        ( i = O /\ new_now <> my_ticket /\
                          d' = adt {log : ZMap.set lock_index
                                          ((LogToLoop l)) adt.(log) }
                        )
                        \/
                        ( ( (* during while loop *)
                            (0 < i < K)%nat /\ new_now <> my_ticket
                          \/
                              (* end of while loop *)
                              i = K  /\ new_now = my_ticket
                            )
                            /\
                            (* calculate d' depending on num of iterations *)
                            calculate_wait_lock i = Some d'
                        )
                      ) /\

                      (* new_now <- d' *)
                      get_cur_ticket d' = Some new_now /\

                      (* i is increasing, so we flip it to obtain variant *)
                      w = Z.of_nat K - Z.of_nat i /\

                      (* something to do with memory? we don't care *)
                      m = (minit, d') /\
                      bars d' = BarrierValid
          ).
        { (* relation is well-founded *)
          apply Zwf_well_founded.
        }
        { (* invariant holds before loop *)
          intros le m (? & ? & ? & ?).
          exists (Z.of_nat K), O, prev_now.
          esplit.
          repeat vcgen.
          - unfold get_cur_ticket; simpl.
            rewrite ZMap.gss; simpl.
            simpl in lock_after_inc; rewrite lock_after_inc.
            rewrite Int.unsigned_repr by omega.
            reflexivity.
          - simpl; omega.
        }
        { (* invariant holds during loop *)
          unfold wait_lock_loop_condition, wait_lock_loop_body.
          intros le m w Hi.
          destruct Hi as (i & new_ticket & newd
                            & Hle1 & Hle2 & Hle3
                            & Hicond & Hcur & Hw & Hm & Hbar).
          Caseeq Hicond.
          { (* i = 0 *)
            intros (ival & new & nd); rewrite nd in *.
            unfold get_cur_ticket in Hcur; simpl in Hcur.
            rewrite ZMap.gss in Hcur.
            subdestruct.
            inversion Hcur.

            assert (tmp: exists tmp_ticket  tmp_now  tmp_post,
                          CalTicketLockWraparound
                            (Query (LogToLoop l) ++ LogToLoop l) =
                          Some (tmp_ticket, tmp_now, tmp_post)).
            {
              assert(Kneq0: K <> O) by omega.
              apply NPeano.Nat.succ_pred in Kneq0.
              rewrite <- Kneq0 in KPost.
              simpl in KPost.
              subdestruct; exists z1, z2, l2; reflexivity.
            }
            destruct tmp as [tmp_ticket [tmp_now [tmp_post tmp_cal]]].
            assert (0 <= new_ticket <= Int.max_unsigned).
            {
              eapply CalTicketLockWraparoundRange in Hdestruct.
              inversion_clear Hcur in Hdestruct.
              destruct Hdestruct; assumption.
            }
            assert (0 <= tmp_now <= Int.max_unsigned).
            {
              eapply CalTicketLockWraparoundRange in tmp_cal.
              destruct tmp_cal; assumption.
            }

            esplit; esplit.
            repeat vcgen.
            esplit; esplit.
            repeat vcgen.
            { unfold get_now_spec; simpl.
              (* rewrite iihalt. *)
              rewrite id2z.
              rewrite ZMap.gss.
              rewrite ZMap.set2.
              simpl in tmp_cal; rewrite tmp_cal.
              instantiate (1:= (Int.repr tmp_now)).
              rewrite Int.unsigned_repr by assumption.
              simpl in Hbar. rewrite Hbar.
              reflexivity.
            }
            { (* invariant proof *)
              exists (Z.of_nat K - 1).
              repeat vcgen.
              exists 1%nat.
              esplit; esplit.
              repeat vcgen.
              {
                right.
                split.
                assert (Kcase: (1 = K \/ 1 < K)%nat) by omega.
                Caseeq Kcase; intros.
                - subst.
                  right; split; [reflexivity |].
                  simpl in KPost.
                  subdestruct; subst.
                  inv tmp_cal.
                  rewrite Int.unsigned_repr by omega.
                  reflexivity.
                - left; split; try omega.
                  assert (onerange: (0 <= 1 < K)%nat) by omega.
                  eapply KPre in onerange.
                  simpl in onerange.
                  subdestruct.
                  inv tmp_cal; eauto.
                  clear Hdestruct5.
                  generalize dependent tmp_now.
                  intros ? ?.
                  rewrite Int.unsigned_repr by assumption.
                  intros.
                  apply not_eq_sym; assumption.
                - unfold calculate_wait_lock; simpl.
                  simpl in tmp_cal; rewrite tmp_cal.
                  rewrite Int.unsigned_repr by omega.
                  destruct (zeq my_ticket tmp_now); reflexivity.
              }
              {
                unfold get_cur_ticket; simpl.
                rewrite ZMap.gss.
                simpl in *; rewrite tmp_cal.
                rewrite Int.unsigned_repr by omega.
                reflexivity.
              }
            }
          }
          {
            intro tmp; destruct tmp as [icond Hcalc].
            Caseeq icond.
            { (* i < K and new_ticket <> my_ticket + 1 *)
              intros (irange & neq).

              unfold calculate_wait_lock in Hcalc; simpl in Hcalc.
              subdestruct.
              inv Hcalc.
              assert (tmp: exists tmp_ticket tmp_now tq_tmp,
                            CalTicketLockWraparound (Query m0 ++ m0) =
                            Some (tmp_ticket, tmp_now, tq_tmp)).
            {
              eapply CalTicketWaitWraparoundToIter in KPost; eauto.
              assert ((S i <= K)%nat) by omega.
              eapply CalTicketWaitWraparoundToIterCons in KPost; eauto.
              destruct KPost.
              eapply CalWaitIterInv in H0; eauto.
              - destruct H0 as [? []].
                simpl in H0; rewrite Hdestruct in H0.
                inv H0.
                simpl in H1.
                subdestruct; exists z, z0, l; reflexivity.
              - intros.
                eapply KPre; eauto.
                clear - irange H1.
                omega.
            }
            destruct tmp as [tmp_ticket [tmp_now [tq_tmp tmp_cal]]].
            assert (tmp_now_range: 0 <= tmp_now <= Int.max_unsigned).
            {
              apply CalTicketLockWraparoundRange in tmp_cal.
              destruct tmp_cal; auto.
            }
            assert (tmp_ticket_range: 0 <= tmp_ticket <= Int.max_unsigned).
            {
              apply CalTicketLockWraparoundRange in tmp_cal.
              destruct tmp_cal; auto.
            }
            assert (new_ticket_range: 0 <= new_ticket <= Int.max_unsigned).
            {
              unfold get_cur_ticket in Hcur.
              simpl in Hcur.
              replace (Int.unsigned lock_id) with lock_index in Hcur
                by assumption.
              rewrite ZMap.gss in Hcur.
              subdestruct.
              inv Hcur.
              apply CalTicketLockWraparoundRange in Hdestruct0.
              destruct Hdestruct0; auto.
            }

            esplit; esplit.
            repeat vcgen.
            esplit; esplit.
            repeat vcgen.
            {
              unfold get_now_spec; simpl.
              (* rewrite iihalt. *)
              rewrite id2z.
              rewrite ZMap.gss.
              rewrite tmp_cal.
              instantiate (1:= (Int.repr tmp_now)).
              rewrite Int.unsigned_repr by assumption.
              simpl in Hbar; rewrite Hbar.
              reflexivity.
            }
            { (* invariant proof *)
              exists (Z.of_nat K - Z.of_nat i - 1).
              repeat vcgen.
              esplit; esplit; esplit.
              repeat vcgen.
              {
                instantiate (1 := (S i)).
                right.
                split.
                {
                  assert (icase: (S i = K \/ S i < K)%nat) by omega.
                  Caseeq icase; intros.
                  + (* S i = K *)
                    right.
                    split; auto.
                    assert((K <= K)%nat) by omega.
                    eapply KPostPre in H1.
                    rewrite <-H0 in H1.
                    assert (CalTicketLockWraparound l1 =
                            Some (tmp_ticket, tmp_now, tq_tmp)).
                    {
                      eapply CalWaitIterInv in H1; eauto.
                      - simpl in H1.
                        destruct H1 as [? []].
                        rewrite Hdestruct in H1.
                        inv H1.
                        simpl in H2.
                        subdestruct.
                        + inversion tmp_cal.
                          inversion H2.
                          simpl.
                          rewrite Hdestruct0.
                          rewrite Int.unsigned_repr by omega.
                          rewrite Int.unsigned_repr by omega.
                          assumption.
                        + inversion tmp_cal.
                          inversion H2.
                          simpl.
                          rewrite Hdestruct0.
                          rewrite Int.unsigned_repr by omega.
                          rewrite Int.unsigned_repr by omega.
                          assumption.
                      - intros.
                        eapply KPre; eauto.
                        omega.
                    }
                    eapply CalTicketWaitWraparoundEq; eauto.
                  + left.
                    split; try omega.
                    assert ((0 <= S i < K)%nat) by omega.
                    eapply KPre in H1.
                    eapply CalTicketWaitWraparoundToIter in KPost; eauto.
                    assert ((S i <= K)%nat) by omega.
                    eapply CalTicketWaitWraparoundToIterCons in KPost; eauto.
                    destruct KPost.
                    assert (CalTicketLockWraparound x =
                            Some (tmp_ticket, tmp_now, tq_tmp)).
                    {
                      eapply CalWaitIterInv in H3; eauto.
                      - destruct H3 as [? []].
                        simpl in H3; rewrite Hdestruct in H3.
                        inv H3.
                        simpl in H4.
                        subdestruct.
                        + inversion tmp_cal.
                          inversion H4.
                          simpl.
                          rewrite Hdestruct0.
                          rewrite Int.unsigned_repr by omega.
                          rewrite Int.unsigned_repr by omega.
                          assumption.
                        + inversion tmp_cal.
                          inversion H4.
                          simpl.
                          rewrite Hdestruct0.
                          rewrite Int.unsigned_repr by omega.
                          rewrite Int.unsigned_repr by omega.
                          assumption.
                      - intros.
                        eapply KPre; eauto.
                        omega.
                    }
                    eapply CalWaitIterNeq in H3; eauto.
                    apply Arith.Le.le_n_S, Nat.le_0_l.
                  }
                  {
                    unfold calculate_wait_lock.
                    eapply CalTicketWaitWraparoundToIter in KPost; eauto.
                    assert ((S i <= K)%nat) by omega.
                    eapply CalTicketWaitWraparoundToIterCons in KPost; eauto.
                    cbv zeta in KPost.
                    replace (Int.unsigned lock_id) with lock_index in *
                      by assumption.
                    destruct KPost as [? H1].
                    rewrite initlist in H1. rewrite H1.
                    eapply CalWaitIterInv in H1; eauto.
                    + destruct H1 as [? []].
                      rewrite <- initlist, Hdestruct in H1.
                      inv H1.
                      simpl in H2.
                      subdestruct.
                      * inv tmp_cal.
                        inv H2.
                        rewrite ZMap.set2.
                        reflexivity.
                      * inv tmp_cal.
                        inv H2.
                        rewrite ZMap.set2.
                        reflexivity.
                    + intros. rewrite <- initlist.
                      eapply KPre; eauto.
                      omega.
                  }
                }
                {
                  unfold get_cur_ticket; simpl.
                  rewrite ZMap.gss.
                  simpl.
                  rewrite tmp_cal.
                  rewrite Int.unsigned_repr by omega.
                  reflexivity.
                }
                {
                  rewrite Nat2Z.inj_succ; unfold Z.succ.
                  omega.
                }
              }
            }
            {
              (* i = S K and new_ticket = my_ticket + 1 *)
              intros (ival & ticketseq).
              subst.
              esplit. esplit.
              repeat vcgen.
              unfold wait_lock_loop_body_Q.
              exists newd.
              repeat (split; eauto).
              assert ((K <= (pred cal_time))%nat) by omega.
              unfold calculate_wait_lock in *.
              assert ((K <= K)%nat) by omega.
              move Hcalc at bottom.
              replace lock_index with (Int.unsigned lock_id) in * by assumption.
              rewrite <- initlist in Hcalc.
              erewrite KPostPre in Hcalc; eauto.
              rewrite <- initlist.
              erewrite KPostPre; eauto.
            }
          }
        }
      Qed.

    End LoopProof.

    (* Unwieldier abbreviations, but still useful *)
    Local Notation Query l adt lock_index :=
      (ZMap.get lock_index adt.(oracle) adt.(curid) l)%list
      (only parsing).

    Local Notation nbound bound :=
      (Z.to_nat (Int.unsigned bound))
      (only parsing).

    Local Notation LogToIncrT l0 adt lock_index bound := (
      let l1 := (Query l0 adt lock_index) ++ l0 in
      let l2 := TEVENT (adt.(curid))%list (TTICKET (INC_TICKET (nbound bound))) :: l1 in
      l2
    ) (only parsing).

    Local Notation LogToLoop l0 adt lock_index bound := (
      let l2 := LogToIncrT l0 adt lock_index bound in
      let l3 := Query l2 adt lock_index ++ l2 in
      let l4 := TEVENT (adt.(curid))%list (TTICKET GET_NOW) :: l3 in
      l4
    ) (only parsing).

    Lemma wait_lock_body_correct:
      forall m d d' env le lk
       (Henv: env = PTree.empty _)
       (HPTlk: PTree.get _lk le = Some (Vint lk))

       (* (Hhalt: d.(shared).(halt) = false) *)
       (Hinv: high_level_invariant d)
       (Hspec: wait_lock_spec_wraparound (Int.unsigned lk) d = Some d'),
       exists le', exec_stmt ge env le ((m, d): mem) wait_lock_body
                                E0 le' (m, d') Out_normal.
    Proof.
      generalize max_unsigned_val; intro muval.
      intros; subst.
      unfold wait_lock_body; subst.
      unfold wait_lock_spec_wraparound in Hspec; subst.
      simpl_hyp Hspec.
      (* rewrite Hhalt in Hspec. *)
      Opaque CalTicketLockWraparound CalWaitTime.
      (* Opaque Z.to_nat fairness lock_bound. *)
      pose proof lock_bound_lt_max as Hlock_bound_range.
      subdestruct; subst.
      assert (cal_time_range: (CalWaitTime l > 0)%nat).
      {
        assert (cwt0: CalWaitTime l <> O).
        {
          Transparent CalWaitTime.
          unfold CalWaitTime.
          discriminate 1.
        }
        omega.
      }

      set (cal_time := CalWaitTime l).
      fold cal_time in cal_time_range, Hdestruct2.
      rewrite <- NPeano.Nat.succ_pred_pos with (n:= cal_time) in Hdestruct2
        by omega.
      remember (Int.unsigned lk) as lock_index.
      rename z into t_prev.
      rename z0 into n_prev.
      rename l into tq_prev.
      remember (lock_index @ (d.(log))) as l.

      assert (init_lock_st:
                exists t_init n_init tq_init,
                        CalTicketLockWraparound
                          ((lock_index @ (d.(oracle))) d.(curid) l ++ l) =
                        Some (t_init, n_init, tq_init)
              ).
      { Transparent CalTicketLockWraparound.
        simpl in Hdestruct.
        subdestruct; subst.
        eexists; eexists; eexists; reflexivity.
        Opaque CalTicketLockWraparound.
      }
      destruct init_lock_st as [t_init [n_init [tq_init init_lock_st]]].

      Transparent CalTicketLockWraparound.
      (* unfold CalTicketLockWraparound in Hdestruct0. *)
      assert (ticket_lock_vals:
                Int.unsigned (Int.repr (t_init + 1)) = t_prev /\
                n_init = n_prev /\
                tq_init ++ Z.to_nat lock_bound :: nil = tq_prev
              ).
      {
        (* Transparent CalTicketLockWraparound. *)
        simpl in Hdestruct.
        subdestruct; simpl; subst.
        move Hdestruct2 at bottom.
        clear Hdestruct2 cal_time_range cal_time.
        move init_lock_st at bottom.
        inv init_lock_st; inv Hdestruct.
        split.
        - reflexivity.
        - rewrite Int.unsigned_repr by
            (eapply CalTicketLockWraparoundRange; eauto).
          tauto.
        (* Opaque CalTicketLockWraparound. *)
      }
      Opaque CalTicketLockWraparound.
      destruct ticket_lock_vals as [tlv1 [tlv2 tlv3]]
      ; symmetry in tlv1, tlv2, tlv3
      ; rewrite tlv1, tlv2, tlv3 in *
      ; clear tlv1 tlv2 tlv3
      .

      (* unfold CalTicketWaitWraparound in Hdestruct3. *)
      assert (Ht_init_range: 0 <= t_init <= Int.max_unsigned).
      {
        eapply CalTicketLockWraparoundRange in init_lock_st;
        destruct init_lock_st; auto.
      }

      inv Hdestruct2; subst.
      subdestruct.
      { (* loop terminates immediately *)
        inv Hdestruct2; subst.
        inv Hspec; subst.
        esplit; repeat vcgen.
        + (* first incr_ticket *)
          unfold incr_ticket_spec.
          (* rewrite Hhalt. *)
          rewrite init_lock_st.
          instantiate (1:= Int.repr t_init).
          rewrite Int.unsigned_repr by omega.
          rewrite C. reflexivity.

        + (* first get_now *)
          unfold get_now_spec.
          simpl.
          (* rewrite Hhalt. *)
          rewrite ZMap.gss. rewrite C.
          Transparent lock_bound.
          unfold lock_bound in Hdestruct0.
          Opaque lock_bound.
          replace (Pos.to_nat 10) with (Z.to_nat 10) by reflexivity.
          rewrite Hdestruct0.
          rewrite ZMap.set2.
          instantiate (1:= Int.repr t_init).

          assert (Ht_init_eq:
            Int.unsigned (Int.repr (Int.unsigned (Int.repr (t_init+1))-1)) = t_init).
          {
            assert(tcase: t_init = Int.max_unsigned \/ t_init < Int.max_unsigned) by omega.
            Caseeq tcase.
            - intros t_init_max; rewrite t_init_max; clear t_init_max.
              rewrite muval.
              reflexivity.
            - intros.
              rewrite Int.unsigned_repr; rewrite Int.unsigned_repr; omega.
          }
          rewrite Ht_init_eq.
          rewrite Int.unsigned_repr by assumption.
          reflexivity.

        + (* loop - terminate immediatly *)
          rewrite multi_log_double_update; subst.
          instantiate (2 :=
            (set_opttemp (Some _cur_ticket) (Vint (Int.repr t_init))
            (set_opttemp (Some _t'2) (Vint (Int.repr t_init))
            (set_opttemp (Some _my_ticket)  (Vint (Int.repr t_init))
            (set_opttemp (Some _t'1)  (Vint (Int.repr t_init))
            le))))).
          unfold set_opttemp.

          instantiate (1 :=
            let lock_index := Int.unsigned lk in
            let bound := Int.repr lock_bound in
            d {log: ZMap.set lock_index
              ((LogToLoop ((Int.unsigned lk) @ (d.(log))) d lock_index bound)) d.(log)}).
          unfold wait_lock_loop_condition, wait_lock_loop_body.
          (* (1* problematic *1) *)
          (* Transparent lock_bound. *)
          (*   unfold lock_bound. *)
          (* Opaque lock_bound. *)
          eapply exec_Sloop_stop1; [|constructor].
          eapply exec_Sseq_2; [|discriminate 1].
          repeat vcgen.
        + repeat vcgen.
        + repeat vcgen.
        + unfold log_hold_spec.
          (* rewrite <- halt_remain, Hhalt; simpl. *)
          simpl; rewrite ZMap.gss.
          rewrite multi_log_double_update; subst; simpl.
          rewrite ZMap.set2. rewrite C.
          inv H0. eauto.
        + unfold barrier_spec. simpl.
          subst; simpl. rewrite <- C.
          destruct d; simpl. reflexivity.
      }
      { (* require loop *)
        inv Hspec; subst.

        assert (0 <= z0 <= Int.max_unsigned)
          by (eapply CalTicketLockWraparoundRange; eauto).

        assert (before_get_now:
          let lock_index := Int.unsigned lk in
          let bound := Int.repr lock_bound in
          CalTicketLockWraparound
            (Query (LogToIncrT ((Int.unsigned lk) @ (d.(log))) d lock_index bound) d lock_index ++
            LogToIncrT ((Int.unsigned lk) @ (d.(log))) d lock_index bound)
          = Some (z, z0, l)).

        {
          Transparent CalTicketLockWraparound.
          simpl in Hdestruct0; simpl.
          Opaque CalTicketLockWraparound.
          subdestruct.
          rewrite Int.unsigned_repr in Hdestruct0
            by (eapply CalTicketLockWraparoundRange in Hdestruct1;
                destruct Hdestruct1; eauto).
          rewrite Int.unsigned_repr in Hdestruct0
            by (eapply CalTicketLockWraparoundRange; eauto).
          inv Hdestruct0.
          inv Hdestruct1.
          reflexivity.
        }
        rename H0 into Hdestruct2.
        pose proof Hdestruct2 as HcalcWait;
        pose proof HcalcWait as Hcalctmp.
        eapply CalTicketWaitWraparoundToIter in HcalcWait; eauto.
        eapply CalTicketWaitWraparoundStops in Hdestruct2; eauto.
        destruct Hdestruct2 as [K [Krange [KPre [KPost KPostPre]]]].
        assert (Kgt0: (0 < K)%nat).
        { assert (K = O -> False) by (intro; subst; inv KPost). omega. }

        assert (KRange': (K <= pred cal_time)%nat) by now unfold cal_time.
        assert (Krangelt: (0 < K < cal_time)%nat) by omega.

        set (my_ticket := t_init + 1 - 1).
        fold my_ticket
          in Hcalctmp, HcalcWait, KPostPre, KPost, KPre, n, Hdestruct3.
        assert (my_ticket_prop1: t_init + 1 = my_ticket + 1)
          by (unfold my_ticket; ring).
        assert (my_ticket_prop2: t_init = my_ticket)
          by (unfold my_ticket; ring).
        rewrite my_ticket_prop1 in Hdestruct.
        rewrite my_ticket_prop2 in init_lock_st, Ht_init_range.
        rename z0 into prev_now.
        rename z into prev_ticket.
        rename tq_prev into tq_caltime.
        rename l into tq_prev.
        clear Hdestruct3.
        assert (tiniteq: Int.unsigned (Int.repr (Int.unsigned (Int.repr (t_init + 1)) - 1)) = t_init).
        {
          assert(tcase: t_init = Int.max_unsigned \/ t_init < Int.max_unsigned) by omega.
          Caseeq tcase; intros Htcase.
          - rewrite Htcase.
            Transparent Int.repr.
            rewrite muval.
            reflexivity.
            Opaque Int.repr.
          - repeat (rewrite Int.unsigned_repr; try omega).
        }
        rewrite tiniteq in *.
        rewrite my_ticket_prop2 in *.
        assert(Hdst: (Int.unsigned lk) @ (d.(log)) = (Int.unsigned lk) @ (d.(log))) by reflexivity.
        pose proof (wait_lock_loop_correct_aux m d my_ticket n_init
                                               prev_ticket prev_now
                                               (Int.repr lock_bound)
                                               cal_time tq_init tq_prev
                                               lk (Int.unsigned lk)
                                               ((Int.unsigned lk) @ (d.(log)))
                                               K l0
                                               n eq_refl Hdst
                                               init_lock_st
                                               before_get_now
                                               Krangelt
                                               Hcalctmp KPre KPost KPostPre
                                               Ht_init_range H)
          as LP.
        eapply LoopProofSimpleWhile.termination
          with (condition := wait_lock_loop_condition)
               (body := wait_lock_loop_body)
               (P := wait_lock_loop_body_P m d my_ticket prev_now
                        (Int.repr lock_bound) lk (Int.unsigned lk) ((Int.unsigned lk) @ (d.(log))))
               (Q := wait_lock_loop_body_Q m d my_ticket
                        (Int.repr lock_bound) cal_time lk (Int.unsigned lk) ((Int.unsigned lk) @ (d.(log))))
               (le0 :=
                  (set_opttemp (Some _cur_ticket) (Vint (Int.repr prev_now))
                  (set_opttemp (Some _t'2) (Vint (Int.repr prev_now))
                  (set_opttemp (Some _my_ticket)  (Vint (Int.repr my_ticket))
                  (set_opttemp (Some _t'1)  (Vint (Int.repr my_ticket))
                  le)))))
               (m0 := (m, d {log: ZMap.set (Int.unsigned lk)
                                    (
                                      (LogToLoop ((Int.unsigned lk) @ (d.(log))) d
                                                  (Int.unsigned lk)
                                                  (Int.repr lock_bound)))
                                    d.(log) }))
            in LP.
        { (* prove loop post-condition *)
          destruct LP as (while_le', (while_m', (LP1 & LP2))).
          unfold wait_lock_loop_body_Q in LP2.
          destruct LP2 as (while_d', LP2).
          destruct LP2 as (LP21 & LP22 & LP23 & LP26 & LP27 & LP28).
          destruct while_m' as (while_tmp_m, while_tmp_d').
          esplit; vcgen. vcgen. vcgen. repeat vcgen.
          + (* first incr_ticket *)
            unfold incr_ticket_spec.
            rewrite init_lock_st.
            rewrite Int.unsigned_repr.
            rewrite C.
            * unfold ret; unfold option_monad_ops; repeat f_equal.
            * assumption.
          + vcgen. vcgen. repeat vcgen.
            (* first get_now *)
            unfold get_now_spec.
            simpl.
            rewrite ZMap.gss.
            rewrite C.
            Transparent lock_bound.
            unfold lock_bound in Hdestruct0.
            Opaque lock_bound.
            replace (Pos.to_nat 10) with (Z.to_nat 10) by reflexivity.

            rewrite Hdestruct0.
            rewrite multi_log_double_update.
            rewrite ZMap.set2.
            Focus 2.
            vcgen. vcgen. repeat vcgen.
            vcgen. vcgen. vcgen. vcgen. vcgen.
            vcgen. vcgen. vcgen. vcgen.
            vcgen. vcgen. vcgen. vcgen.
            vcgen. vcgen. vcgen. vcgen.
            vcgen. vcgen. vcgen.
            unfold log_hold_spec.
            inversion LP27.
            rewrite LP28. reflexivity.
            repeat vcgen; simpl.
            inversion LP27. reflexivity.
            unfold barrier_spec; simpl.
            unfold ret; unfold option_monad_ops; repeat f_equal.

            unfold calculate_wait_lock in LP26.
            pose proof lock_bound_lt_max.
            rewrite (Int.unsigned_repr lock_bound) in LP26 by assumption.
            simpl in LP26.
            rewrite HcalcWait in LP26.
            inversion LP26.
            inversion HcalcWait.
            simpl; rewrite ZMap.gss.
            rewrite multi_log_double_update.
            destruct d; simpl.
            simpl in C. rewrite C. rewrite ZMap.set2.
            reflexivity.

            rewrite (Int.unsigned_repr prev_now) by omega.
            reflexivity.
        }
        { (* prove loop precondition *)
          unfold wait_lock_loop_body_P.
          split; [repeat vcgen | ].
          split; [repeat vcgen | ].
          split; [repeat vcgen | ].
          split. reflexivity. assumption.
        }
      }
      inversion Hspec.
      inversion Hspec.
    Qed.

    End BodyProof.

    Theorem wait_lock_code_correct:
      spec_le (wait_lock ↦ wait_lock_spec_low) (〚 wait_lock ↦ f_wait_lock 〛L).
    Proof.
      fbigstep_pre L.
      fbigstep (wait_lock_body_correct
                  s (Genv.globalenv p) makeglobalenv
                  b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b3 Hb3fs Hb3fp b2 Hb2fs Hb2fp
                  m'0 labd labd' (PTree.empty _)
                  (bind_parameter_temps' (fn_params f_wait_lock) (Vint lk::nil)
                  (create_undef_temps (fn_temps f_wait_lock))))
                hinv.
    Qed.

  End wait_lock_proof.

  Section pass_lock_proof.

    Let L : compatlayer (cdata RData) :=
      incr_now ↦ gensem incr_now_spec
          ⊕ barrier     ↦ gensem barrier_spec.

    Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
    Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

    Section BodyProof.

      Context `{Hwb: WritableBlockOps}.
      Variable (sc: stencil).
      Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

      Variable b_incr_now: block.
      Hypothesis h_incr_now_s : Genv.find_symbol ge incr_now = Some b_incr_now.
      Hypothesis h_incr_now_p : Genv.find_funct_ptr ge b_incr_now
                                = Some (External (EF_external incr_now
                                                 (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                       (Tcons tuint Tnil) tvoid cc_default).

      Variable b_barrier: block.
      Hypothesis h_barrier_s : Genv.find_symbol ge barrier = Some b_barrier.
      Hypothesis h_barrier_p : Genv.find_funct_ptr ge b_barrier =
        Some (External (EF_external barrier (signature_of_type
        Tnil tvoid cc_default))
        Tnil tvoid cc_default).


      Lemma pass_lock_body_correct:
        forall m d d' env le lk
               (Henv: env = PTree.empty _)
               (HPTlk: PTree.get _lk le = Some (Vint lk))
               (Hinv: high_level_invariant d)
               (Hspec: pass_lock_spec0 (Int.unsigned lk) d = Some d'),
             exists le', (exec_stmt ge env le ((m, d): mem) pass_lock_body E0 le' (m, d') Out_normal).
      Proof.
        solve_code_proof Hspec pass_lock_body; eexists; solve_proof_low.
        unfold incr_now_spec. simpl.
        rewrite <- C. destruct d; simpl; reflexivity.
      Qed.

    End BodyProof.

    Theorem pass_lock_code_correct:
      spec_le (pass_lock ↦ pass_lock_spec_low) (〚 pass_lock ↦ f_pass_lock 〛 L).
    Proof.
      set (L' := L) in *.
      unfold L in *.
      fbigstep_pre L'.
      fbigstep (pass_lock_body_correct s (Genv.globalenv p) makeglobalenv
                b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp  m'0 labd labd'
               (PTree.empty _) (bind_parameter_temps' (fn_params f_pass_lock )
               (Vint lk :: nil) (create_undef_temps (fn_temps f_pass_lock))))
               hinv.
    Qed.

  End pass_lock_proof.

End LockOpsProofLow.
```
