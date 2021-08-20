# LockOpsRefine

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
Require Import AbstractMachine.Layer.
Require Import AbstractMachine.Spec.
Require Import LockOps.Spec.
Require Import LockOps.Layer.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section LockOpsProofHigh.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := LockOps_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := AbstractMachine_ops) HDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.

    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          id_rel: hadt = ladt;
          barrier_valid: bars ladt = BarrierValid
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

      (* Local Opaque fairness lock_bound. *)

      Lemma wait_lock_kern_mode:
        forall lk d d', wait_lock_spec_wraparound lk d = Some d' ->
                        kernel_mode d.
      Proof.
        unfold wait_lock_spec_wraparound. simpl; intros.
        subdestruct; auto.
      Qed.

      Lemma CalTicketLockExist:
        forall l l' t n,
          CalTicketLock l = Some (t, n, l') ->
          CalTicketLockWraparound l =
            Some (Int.unsigned (Int.repr t), Int.unsigned (Int.repr n), l').
      Proof.
        Local Transparent CalTicketLock CalTicketLockWraparound.
        induction l.
        - simpl.
          inversion 1.
          subst.
          reflexivity.
        - simpl.
          intros until n; intro HCalTicketLock.
          assert
            (zeq: forall z,
                    Int.unsigned (Int.repr (Int.unsigned (Int.repr z) + 1)) =
                    Int.unsigned (Int.repr (z + 1))).
          {
            intros.
            repeat rewrite Int.unsigned_repr_eq.
            unfold Int.modulus, two_power_nat, shift_nat.
            simpl.
            Require Import XOmega.
            repeat match goal with | [H: _ |- _] => clear H end.
            xomega.
          }
          subdestruct; inv HCalTicketLock;
          erewrite IHl; eauto;
          rewrite Int.repr_unsigned;
          try rewrite Int.repr_unsigned;
          try rewrite zeq;
          try reflexivity.
      Qed.

      Lemma CalTicketLock_range:
        forall q l t t0 n n0 l' l0
               (Hcal: CalTicketLock l = Some (t, n, l'))
               (Hcal0: CalTicketLock (q ++ l) = Some (t0, n0, l0)),
          t <= t0 /\ n <= n0.
      Proof.
        induction q; simpl; intros.
        - rewrite Hcal in Hcal0. inv Hcal0.
          split; reflexivity.
        - subdestruct; contra_inv; inv Hcal0; eauto.
          + exploit (IHq l); eauto.
            intros (? & ?). split; omega.
          + exploit (IHq l); eauto.
            intros (? & ?). split; omega.
          + exploit (IHq l); eauto.
            intros (? & ?). split; omega.
      Qed.

      Lemma CalTicketWait_range:
        forall n i t l l' to t0 n0 l0
               (Hwait: CalTicketWait n i t l to = Some l')
               (Hcal: CalTicketLock l = Some (t0, n0, l0)),
          n0 <= t.
      Proof.
        Local Transparent CalTicketWait.
        Opaque CalTicketLock.
        induction n; simpl; intros; try congruence.
        subdestruct; subst.
        - rewrite app_comm_cons in Hdestruct.
          eapply CalTicketLock_range; eauto.
        - eapply IHn in Hwait; try eapply Hdestruct.
          rewrite app_comm_cons in Hdestruct.
          exploit CalTicketLock_range; eauto.
          intros (_ & ?). omega.
      Qed.

      Lemma CalTicketWaitExist:
        forall n l l' i t to t0 n0 l0,
          CalTicketLock l = Some (t0, n0, l0) ->
          t < n0 + TOTAL_CPU ->
          CalTicketWait n i t l to = Some l' ->
          CalTicketWaitWraparound n i (Int.unsigned (Int.repr t)) l to = Some l'.
      Proof.
        Local Transparent CalTicketWait CalTicketWaitWraparound.
        Opaque CalTicketLock CalTicketLockWraparound.
        induction n; [auto|].
        intros.
        simpl in *.
        subdestruct; inv H.
        - eapply CalTicketLockExist in Hdestruct; eauto.
          rewrite Hdestruct.
          rewrite zeq_true. eauto.
        - pose proof Hdestruct as Ht.
          eapply CalTicketLockExist in Hdestruct; eauto.
          rewrite Hdestruct.
          assert (Ht_range: z0 < t < z0 + TOTAL_CPU).
          {
            pose proof H1 as Hwait.
            eapply CalTicketWait_range in Hwait; eauto.
            split; [omega|].
            rewrite app_comm_cons in Ht.
            eapply CalTicketLock_range in H3; eauto.
            destruct H3 as (_ & ?). omega.
          }
          rewrite zeq_false.
          eapply IHn; eauto.
          + omega.
          + revert Ht_range. clear; intros.
            repeat rewrite Int.unsigned_repr_eq.
            unfold Int.modulus, two_power_nat, shift_nat.
            simpl.
            assert (4294967296 > 0) by omega.
            repeat rewrite Zmod_eq; trivial.
            assert (Ht: exists a, t = z0 + a /\ 0 < a < 8).
            {
              unfold TOTAL_CPU in *.
              exists (t - z0).
              split; omega.
            }
            destruct Ht as (a & Ht & Ha). subst. clear Ht_range.
            assert (Hz0: exists c d, z0 = c * 4294967296 + d /\
                                     0 <= d < 4294967296).
            {
              pose proof (Z_div_mod_eq z0 _ H) as Hz0.
              replace (4294967296 * (z0 / 4294967296))
                with ((z0 / 4294967296) * 4294967296)
                in Hz0
                by omega.
              exists (z0 / 4294967296), (z0 mod 4294967296).
              split; trivial.
              eapply Z_mod_lt; eauto.
            }
            destruct Hz0 as (c & d & Hz0 & Hd).
            rewrite Hz0.
            replace (c * 4294967296 + d + a) with (c * 4294967296 + (d + a)) by omega.
            assert (4294967296 <> 0) by omega.
            repeat rewrite Z_div_plus_full_l; trivial.
            repeat rewrite Z.mul_add_distr_r.
            repeat rewrite Zminus_plus_simpl_l.
            assert (Hdv: d / 4294967296 = 0) by xomega.
            rewrite Hdv. simpl.
            replace (d - 0) with d by omega.
            assert (Hr: 0 <= (d + a) < 4294967296 \/  4294967296 <= (d + a) < 4294967296 + TOTAL_CPU).
            {
              destruct (zlt (d + a) 4294967296).
              - left. omega.
              - right. unfold TOTAL_CPU. omega.
            }
            destruct Hr.
            {
              assert (Hdv': (d + a) / 4294967296 = 0) by xomega.
              rewrite Hdv'. simpl. omega.
            }
            {
              assert (Hdv': (d + a) / 4294967296 = 1) by xomega.
              rewrite Hdv'. simpl. omega.
            }
      Qed.

      Lemma wait_lock_spec_exists:
      forall habd habd' labd lk f
             (Hspec: wait_lock_spec lk habd = Some habd')
             (Hrel: relate_RData f habd labd),
        exists labd', wait_lock_spec_wraparound lk labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        Opaque CalTicketLock CalTicketLockWraparound CalTicketWait CalTicketWaitWraparound.
        unfold wait_lock_spec, wait_lock_spec_wraparound, TOTAL_CPU.
        intros.
        inversion Hrel as [hleq]; rewrite hleq in *; clear hleq.
        subdestruct.
        match goal with
        | [H: CalTicketWait _ _ _ _ _ = Some _ |- _] =>
          eapply CalTicketWaitExist in H; eauto
        end.
        - match goal with
          | [H: CalTicketLock _ = Some (_, _, _) |- _] =>
            eapply CalTicketLockExist in H; eauto
          end.
          subrewrite'.
          assert (z1eq: (Int.unsigned (Int.repr (Int.unsigned (Int.repr z) - 1))) =
                        (Int.unsigned (Int.repr (z - 1)))).
          {
            rewrite Int.unsigned_repr_eq,
                    Int.unsigned_repr_eq,
                    Int.unsigned_repr_eq.
            Require Import XOmega.
            unfold Int.modulus, two_power_nat, shift_nat; simpl.
            clear; xomega.
          }
          subrewrite'.
          refine_split.
          + reflexivity.
          + inversion Hspec; subst. constructor. reflexivity.
            simpl; assumption.
        - unfold TOTAL_CPU; omega.
      Qed.

      Lemma wait_lock_spec_ref:
        compatsim (crel RData RData) (gensem wait_lock_spec) wait_lock_spec_low.
      Proof.
        Opaque wait_lock_spec.
        compatsim_simpl (@match_RData).
        exploit wait_lock_spec_exists; eauto 1;
        intros (labd' & Hspec & Hrel).
        refine_split; repeat (try econstructor; eauto).
      Qed.

      Lemma pass_lock_spec_exists:
        forall habd habd' labd lk f
               (Hspec: pass_lock_spec lk habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', pass_lock_spec0 lk labd = Some labd' /\
                        relate_RData f habd' labd'.
      Proof.
        unfold pass_lock_spec, pass_lock_spec0; intros until f; exist_simpl.
      Qed.

    End FreshPrim.

    Section PassthroughPrim.

      Lemma get_pgd_next_spec_exists:
        forall vmid next habd labd f
               (Hspec: get_pgd_next_spec vmid habd = Some next)
               (Hrel: relate_RData f habd labd),
          get_pgd_next_spec0 vmid labd = Some next.
      Proof.
        unfold get_pgd_next_spec, get_pgd_next_spec0; intros.
        destruct Hrel. srewrite. reflexivity.
      Qed.

      Lemma get_pud_next_spec_exists:
        forall vmid next habd labd f
               (Hspec: get_pud_next_spec vmid habd = Some next)
               (Hrel: relate_RData f habd labd),
          get_pud_next_spec0 vmid labd = Some next.
      Proof.
        unfold get_pud_next_spec, get_pud_next_spec0; intros.
        destruct Hrel. srewrite. reflexivity.
      Qed.

      Lemma get_pmd_next_spec_exists:
        forall vmid next habd labd f
               (Hspec: get_pmd_next_spec vmid habd = Some next)
               (Hrel: relate_RData f habd labd),
          get_pmd_next_spec0 vmid labd = Some next.
      Proof.
        unfold get_pmd_next_spec, get_pmd_next_spec0; intros.
        destruct Hrel. srewrite. reflexivity.
      Qed.

      Lemma set_pgd_next_spec_exists:
        forall vmid next habd habd' labd f
               (Hspec: set_pgd_next_spec vmid next habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_pgd_next_spec0 vmid next labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold set_pgd_next_spec, set_pgd_next_spec0; intros.
        destruct Hrel. srewrite.
        eexists; split. reflexivity.
        constructor. reflexivity.
        autounfold in Hspec; repeat simpl_hyp Hspec; inv Hspec; simpl; assumption.
      Qed.

      Lemma set_pud_next_spec_exists:
        forall vmid next habd habd' labd f
               (Hspec: set_pud_next_spec vmid next habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_pud_next_spec0 vmid next labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold set_pud_next_spec, set_pud_next_spec0; intros.
        destruct Hrel. srewrite.
        eexists; split. reflexivity.
        constructor. reflexivity.
        autounfold in Hspec; repeat simpl_hyp Hspec; inv Hspec; simpl; assumption.
      Qed.

      Lemma set_pmd_next_spec_exists:
        forall vmid next habd habd' labd f
               (Hspec: set_pmd_next_spec vmid next habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', set_pmd_next_spec0 vmid next labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold set_pmd_next_spec, set_pmd_next_spec0; intros.
        destruct Hrel. srewrite.
        eexists; split. reflexivity.
        constructor. reflexivity.
        autounfold in Hspec; repeat simpl_hyp Hspec; inv Hspec; simpl; assumption.
      Qed.

      Lemma pt_load_spec_exists:
        forall vmid addr habd labd val f
               (Hspec: pt_load_spec vmid addr habd = Some val)
               (Hrel: relate_RData f habd labd),
          pt_load_spec0 vmid addr labd = Some val.
      Proof.
        unfold pt_load_spec, pt_load_spec0; intros.
        destruct Hrel. srewrite. reflexivity.
      Qed.

      Lemma pt_store_spec_exists:
        forall vmid addr val habd habd' labd f
               (Hspec: pt_store_spec vmid addr val habd = Some habd')
               (Hrel: relate_RData f habd labd),
          exists labd', pt_store_spec0 vmid addr val labd = Some labd' /\ relate_RData f habd' labd'.
      Proof.
        unfold pt_store_spec, pt_store_spec0; intros.
        destruct Hrel. srewrite.
        eexists; split. reflexivity.
        constructor. reflexivity.
        autounfold in Hspec; repeat simpl_hyp Hspec; inv Hspec; simpl; assumption.
      Qed.

    End PassthroughPrim.

  End WITHMEM.

End LockOpsProofHigh.
```
