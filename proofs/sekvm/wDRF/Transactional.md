# Transactional

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

Require Import HypsecCommLib.
Require Import Constants.
Require Import RData.
Require Import AbstractMachine.Spec.
Require Import PTWalk.Spec.
Require Import NPTWalk.Spec.
Require Import NPTWalk.ProofHighAux.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section TransactionalProof.

  Definition pt_map (vmid: Z) (addr: Z) (npt: NPT) :=
    let vttbr := pt_vttbr vmid in
    let vttbr_pa := phys_page vttbr in
    let pgd_idx := pgd_index addr in
    let pgd_p := Z.lor vttbr_pa (pgd_idx * 8) in
    let pgd := pgd_p @ (pt_vttbr_pool npt) in
    if pgd =? 0 then 0
    else
      let pgd_pa := phys_page pgd in
      let pud_idx := pud_index addr in
      let pud_p := Z.lor pgd_pa (pud_idx * 8) in
      let pud := pud_p @ (pt_pgd_pool npt) in
      if pud =? 0 then 0
      else
        let pud_pa := phys_page pud in
        let pmd_idx := pmd_index addr in
        let pmd_p := Z.lor pud_pa (pmd_idx * 8) in
        let pmd := pmd_p @ (pt_pud_pool npt) in
        if pmd =? 0 then 0
        else
          if pmd_table pmd =? PMD_TYPE_TABLE then
            let pmd_pa := phys_page pmd in
            let pte_idx := pte_index addr in
            let pte_p := Z.lor pmd_pa (pte_idx * 8) in
            let pte := pte_p @ (pt_pmd_pool npt) in
            pte
          else
            pmd.

  Fixpoint update_npt updates npt :=
    match updates with
    | nil => npt
    | u :: updates' =>
      let npt' := update_npt updates' npt in
      match u with
      | UPDATE_PGD pgd_p pgd =>
        npt' {pt_vttbr_pool: (pt_vttbr_pool npt) # pgd_p == pgd}
      | UPDATE_PUD pud_p pud =>
        npt' {pt_pgd_pool: (pt_pgd_pool npt) # pud_p == pud}
      | UPDATE_PMD pmd_p pmd =>
        npt' {pt_pud_pool: (pt_pud_pool npt) # pmd_p == pmd}
      | UPDATE_PTE pte_p pte =>
        npt' {pt_pmd_pool: (pt_pmd_pool npt) # pte_p == pte}
      end
    end.

  Fixpoint insert_into_lists (e: NPT_UPDATE) (lists: list (list NPT_UPDATE)) :=
    match lists with
    | nil => nil
    | l :: lists' =>
      (e :: l) :: (insert_into_lists e lists')
    end.

  Fixpoint sample_updates updates :=
    match updates with
    | nil => (nil :: nil)
    | u :: updates' =>
      (sample_updates updates') ++ (insert_into_lists u (sample_updates updates'))
    end.

  Fixpoint insert_into_middle (pre: list NPT_UPDATE) (post: list NPT_UPDATE) (e: NPT_UPDATE) :=
    match post with
    | nil => (pre ++ (e::nil)) :: nil
    | u :: post' =>
      (pre ++ (e::nil) ++ post) :: (insert_into_middle (pre ++ (u::nil)) post' e)
    end.

  Fixpoint insert_into_shuffled_lists (e: NPT_UPDATE) (lists: list (list NPT_UPDATE)) :=
    match lists with
    | nil => nil
    | l :: lists' =>
      (insert_into_middle nil l e) ++ (insert_into_shuffled_lists e lists')
    end.

  Fixpoint shuffle_updates updates :=
    match updates with
    | nil => nil :: nil
    | u :: updates' =>
      insert_into_shuffled_lists u (shuffle_updates updates')
    end.

  Fixpoint shuffle_lists lists :=
    match lists with
    | nil => nil
    | update :: lists' =>
      (shuffle_updates update) ++ (shuffle_lists lists')
    end.

  Definition sample_and_shuffle_updates updates :=
    let samples := sample_updates updates in
    shuffle_lists samples.

  Ltac get_sample :=
    match goal with
    | [H: In _ (shuffle_updates ?up) |- _ ] => remember up as sample
    end.

  Ltac simpl_In_app :=
    repeat match goal with
           | [H: In _ (_ ++ _) |- _] => apply in_app_or in H; destruct H as [H|H]
           end.

  Lemma TransactionalPageTableWriteLevel3:
    forall vmid addr level pte adt adt'
      (Hset: set_npt_spec0 vmid (VZ64 addr) level (VZ64 pte) adt = Some adt')
      (Hvmid: valid_vmid vmid)
      (Haddr: valid_addr addr)
      (Hhalt: halt adt = false)
      (Hhalt': halt adt' = false)
      (Hlevel: level <> 2)
      (Hbuffer: forall vmid, (pt_updates (vmid @ (npts (shared adt))) = nil))
      (Hvalid: forall vmid, valid_lnpt vmid (vmid @ (npts (shared adt)))),
    forall observer,
      let npt := observer @ (npts (shared adt)) in
      let npt' := observer @ (npts (shared adt')) in
      forall updates npt_mid
        (Hupdates: In updates (sample_and_shuffle_updates (pt_updates npt')))
        (Hnpt_mid: npt_mid = update_npt updates npt),
      forall address (Haddress: valid_addr address),
        In (pt_map observer address npt_mid) ((pt_map observer address npt) :: (pt_map observer address npt') :: nil).
  Proof.
    intros until observer.
    unfold set_npt_spec0 in Hset.
    autounfold in Hset; unfold panic_spec in Hset.
    pose proof (vttbr_val vmid Hvmid) as Hvttbr.
    assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
    { rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. }
    repeat simpl_hyp Hset; subst.
    - (* level = 2 *)
      bool_rel; contra.
    - (* level = 3 *)
      rename z0 into vttbr. rename z2 into pgd. rename z4 into pud.
      rename C into Sget_vttbr. rename C2 into Swalk_pgd.
      rename C6 into Swalk_pud. rename C11 into Swalk_pmd.
      rename Hset into Sset_pte.
      unfold get_pt_vttbr_spec in Sget_vttbr; rewrite Hhalt in Sget_vttbr.
      autounfold in *. repeat simpl_hyp Sget_vttbr. inversion Sget_vttbr.
      clear Sget_vttbr. rename H0 into Hvttbr_val.
      unfold walk_pgd_spec in Swalk_pgd; rewrite Hhalt in Swalk_pgd.
      autounfold in *. repeat simpl_hyp Swalk_pgd; inv Swalk_pgd.
      + (* pgd does not exist *)
        unfold walk_pud_spec in Swalk_pud; simpl in *.
        repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        rewrite Hhalt in *. autounfold in *.
        rewrite andb_comm in C7; simpl in C7.
        repeat simpl_hyp Swalk_pud; inv Swalk_pud;
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        * (* or3 contra *)
          bool_rel. apply or3nz in C16. inv C16.
        * (* pud does not exist *)
          rewrite andb_comm in C19; simpl in C19.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          rewrite Hhalt in *. autounfold in *.
          repeat simpl_hyp Swalk_pmd; inv Swalk_pmd;
            repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          (* or3 contra *)
          bool_rel. apply or3nz in C23. inv C23.
          (* pmd does not exist *)
          rewrite andb_comm in C26; simpl in C26.
          rewrite Hhalt in *. autounfold in *. repeat simpl_hyp Sset_pte; inv Sset_pte.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PGD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a) as Hvttbr_pool'
                    end.
                    destruct Hvttbr_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PGD PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      right. assumption.
                      rewrite (ZMap.gso _ _ Hneq).
                      rewrite (Hpgd_next). reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PGD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a) as Hvttbr_pool'
                    end.
                    destruct Hvttbr_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PGD PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. destruct_if. reflexivity.
                      destruct (zeq (pmd_index address) (pmd_index addr)).
                      * rewrite e1. rewrite ZMap.gss. destruct_if. reflexivity.
                        rewrite Hpmd_next. rewrite and_or_same. reflexivity.
                        rewrite phys_page_or_not_change.
                        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                        apply or_index_range. autounfold in *. omega. assumption.
                        autounfold; somega. omega. omega. assumption.
                      * assert_gso. apply or_index_ne_cond; try assumption.
                        apply phys_page_fixed. apply phys_page_fixed.
                        right. assumption.
                        rewrite (ZMap.gso _ _ Hneq).
                        rewrite (Hpud_next). reflexivity.
                        rewrite phys_page_or_not_change.
                        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                        apply or_index_range. autounfold in *. omega. assumption.
                        autounfold; somega. omega. omega. assumption.
                    +  assert_gso. autounfold.
                       apply or_index_ne_cond; try assumption.
                       apply phys_page_fixed. apply phys_page_fixed.
                       autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                       rewrite (Hpgd_next). reflexivity.
                       rewrite phys_page_or_not_change.
                       match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                       apply or_index_range. autounfold in *. omega. assumption.
                       autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0).
                    destruct_if. reflexivity.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq1). reflexivity.
                }
              + get_sample. (* [PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                }
              + get_sample. (* [PGD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                }
              + get_sample. (* [PUD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                }
              + get_sample. (* [PGD PUD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      right. assumption.
                      rewrite (ZMap.gso _ _ Hneq).
                      rewrite (Hpgd_next). reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq1). reflexivity. reflexivity.
                }
              + get_sample. (* [PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                }
              + get_sample. (* [PGD PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq1). reflexivity. reflexivity.
                }
              + get_sample. (* [PUD PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a) as Hvttbr_pool'
                    end.
                    destruct Hvttbr_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0).
                    destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. autounfold in *. rewrite Hvttbr in Case2. bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq1). reflexivity. reflexivity.
                }
              + get_sample. (* [PGD PUD PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
          (* halt *)
          simpl in *. simpl_hyp Sset_pte; inv Sset_pte; inv Hhalt'.
          (* next <> 0 contra *)
          destruct (Hvalid vmid).
          rewrite Hpud_next in C26. inversion C26.
          rewrite phys_page_or_not_change.
          match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
          apply or_index_range. autounfold in *. omega. assumption.
          autounfold; somega. omega. omega. assumption.
        * (* halt *)
          simpl in *. inv Swalk_pmd. simpl in *. simpl_hyp Sset_pte; inv Sset_pte; inv Hhalt'.
        * (* next <> 0 contra *)
          rewrite andb_comm in C19; simpl in C19.
          destruct (Hvalid vmid).
          rewrite Hpgd_next in C19. inversion C19.
          rewrite phys_page_or_not_change.
          match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
          apply or_index_range. autounfold in *. omega. assumption.
          autounfold; somega. omega. omega. assumption.
      + (* halt *)
        hsimpl_func Swalk_pud; simpl in *; hsimpl_func Swalk_pmd; simpl in *;
          hsimpl_func Sset_pte; simpl in *; contra.
      + (* pgd exists *)
        unfold walk_pud_spec in Swalk_pud; simpl in *.
        repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        rewrite Hhalt in *. autounfold in *.
        repeat simpl_hyp Swalk_pud; inv Swalk_pud;
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        * (* halt *)
          contra.
        * (* pud does not exist *)
          rewrite andb_comm in C17; simpl in C17.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          rewrite Hhalt in *. autounfold in *.
          repeat simpl_hyp Swalk_pmd; inv Swalk_pmd;
            repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          (* or3 contra *)
          bool_rel. apply or3nz in C21. inv C21.
          (* pmd does not exist *)
          rewrite andb_comm in C24; simpl in C24.
          rewrite Hhalt in *. autounfold in *. repeat simpl_hyp Sset_pte; inv Sset_pte.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. autounfold; srewrite.
                      destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                  - destruct_if. reflexivity. rewrite Hvttbr; autounfold.
                    assert_gso. apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. autounfold in *; rewrite Hvttbr in *.
                    eapply pgd_index_diff_res_diff; bool_rel; try assumption. apply Hvalid.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. srewrite. reflexivity.
                    + destruct_if. reflexivity.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpgd_pool a) as Hpgd_pool'
                      end.
                      destruct Hpgd_pool' as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq). reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpgd_pool a) as Hpgd_pool'
                    end.
                    destruct Hpgd_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. autounfold; srewrite.
                      destruct (zeq (pmd_index address) (pmd_index addr)).
                      * rewrite e1. rewrite ZMap.gss. autounfold; srewrite.
                        destruct_if. reflexivity.
                        rewrite Hpmd_next. reflexivity.
                        rewrite phys_page_or_not_change.
                        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                        apply or_index_range. autounfold in *. omega. assumption.
                        autounfold; somega. omega. omega. assumption.
                      * assert_gso. autounfold.
                        apply or_index_ne_cond; try assumption.
                        apply phys_page_fixed. apply phys_page_fixed.
                        autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                        rewrite Hpud_next. reflexivity.
                        rewrite phys_page_or_not_change.
                        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                        apply or_index_range. autounfold in *. omega. assumption.
                        autounfold; somega. omega. omega. assumption.
                    + assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                      destruct_if. reflexivity.
                      assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                        pose proof (Hpgd_pool a)
                      end.
                      destruct H. rewrite H.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega. destruct H. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                  - repeat rewrite Hvttbr. destruct_if. reflexivity.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    autounfold. left.
                    autounfold in *; rewrite Hvttbr in *.
                    eapply pgd_index_diff_res_diff; bool_rel; try assumption. apply Hvalid.
                    rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. srewrite. reflexivity.
                    + destruct_if. reflexivity. destruct_if. reflexivity.
                      destruct_if.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpud_pool a)
                      end.
                      destruct H as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. autounfold in *; bool_rel; contra.
                      destruct H. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                  - destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. autounfold in *; rewrite Hvttbr in *; bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                }
              + get_sample. (* [PUD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. autounfold; srewrite.
                      destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                      destruct_if. reflexivity. destruct_if. reflexivity. destruct_if.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpud_pool a)
                      end.
                      destruct H as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. autounfold in *; bool_rel; contra.
                      destruct H. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                  - destruct_if. reflexivity. rewrite Hvttbr; autounfold.
                    assert_gso. apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. autounfold in *; rewrite Hvttbr in *.
                    eapply pgd_index_diff_res_diff; bool_rel; try assumption. apply Hvalid.
                    rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity. destruct_if. reflexivity. destruct_if.
                    assert_gso. apply or_index_ne_cond.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite Hvttbr. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. autounfold in *; rewrite Hvttbr in *; bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                }
              + get_sample. (* [PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. autounfold; srewrite. reflexivity.
                    + destruct_if. reflexivity.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpgd_pool a)
                      end.
                      destruct H as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq).
                      destruct_if. reflexivity. destruct_if.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpud_pool a)
                      end.
                      destruct H as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. autounfold in *; bool_rel; contra.
                      destruct H. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                  - destruct_if. reflexivity. destruct_if. reflexivity.
                    assert_gso. apply or_index_ne_cond.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. apply or_index_ne_cond.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. autounfold in *; bool_rel; contra.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity. reflexivity.
                }
              + get_sample. (* [PUD PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
          (* halt *)
          simpl in *. simpl_hyp Sset_pte; inv Sset_pte; inv Hhalt'.
          (* next <> 0 contra *)
          destruct (Hvalid vmid).
          rewrite Hpud_next in C24. inversion C24.
          rewrite phys_page_or_not_change.
          match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
          apply or_index_range. autounfold in *. omega. assumption.
          autounfold; somega. omega. omega. assumption.
        * (* halt *)
          simpl in *. inv Swalk_pmd. simpl in *. simpl_hyp Sset_pte; inv Sset_pte; inv Hhalt'.
        * (* pud exists *)
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          rewrite Hhalt in *. autounfold in *.
          repeat simpl_hyp Swalk_pmd; inv Swalk_pmd;
            repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          contra.
          (* pmd does not exist *)
          rewrite andb_comm in C22; simpl in C22.
          rewrite Hhalt in *. autounfold in *. repeat simpl_hyp Sset_pte; inv Sset_pte.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. autounfold; srewrite.
                      destruct (zeq (pmd_index address) (pmd_index addr)).
                      * rewrite e1. rewrite ZMap.gss. autounfold; srewrite.
                        destruct_if. reflexivity.
                        rewrite Hpmd_next. reflexivity.
                        rewrite phys_page_or_not_change.
                        match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                        apply or_index_range. autounfold in *. omega. assumption.
                        autounfold; somega. omega. omega. assumption.
                      * assert_gso. autounfold.
                        apply or_index_ne_cond; try assumption.
                        apply phys_page_fixed. apply phys_page_fixed.
                        autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                    + destruct_if. reflexivity.
                      assert_gso. apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. autounfold in *. rewrite <- e at 1.
                      eapply pud_index_diff_res_diff; bool_rel; try rewrite e; try assumption. apply Hvalid.
                      right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                  - destruct_if. reflexivity. destruct_if. reflexivity.
                    assert_gso. apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. autounfold in *. rewrite Hvttbr in *.
                    eapply pud_index_diff_res_diff; bool_rel; try rewrite e; try assumption. apply Hvalid.
                    left; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. srewrite.
                      destruct (zeq (pmd_index address) (pmd_index addr)).
                      * rewrite e1. srewrite. reflexivity.
                      * destruct_if. reflexivity. destruct_if.
                        assert_gso. apply or_index_ne_cond.
                        apply phys_page_fixed. apply phys_page_fixed.
                        left. rewrite phys_page_or_not_change.
                        match goal with
                        | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                          pose proof (Hpud_pool a)
                        end.
                        destruct H as [P|P]. rewrite P.
                        match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                        autounfold in *; omega.
                        destruct P. autounfold in *; bool_rel; contra.
                        destruct H. omega. omega. assumption.
                        rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                    + destruct_if. reflexivity. destruct_if. reflexivity. destruct_if.
                      assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                        pose proof (Hpud_pool a)
                      end.
                      destruct H as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. autounfold in *; bool_rel; contra.
                      destruct H. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                  - destruct_if. reflexivity. destruct_if. reflexivity.
                    destruct_if. reflexivity. destruct_if.
                    assert_gso. autounfold.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left.
                    match goal with
                    | [ |- context[?a @ (pt_pud_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpud_pool a)
                    end.
                    destruct H as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    rewrite phys_page_or_not_change. autounfold in *; omega. omega. assumption.
                    destruct P. autounfold in *; bool_rel; contra.
                    destruct H. rewrite phys_page_or_not_change with (n:=3). omega.
                    omega. assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity. reflexivity.
                }
              + get_sample. (* [PMD PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
          (* halt *)
          repeat simpl_hyp Sset_pte; inv Sset_pte; inv Hhalt'.
          (* pmd exists *)
          rewrite Hhalt in Sset_pte.
          autounfold in *. repeat simpl_hyp Sset_pte; inv Sset_pte.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r1))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PTE] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r1))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
    - inv Hset. inv Hhalt'.
  Qed.

  Lemma TransactionalPageTableWriteLevel2:
    forall vmid addr level pte adt adt'
      (Hset: set_npt_spec0 vmid (VZ64 addr) level (VZ64 pte) adt = Some adt')
      (Hvmid: valid_vmid vmid)
      (Haddr: valid_addr addr)
      (Hhalt: halt adt = false)
      (Hhalt': halt adt' = false)
      (Hlevel: level = 2)
      (Hbuffer: forall vmid, (pt_updates (vmid @ (npts (shared adt))) = nil))
      (Hvalid: forall vmid, valid_lnpt vmid (vmid @ (npts (shared adt)))),
    forall observer,
      let npt := observer @ (npts (shared adt)) in
      let npt' := observer @ (npts (shared adt')) in
      forall updates npt_mid
        (Hupdates: In updates (sample_and_shuffle_updates (pt_updates npt')))
        (Hnpt_mid: npt_mid = update_npt updates npt),
      forall address (Haddress: valid_addr address),
        In (pt_map observer address npt_mid) ((pt_map observer address npt) :: (pt_map observer address npt') :: nil).
  Proof.
    intros until observer.
    unfold set_npt_spec0 in Hset.
    autounfold in Hset; unfold panic_spec in Hset.
    pose proof (vttbr_val vmid Hvmid) as Hvttbr.
    assert(vttbr_align: phys_page (pool_start vmid) = pool_start vmid).
    { rewrite <- Hvttbr. rewrite phys_page_fixed. reflexivity. }
    repeat simpl_hyp Hset; subst.
    - (* level = 2 *)
      rename z0 into vttbr. rename z2 into pgd. rename z4 into pud.
      rename C into Sget_vttbr. rename C2 into Swalk_pgd.
      rename C6 into Swalk_pud. rename Hset into Sset_pmd.
      unfold get_pt_vttbr_spec in Sget_vttbr; rewrite Hhalt in Sget_vttbr.
      autounfold in *. repeat simpl_hyp Sget_vttbr. inversion Sget_vttbr.
      clear Sget_vttbr. rename H0 into Hvttbr_val.
      unfold walk_pgd_spec in Swalk_pgd; rewrite Hhalt in Swalk_pgd.
      autounfold in *. repeat simpl_hyp Swalk_pgd; inv Swalk_pgd.
      + (* pgd does not exist *)
        unfold walk_pud_spec in Swalk_pud; simpl in *.
        repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        rewrite Hhalt in *. autounfold in *.
        repeat simpl_hyp Swalk_pud; inv Swalk_pud;
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        * (* or3 contra *)
          bool_rel. apply or3nz in C14. inv C14.
        * (* pud does not exist *)
          rewrite andb_comm in C7; simpl in C7.
          rewrite Hhalt in Sset_pmd.
          autounfold in *. repeat simpl_hyp Sset_pmd; inv Sset_pmd.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PGD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a) as Hvttbr_pool'
                    end.
                    destruct Hvttbr_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PGD PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      right. assumption.
                      rewrite (ZMap.gso _ _ Hneq).
                      rewrite (Hpgd_next). reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a)
                    end.
                    destruct H. rewrite H.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega. destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PGD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. rewrite ZMap.gss. autounfold. srewrite.
                    rewrite Hpgd_next. reflexivity.
                    rewrite phys_page_or_not_change.
                    match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                    apply or_index_range. autounfold in *. omega. assumption.
                    autounfold; somega. omega. omega. assumption.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite. reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_vttbr_pool vmid @ (npts (shared adt)))]] =>
                      pose proof (Hvttbr_pool a) as Hvttbr_pool'
                    end.
                    destruct Hvttbr_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq).
                    assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared _)))]] =>
                      pose proof (Hpgd_pool a)
                    end.
                    destruct H. rewrite H. replace (phys_page 0) with 0 by reflexivity. autounfold in *; omega.
                    destruct H. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq0). reflexivity.
                }
              + get_sample. (* [PGD PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared adt))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
        * (* halt *)
          simpl in *. inv Sset_pmd; inv Hhalt'.
        * (* next <> 0 contra *)
          rewrite andb_comm in C17; simpl in C17.
          destruct (Hvalid vmid).
          rewrite Hpgd_next in C17. inversion C17.
          rewrite phys_page_or_not_change.
          match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
          apply or_index_range. autounfold in *. omega. assumption.
          autounfold; somega. omega. omega. assumption.
      + (* halt *)
        hsimpl_func Swalk_pud; simpl in *; hsimpl_func Sset_pmd; simpl in *; contra.
      + (* pgd exists *)
        unfold walk_pud_spec in Swalk_pud; simpl in *.
        repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        rewrite Hhalt in *. autounfold in *.
        repeat simpl_hyp Swalk_pud; inv Swalk_pud;
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
        * (* halt *)
          contra.
        * (* pud does not exist *)
          rewrite andb_comm in C15; simpl in C15.
          rewrite Hhalt in Sset_pmd.
          autounfold in *. repeat simpl_hyp Sset_pmd; inv Sset_pmd.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PUD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. rewrite ZMap.gss. autounfold; srewrite.
                      destruct_if. reflexivity.
                      rewrite Hpud_next. reflexivity.
                      rewrite phys_page_or_not_change.
                      match goal with |- context[Z.lor ?a ?b] => assert(a <= Z.lor a b < a + 4096) end.
                      apply or_index_range. autounfold in *. omega. assumption.
                      autounfold; somega. omega. omega. assumption.
                    + assert_gso. autounfold.
                      apply or_index_ne_cond; try assumption.
                      apply phys_page_fixed. apply phys_page_fixed.
                      autounfold. right; assumption. rewrite (ZMap.gso _ _ Hneq). reflexivity.
                  - destruct_if. reflexivity. rewrite Hvttbr; autounfold.
                    assert_gso. apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. autounfold in *; rewrite Hvttbr in *.
                    eapply pgd_index_diff_res_diff; bool_rel; try assumption. apply Hvalid.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                left. unfold pt_map. simpl.
                {
                  destruct (zeq (pgd_index address) (pgd_index addr)).
                  - rewrite e. autounfold. srewrite.
                    destruct (zeq (pud_index address) (pud_index addr)).
                    + rewrite e0. srewrite. reflexivity.
                    + destruct_if. reflexivity.
                      assert_gso. apply or_index_ne_cond.
                      apply phys_page_fixed. apply phys_page_fixed.
                      left. rewrite phys_page_or_not_change.
                      match goal with
                      | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                        pose proof (Hpgd_pool a) as Hpgd_pool'
                      end.
                      destruct Hpgd_pool' as [P|P]. rewrite P.
                      match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                      autounfold in *; omega.
                      destruct P. omega. omega. assumption.
                      rewrite (ZMap.gso _ _ Hneq). reflexivity.
                  - assert_gso. autounfold. rewrite Hvttbr.
                    apply or_index_ne_cond; try assumption.
                    apply phys_page_fixed. apply phys_page_fixed.
                    left. rewrite phys_page_or_not_change.
                    match goal with
                    | [ |- context[?a @ (pt_pgd_pool vmid @ (npts (shared r)))]] =>
                      pose proof (Hpgd_pool a) as Hpgd_pool'
                    end.
                    destruct Hpgd_pool' as [P|P]. rewrite P.
                    match goal with |- ?a <> _ => replace a with 0 by reflexivity end.
                    autounfold in *; omega.
                    destruct P. omega. omega. assumption.
                    rewrite (ZMap.gso _ _ Hneq). reflexivity.
                }
              + get_sample. (* [PUD PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
        * (* halt *)
          inv Sset_pmd. inv Hhalt'.
        * (* pud exists *)
          rewrite Hhalt in Sset_pmd.
          autounfold in *. repeat simpl_hyp Sset_pmd; inv Sset_pmd.
          repeat rewrite ZMap.gss, ZMap.set2 in *; simpl in *.
          {
            destruct (zeq observer vmid).
            - (* observer = vmid *)
              subst. repeat rewrite ZMap.gss in *; simpl in *.
              intros. unfold sample_and_shuffle_updates in Hupdates.
              rewrite Hbuffer in Hupdates.
              Local Opaque shuffle_updates.
              simpl in Hupdates.
              Local Transparent shuffle_updates.
              destruct (Hvalid vmid).
              simpl_In_app.
              + get_sample. (* [] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                auto.
              + get_sample. (* [PMD] *)
                assert(Hmid: npt_mid = update_npt sample vmid @ (npts (shared r0))).
                { rewrite Hnpt_mid. rewrite Heqsample. rewrite Heqsample in Hupdates.
                  simpl in Hupdates.
                  repeat destruct Hupdates as [Hupdates|Hupdates];
                    subst; try reflexivity; try inv Hupdates. }
                clear Hupdates Hnpt_mid. rewrite Heqsample in Hmid. rewrite Hmid; simpl.
                right. left. unfold pt_map. simpl. reflexivity.
              + (* nil *) destruct Hupdates.
            - (* observer <> vmid *)
              rewrite (ZMap.gso _ _ n).
              intros. rewrite Hbuffer in Hupdates. simpl in Hupdates.
              destruct Hupdates; subst; simpl. auto. inv H.
          }
    - (* level <> 2 contra *)
      inv C10.
    - inv Hset. inv Hhalt'.
  Qed.

  Theorem TransactionalPageTableWrite:
    forall vmid addr level pte adt adt'
      (Hset: set_npt_spec0 vmid (VZ64 addr) level (VZ64 pte) adt = Some adt')
      (Hvmid: valid_vmid vmid)
      (Haddr: valid_addr addr)
      (Hhalt: halt adt = false)
      (Hhalt': halt adt' = false)
      (Hbuffer: forall vmid, (pt_updates (vmid @ (npts (shared adt))) = nil))
      (Hvalid: forall vmid, valid_lnpt vmid (vmid @ (npts (shared adt)))),
    forall observer,
      let npt := observer @ (npts (shared adt)) in
      let npt' := observer @ (npts (shared adt')) in
      forall updates npt_mid
        (Hupdates: In updates (sample_and_shuffle_updates (pt_updates npt')))
        (Hnpt_mid: npt_mid = update_npt updates npt),
      forall address (Haddress: valid_addr address),
        In (pt_map observer address npt_mid) ((pt_map observer address npt) :: (pt_map observer address npt') :: nil).
  Proof.
    intros until observer.
    destruct (level =? 2) eqn:Hlevel; bool_rel.
    eapply TransactionalPageTableWriteLevel2; eassumption.
    eapply TransactionalPageTableWriteLevel3; eassumption.
  Qed.

End TransactionalProof.
```
