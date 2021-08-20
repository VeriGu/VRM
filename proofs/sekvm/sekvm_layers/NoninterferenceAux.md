# NoninterferenceAux

```coq
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import GenSem.
Require Import Coqlib.
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

Require Import RData.
Require Import Constants.
Require Import HypsecCommLib.
Require Import Specs.
Require Import Invs.
Require Import Indistinguishable.

Local Open Scope Z.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Ltac halt_contra :=
  match goal with
  | [H1: halt ?x = true, H2: halt ?x = false |- _] =>
    rewrite H1 in H2; inversion H2
  | [|- _] => simpl in *
  end.

Ltac clear_hyp :=
  repeat
    match goal with
    | [H: true = true |- _ ] => clear H
    | [H: false = false |- _ ] => clear H
    | [H1: ?P, H2: ?P |- _ ] => clear H2
    end.

Ltac destruct_zmap :=
  let H := fresh "Heq" in
  match goal with
  | |- context [?a @ (?m # ?b == ?c)] =>
    destruct (a =? b) eqn:H; bool_rel;
    [rewrite H; repeat rewrite ZMap.gss| repeat rewrite (ZMap.gso _ _ H)]
  end.

Ltac srewrite :=
  (repeat
     let T := fresh "tmp" in
     match goal with
     | [H:?x = ?y |- _] => repeat rewrite H in *; assert(T: True -> x = y) by (intros; apply H); clear H; rename T into H
     end);
  (repeat
     let E := fresh "Eq" in
     match goal with
     | [H: True -> ?x = ?y |- _] => assert(E: x = y) by (apply H; constructor); clear H; rename E into H
     end).

Ltac simpl_some :=
  repeat
    let T := fresh "T" in
    match goal with
    | [H: Some ?x = Some ?y |- _] =>
      assert(T: x = y) by (inversion H; reflexivity; assumption); clear H; rename T into H
    end.

Ltac simpl_obs_eq :=
  match goal with
  | [|- ?x _ = ?x _] => unfold x
  | [|- ?x _ _ = ?x _ _] => unfold x
  | [|- ?x _ _ _ = ?x _ _ _] => unfold x
  | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
  | [H: ?x = _ |- context [?x]] => rewrite H
  | _ => idtac
  end.

Ltac simpl_eq_goal :=
  let H := fresh "Hdest" in
  match goal with
  | [ |- match ?x with | Some _ => _ | None => None end =
         match ?x with | Some _ => _ | None => None end ] =>
    destruct (x) eqn:H
  | [ |- if ?x then _ else _ = if ?x then _ else _ ] =>
    destruct (x) eqn:H
  end.

Ltac unfold_spec H :=
  match type of H with
  | ?x _ = _ => unfold x in H
  | ?x _ _ = _ => unfold x in H
  | ?x _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ _ = _ => unfold x in H
  | ?x _ _ _ _ _ _ _ = _ => unfold x in H
  end; rm_bind H.

Ltac inv_hyp H := (try unfold_spec H); (try rm_bind H); repeat (simpl_hyp H; contra).

Ltac subst_all := (repeat match goal with
                  | [H: Some _ = Some _ |- _] => inv H
                  | [H: (_, _) = (_, _) |- _] => inv H
                  end); simpl in *.

Ltac inv_all_hyp H :=
  let HC := fresh "Hdst" in
  lazymatch type of H with
  | context [if ?cond then _ else _] =>
    destruct cond eqn:HC; contra; inv_all_hyp H
  | context [match ?cond with | _ => _ end] =>
    destruct cond eqn:HC; contra; inv_all_hyp HC; inv_all_hyp H
  | context [post_handle_shadow_s2pt_fault_spec _ _ _ _] => idtac
  | context [query_oracle _] => idtac
  | context [reset_sys_regs_loop] => idtac
  | context [sync_dirty_to_shadow_loop] => idtac
  | context [grant_stage2_loop] => idtac
  | context [revoke_stage2_loop] => idtac
  | context [search_load_info_loop] => idtac
  | Some _ = Some _ => inv H
  | (_, _) = (_, _) => inv H
  | ?f _ _ _ _ _ ?r = _ => match type of r with
                           | RData => idtac f; unfold f in H; try rm_bind H; inv_all_hyp H
                           | _ => idtac
                           end
  | ?f _ _ _ _ ?r = _ => match type of r with
                         | RData => idtac f;unfold f in H; try rm_bind H; inv_all_hyp H
                         | _ => idtac
                         end
  | ?f _ _ _ ?r = _ => match type of r with
                       | RData => idtac f;unfold f in H; try rm_bind H; inv_all_hyp H
                       | _ => idtac
                       end
  | ?f _ _ ?r = _ => match type of r with
                     | RData => idtac f;unfold f in H; try rm_bind H; inv_all_hyp H
                     | _ => idtac
                     end
  | ?f _ ?r = _ => match type of r with
                   | RData => idtac f;unfold f in H; try rm_bind H; inv_all_hyp H
                   | _ => idtac
                   end
  | ?f ?r = _ => match type of r with
                 | RData => idtac f;unfold f in H; try rm_bind H; inv_all_hyp H
                 | _ => idtac
                 end
  | _ => idtac
  end.

Ltac simpl_conf H1 H2 :=
  match type of H1 with
  | match ?cond with
    | Some _ => _
    | None => None
    end = Some _ => simpl_hyp H1; contra; simpl_conf H1 H2
  | match ?cond with
    | VZ64 _ => _
    end = Some _ => simpl_hyp H1; simpl_conf H1 H2
  | (if ?cond then ?x else ?y) = _ =>
    match x with
    | None => simpl_hyp H1; contra; simpl_conf H1 H2
    | _ => match y with
           | None => simpl_hyp H1; contra; simpl_conf H1 H2
           | _ => fail
           end
    end
  | _ =>
    match type of H2 with
    | match ?cond with
      | Some _ => _
      | None => None
      end = Some _ => simpl_hyp H2; contra; simpl_conf H1 H2
    | match ?cond with
      | VZ64 _ => _
      end = Some _ => simpl_hyp H2; simpl_conf H1 H2
    | (if ?cond then ?x else ?y) = _ =>
      match x with
      | None => simpl_hyp H2; contra; simpl_conf H1 H2
      | _ => match y with
             | None => simpl_hyp H2; contra; simpl_conf H1 H2
             | _ => idtac
             end
      end
    | _ => idtac
    end
  end.

Ltac solve_conf Heq :=
  destruct Heq; intros;
  match goal with
  | [H:context [observe_reg _ _ _] |- context [observe_reg _ _ _]] =>
    unfold observe_reg, active in *; simpl in *; try apply H; try reflexivity
  | [H:context [observe_flatmem _ _ _] |- context [observe_flatmem _ _ _]] =>
    unfold observe_flatmem in *; simpl in *; try apply H
  | [H:context [observe_share _ _ _] |- context [observe_share _ _ _]] =>
    unfold observe_share in *; simpl in *; try apply H
  | [H:context [observe_shadow_ctxt _ _ _ _] |- context [observe_shadow_ctxt _ _ _ _]] =>
    unfold observe_shadow_ctxt in *; simpl in *; try apply H
  | [H:context [observe_vminfo _ _] |- context [observe_vminfo _ _]] =>
    unfold observe_vminfo in *; simpl in *; try apply H
  | [H:context [observe_image_pfn _ _ _] |- context [observe_image_pfn _ _ _]] =>
    unfold observe_image_pfn in *; simpl in *; try apply H
  | [H:context [observe_cur_vcpuid _ _] |- context [observe_cur_vcpuid _ _]] =>
    unfold observe_cur_vcpuid in *; simpl in *; try apply H
  | [H:context [observe_data_log _ _] |- context [observe_data_log _ _]] =>
    unfold observe_data_log in *; simpl in *; try apply H
  | [H:context [observe_data_oracle _ _] |- context [observe_data_oracle _ _]] =>
    unfold observe_data_oracle in *; simpl in *; try apply H
  | [H: context [curid _] |- context [curid _]] => simpl in *; try assumption
  end.

Ltac solve_ctxt_assign :=
  let H := fresh "Hcond" in
  match goal with
  | [|- Some ?x @ (?ctxt # ?y == ?z) = Some ?x @ (?ctxt' # ?y == ?z)] =>
    destruct (x=?y) eqn:H; bool_rel; [rewrite H; repeat rewrite ZMap.gss; reflexivity|
                                      repeat rewrite (ZMap.gso _ _ H); solve_ctxt_assign]
  | _ => idtac
  end.

Ltac solve_role := try solve [unfold valid_role, active in *; simpl in *; assumption].
```
