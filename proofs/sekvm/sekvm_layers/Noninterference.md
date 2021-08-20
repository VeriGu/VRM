# Noninterference

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
Require Import HighSpecs.
Require Import HypsecCommLib.
Require Import SecurityDef.
Require Import NoninterferenceLemma1.
Require Import NoninterferenceLemma2.
Require Import NoninterferenceLemma3.

Local Open Scope Z.

  Inductive HStep :=
  | MEM_LOAD (gfn reg: Z)
  | MEM_STORE (gfn reg: Z)
  | DEV_LOAD (gfn reg cbndx index: Z)
  | DEV_STORE (gfn reg cbndx index: Z)
  | HOST_HVC
  | HOST_NPT
  | VM_RUN
  | VM_EXIT.

  Fixpoint Execute (s: HStep) (d: RData) :=
    match s with
    | MEM_LOAD gfn reg => mem_load_spec gfn reg d
    | MEM_STORE gfn reg =>mem_store_spec gfn reg d
    | DEV_LOAD gfn reg cbndx index => dev_load_spec gfn reg cbndx index d
    | DEV_STORE gfn reg cbndx index => dev_store_spec gfn reg cbndx index d
    | HOST_HVC => host_hvc_handler_spec d
    | HOST_NPT => host_npt_handler_spec d
    | VM_RUN => host_vcpu_run_handler_spec d
    | VM_EXIT => vm_exit_handler_spec d
    end.

  Definition is_valid_role vmid d :=
    (vmid =? HOSTVISOR) || (is_vm vmid && (vm_state (VS vmid @ (vminfos (shared d))) =? VERIFIED)).

  Lemma is_valid_role_iff:
    forall vmid d, is_valid_role vmid d = true -> valid_role vmid d.
  Proof.
    intros. unfold valid_role, is_valid_role in *; autounfold in *.
    repeat bool_rel_all; omega.
  Qed.

  Fixpoint ExecuteInactive (vmid: Z) (s: list HStep) (d: RData) :=
    match s with
    | nil => Some d
    | e :: s' =>
      match is_valid_role vmid d, active vmid d, halt d with
      | true, false, false =>
        match Execute e d with
        | Some d' => ExecuteInactive vmid s' d'
        | _ => None
        end
      | _, _, _ => None
      end
    end.

  Inductive BigStep vmid step d d':=
  | BIG_STEP:
      forall steps d1
        (role: valid_role vmid d)
        (role': valid_role vmid d')
        (act: active vmid d = true)
        (act3: active vmid d' = true)
        (halt': halt d = false)
        (halt'': halt d' = false)
        (act3: active vmid d' = true)
        (ex1: Execute step d = Some d1)
        (ex2: ExecuteInactive vmid steps d1 = Some d'),
        BigStep vmid step d d'.

  Theorem BigStepSecurity:
    forall vmid step d1 d1' d2 d2'
      (ex1: BigStep vmid step d1 d1')
      (ex2: BigStep vmid step d2 d2')
      (inv1: state_inv d1)
      (inv2: state_inv d2),
      obs_eq vmid d1 d2 -> obs_eq vmid d1' d2'.
  Proof.
    intros. destruct ex1; destruct ex2.
    assert(indisting vmid d1' d2').
    destruct steps; destruct steps0.
    - simpl in *. simpl_some. subst.
      destruct step; simpl in *.
      + eapply (mem_load_confidentiality vmid gfn reg d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (mem_store_confidentiality vmid gfn reg d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (dev_load_confidentiality vmid gfn reg cbndx index d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (dev_store_confidentiality vmid gfn reg cbndx index d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_hvc_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_npt_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_vcpu_run_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (vm_exit_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
    - simpl in *; repeat simpl_hyp ex3; inv ex3.
      simpl_some; subst. destruct step; simpl in *.
      + exploit (mem_load_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (mem_store_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (dev_load_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (dev_store_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (host_hvc_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (host_npt_aux); try eapply ex2; try eassumption.
        intros T. rewrite T in act1. contra.
      + exploit (host_vcpu_run_confidentiality vmid d1 d2 d1' d3); try eassumption.
        apply is_valid_role_iff; assumption. apply OBS_EQ; assumption.
        intros (? & T); srewrite. contra.
      + exploit (vm_exit_confidentiality vmid d1 d2 d1' d3); try eassumption.
        apply is_valid_role_iff; assumption. apply OBS_EQ; assumption.
        intros (? & T); srewrite. contra.
    - simpl in *; repeat simpl_hyp ex0; inv ex0.
      simpl_some; subst. destruct step; simpl in *.
      + exploit (mem_load_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (mem_store_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (dev_load_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (dev_store_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (host_hvc_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (host_npt_aux); try eapply ex1; try eassumption.
        intros T. rewrite T in act. contra.
      + exploit (host_vcpu_run_confidentiality vmid d1 d2 d0 d2'); try eassumption.
        apply is_valid_role_iff; assumption. apply OBS_EQ; assumption.
        intros (? & T); srewrite. contra.
      + exploit (vm_exit_confidentiality vmid d1 d2 d0 d2'); try eassumption.
        apply is_valid_role_iff; assumption. apply OBS_EQ; assumption.
        intros (? & T); srewrite. contra.
    - destruct step; simpl in *;
        repeat simpl_hyp ex0; repeat simpl_hyp ex3; contra;
          repeat match goal with | [H:context[is_valid_role _ _] |- _] => apply is_valid_role_iff in H end.
      + eapply (mem_load_confidentiality vmid gfn reg d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (mem_store_confidentiality vmid gfn reg d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (dev_load_confidentiality vmid gfn reg cbndx index d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (dev_store_confidentiality vmid gfn reg cbndx index d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_hvc_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_npt_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (host_vcpu_run_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
      + eapply (vm_exit_confidentiality vmid d1 d2); try eassumption.
        apply OBS_EQ; assumption.
    - apply indisting_obs_eq in H0; assumption.
  Qed.
```
