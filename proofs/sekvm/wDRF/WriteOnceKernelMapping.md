# WriteOnceKernelMapping

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
Require Import Constants.
Require Import HypsecCommLib.
Require Import TrapHandler.Spec.
Require Import AbstractMachine.Spec.
Require Import MemoryIsolation.

Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.
Local Opaque Z.eqb Z.leb Z.ltb Z.geb Z.gtb.

Definition core_map (st: Shared) (gfn: Z) :=
  let core_pt := COREVISOR @ (npts st) in
  match gfn @ (pt core_pt) with
  | (pfn, level, pte) =>
    pfn
  end.

Lemma map_host_write_once:
  forall addr s s' a b
         (ex: local_map_host addr s = (s', false, a, b))
         (Haddr: valid_addr addr)
         (Hinv: shared_inv s)
         gfnc pfnc (Hmap: core_map s gfnc = pfnc)
         (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros; unfold core_map in *. hsimpl_func ex.
  autounfold; simpl. rewrite ZMap.gso; somega. discriminate.
Qed.

Lemma clear_vm_write_once:
  forall vmid pfn s s' a b c
    (ex: local_clear_vm_page vmid pfn s = (s', false, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros; unfold core_map in *. hsimpl_func ex.
  autounfold; simpl. rewrite ZMap.gso; somega. discriminate.
  somega.
Qed.

Lemma assign_pfn_to_vm_write_once:
  forall vmid gfn pfn dorc logn s s' n a b c
    (ex: local_assign_pfn_to_vm vmid gfn pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. rewrite ZMap.gso; somega; discriminate.
  somega.
Qed.

Lemma map_pfn_vm_write_once:
  forall vmid addr pte level s s' a
    (ex: local_map_pfn_vm vmid addr pte level s = (s', false, a))
    (valid_vm: valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. rewrite ZMap.gso; somega.
  intro V. destruct valid_vm. rewrite V in H0. omega.
Qed.

Lemma map_io_write_once:
  forall vmid gpa pa s s' a b c
    (ex: local_map_io vmid gpa pa s = (s', false, a, b, c))
    (valid_addr: valid_paddr pa)
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. rewrite ZMap.gso; somega.
  intro V. destruct valid_vm'. rewrite V in H0. omega.
  omega.
Qed.

Lemma grant_vm_page_write_once:
  forall vmid pfn s s' a
    (ex: local_grant_vm_page vmid pfn s = (s', a))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega.
Qed.

Lemma revoke_vm_page_write_once:
  forall vmid pfn dorc logn s s' a b c n
    (ex: local_revoke_vm_page vmid pfn dorc logn s = (s', false, n, a, b, c))
    (valid_vm': valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl.
  - rewrite ZMap.gso; somega. discriminate.
  - omega.
  - omega.
Qed.

Lemma set_vcpu_active_write_once:
  forall vmid vcpuid s s' a
    (ex: local_set_vcpu_active vmid vcpuid s = (s', false, a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega.
Qed.

Lemma register_vcpu_write_once:
  forall vmid vcpuid s s' a
    (ex: local_register_vcpu vmid vcpuid s = (s', false, a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega.
Qed.

Lemma gen_vmid_write_once:
  forall s s' a
    (ex: local_gen_vmid s = (s', false, a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega.
Qed.

Lemma register_kvm_write_once:
  forall vmid s s' a
    (ex: local_register_kvm vmid s = (s', false, a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega.
Qed.

Lemma set_boot_info_write_once:
  forall vmid load_addr size s s' a b
    (ex: local_set_boot_info vmid load_addr size s = (s', false, a, b))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl. omega. omega.
Qed.

Lemma remap_vm_image_write_once:
  forall vmid pfn load_idx s s' a b
    (ex: local_remap_vm_image vmid pfn load_idx s = (s', false, a, b))
    (Hinv: shared_inv s)
    (Hload_idx: valid_load_idx load_idx)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
  rewrite ZMap.gss.
  pose proof (local_mmap_level3 _ _ _ _ _ C2).
  rewrite H.
  destruct_zmap; [|omega].
  autounfold in *.
  assert(False).
  apply Hpfnnz. destruct Hinv.
  exploit (core_remap vmid load_idx). omega.
  autounfold; intros. instantiate(1:=gfnc).
  rewrite Heq. rewrite Z_div_plus_full. omega.
  intro T; inv T. autounfold; intro T.
  destruct (gfnc @ (pt 16 @ (npts s))).
  destruct p. assumption.
  inv H0.
Qed.

Lemma smmu_assign_page_write_once:
  forall vmid cbndx index pfn gfn s s' a b c d
    (ex: local_smmu_assign_page cbndx index pfn gfn s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hvm: valid_vm vmid)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
  rewrite ZMap.gso; somega. discriminate.
Qed.

Lemma smmu_map_page_write_once:
  forall cbndx index iova pte s s' a b c d
    (ex: local_smmu_map_page cbndx index iova pte s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma smmu_clear_write_once:
  forall iova cbndx index s s' a b c d
    (ex: local_smmu_clear iova cbndx index s = (s', false, a, b, c, d))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma free_smmu_pgd_write_once:
  forall cbndx index s s' a b
    (ex: local_free_smmu_pgd cbndx index s = (s', false, a, b))
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma alloc_smmu_pgd_write_once:
  forall cbndx vmid index num s s' a b c
    (ex: local_alloc_smmu_pgd cbndx vmid index num s = (s', false, a, b, c))
    (Hvmid: HOSTVISOR <= vmid < COREVISOR)
    (valid_cbndx: valid_smmu_cfg cbndx)
    (valid_index: valid_smmu index)
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma set_vm_poweroff_write_once:
  forall vmid s s' a
    (ex: local_set_vm_poweroff vmid s = (s', a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma verify_vm_write_once:
  forall vmid s s' a
    (ex: local_verify_vm vmid s = (s', false, a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma load_encrypted_vcpu_write_once:
  forall vmid vcpuid cregs cstates dorc logn s s' cr cs n' a
    (ex: local_load_encryted_vcpu vmid vcpuid cregs cstates dorc logn s = (s', false, cr, cs, n', a))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma load_save_encrypt_buf_write_once:
  forall vmid inbuf outbuf dorc logn s s' n' a b
    (ex: local_save_encrypt_buf vmid inbuf outbuf dorc logn s = (s', false, n', a, b))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
Qed.

Lemma load_load_decrypt_buf_write_once:
  forall vmid inbuf dorc logn s s' n' a b c d
    (Hvalid_vm: valid_vm vmid)
    (ex: local_load_decrypt_buf vmid inbuf dorc logn s = (s', false, n', a, b, c, d))
    (Hinv: shared_inv s)
    gfnc pfnc (Hmap: core_map s gfnc = pfnc)
    (Hpfnnz: pfnc <> 0),
    core_map s' gfnc = pfnc.
Proof.
  intros. unfold core_map in *; autounfold in *.
  hsimpl_func ex; simpl; try omega.
  rewrite ZMap.gso; somega. discriminate.
Qed.
```
