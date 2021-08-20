# Constants

```coq
Require Import Coqlib.

Open Local Scope Z_scope.

Section Constants.

Definition INVALID := 4294967295.
Definition INVALID64 := 18446744073709551615.

(* ranges *)
Definition KVM_PHYS_SIZE := 1099511627776.
Definition KVM_ADDR_SPACE := 281474976710656.
Definition KVM_PFN_SPACE := 268435456.
Definition KVM_GFN_SPACE := 68719476736.
Definition PT_POOL_START := 65536.
Definition PT_POOL_PER_VM := 33554432.
Definition PT_POOL_SIZE := 503316480.
Definition PT_POOL_END := 503382016.
Definition PGD_OFFSET := 4096.
Definition PUD_OFFSET := 1052672.
Definition PMD_OFFSET := 9441280.
Definition MAX_VM_NUM := 15.
Definition VCPU_PER_VM := 8.
Definition MAX_LOAD_INFO_NUM := 5.
Definition MAX_MEMBLOCK_NUM := 32.
Definition MAX_S2PAGE_NUM := 16777216.
Definition MAX_REGISTER_NUM := 256.
Definition REMAP_START := 33554432.
Definition REMAP_SIZE := 33554432.
Definition REMAP_END := 67108864.
Definition HOSTVISOR := 0.
Definition COREVISOR := 16.
Definition MAX_SHARE_COUNT := 100.
Definition SMMU_NUM := 2.
Definition SMMU_NUM_CTXT_BANKS := 8.
Definition EL2_SMMU_CFG_SIZE := 16.
Definition SMMU_POOL_START := 65536.
Definition SMMU_PGD_START := 1114112.
Definition SMMU_PMD_START := 2162688.
Definition SMMU_POOL_END := 3211264.
Definition PAGE_SIZE := 4096.
Definition CTXT_POOL_SIZE := 136.
Definition SMMU_TTBR idx cbndx := SMMU_POOL_START + (idx * SMMU_NUM_CTXT_BANKS + cbndx) * PAGE_SIZE * 2.

Definition valid_vm vmid := HOSTVISOR < vmid < COREVISOR.
Definition is_vm vmid := (HOSTVISOR <? vmid) && (vmid <? COREVISOR).

Definition valid_vmid vmid := HOSTVISOR <= vmid <= COREVISOR.
Definition is_vmid vmid := (HOSTVISOR <=? vmid) && (vmid <=? COREVISOR).

Definition valid_vcpu vcpuid := 0 <= vcpuid < VCPU_PER_VM.
Definition is_vcpu vcpuid := (0 <=? vcpuid) && (vcpuid <? VCPU_PER_VM).

Definition valid_addr addr := 0 <= addr < KVM_ADDR_SPACE.
Definition is_addr addr := (0 <=? addr) && (addr <? KVM_ADDR_SPACE).

Definition valid_paddr addr := 0 <= addr < KVM_PHYS_SIZE.
Definition is_paddr addr := (0 <=? addr) && (addr <? KVM_PHYS_SIZE).

Definition valid_pfn pfn := 0 <= pfn < KVM_PFN_SPACE.
Definition is_pfn pfn := (0 <=? pfn) && (pfn <? KVM_PFN_SPACE).

Definition valid_gfn gfn := 0 <= gfn < KVM_GFN_SPACE.
Definition is_gfn gfn := (0 <=? gfn) && (gfn <? KVM_GFN_SPACE).

Definition valid_pt_addr addr := PT_POOL_START <= addr < PT_POOL_END.
Definition is_pt_addr addr := (PT_POOL_START <=? addr) && (addr <? PT_POOL_END).

Definition valid_spt_addr addr := SMMU_POOL_START <= addr < SMMU_POOL_END.
Definition is_spt_addr addr := (SMMU_POOL_START <=? addr) && (addr <? SMMU_POOL_END).

Definition valid_load_idx idx := 0 <= idx < MAX_LOAD_INFO_NUM.
Definition is_load_idx idx := (0 <=? idx) && (idx <? MAX_LOAD_INFO_NUM).

Definition valid_reg idx := 0 <= idx < MAX_REGISTER_NUM.
Definition is_reg idx := (0 <=? idx) && (idx <? MAX_REGISTER_NUM).

Definition valid_memblock idx := 0 <= idx < MAX_MEMBLOCK_NUM.
Definition is_memblock idx := (0 <=? idx) && (idx <? MAX_MEMBLOCK_NUM).

Definition valid_s2page idx := 0 <= idx < MAX_S2PAGE_NUM.
Definition is_s2page idx := (0 <=? idx) && (idx <? MAX_S2PAGE_NUM).

Definition valid_count count := 0 <= count <= MAX_SHARE_COUNT.
Definition is_count count := (0 <=? count) && (count <=? MAX_SHARE_COUNT).

Definition valid_ctxt idx := 0 <= idx < CTXT_POOL_SIZE.
Definition is_ctxt idx := (0 <=? idx) && (idx <? CTXT_POOL_SIZE).

Definition valid_smmu idx := 0 <= idx < SMMU_NUM.
Definition is_smmu idx := (0 <=? idx) && (idx <? SMMU_NUM).

Definition valid_smmu_cfg idx := 0 <= idx < SMMU_NUM_CTXT_BANKS.
Definition is_smmu_cfg idx := (0 <=? idx) && (idx <? SMMU_NUM_CTXT_BANKS).

Definition valid_dirty_bit idx := 0 <= idx <= 32.
Definition is_dirty_bit idx := (0 <=? idx) && (idx <=? 32).

Definition valid_int n := 0 <= n <= 4294967295.
Definition is_int n := (0 <=? n) && (n <=? 4294967295).

Definition valid_int64 n := 0 <= n <= 18446744073709551615.
Definition is_int64 n := (0 <=? n) && (n <=? 18446744073709551615).

Definition is_smmu_addr addr := (0 <=? addr) && (addr <? 1099511627776).
Definition valid_smmu_addr addr := 0 <= addr < 1099511627776.

(* page table *)
Definition PAGE_MASK := 1152921504606842880.
Definition PMD_PAGE_MASK := 1152921504604749824.
Definition PHYS_MASK := 281474976710655.
Definition S2_PGDIR_SHIFT := 30.
Definition PTRS_PER_S2_PGD := 1024.
Definition PGDIR_SHIFT := 39.
Definition PTRS_PER_PGD := 512.
Definition PUD_SHIFT := 30.
Definition PMD_SHIFT := 21.
Definition PTRS_PER_PMD := 512.
Definition PAGE_SHIFT := 12.
Definition PTRS_PER_PTE := 200.
Definition PUD_TYPE_TABLE := 3.
Definition PMD_TYPE_TABLE := 3.
Definition PMD_TABLE_BIT := 2.
Definition NOT_PMD_TABLE_BIT := 18446744073709551613.
Definition PMD_PAGE_NUM := 512.
Definition PMD_SIZE := 2097152.
Definition VTTBR_VMID_SHIFT := 48.
Definition PAGE_S2_DEVICE := 18014398509483847.
Definition S2_RDWR := 192.
Definition PAGE_S2_KERNEL := 4095.
Definition PAGE_NONE := 315251973915938706.
Definition PAGE_GUEST := 144115188075855872.
Definition PAGE_HYP := 18014398509483859.
Definition phys_page addr := Z.land (Z.land addr PHYS_MASK) PAGE_MASK.
Definition pmd_page addr := Z.land (Z.land addr PHYS_MASK) PMD_PAGE_MASK.
Definition stage2_pgd_index addr := Z.land (Z.shiftr addr S2_PGDIR_SHIFT) 1023.
Definition pgd_index addr := Z.land (Z.shiftr addr PGDIR_SHIFT) 511.
Definition pud_index addr := Z.land (Z.shiftr addr PUD_SHIFT) 511.
Definition pmd_index addr := Z.land (Z.shiftr addr PMD_SHIFT) 511.
Definition pte_index addr := Z.land (Z.shiftr addr PAGE_SHIFT) 511.
Definition pmd_table pmd := Z.land pmd PMD_TYPE_TABLE.
Definition pool_start vm := PT_POOL_START + PT_POOL_PER_VM * vm.
Definition pgd_start vm := PT_POOL_START + PT_POOL_PER_VM * vm + PGD_OFFSET.
Definition pud_start vm := PT_POOL_START + PT_POOL_PER_VM * vm + PUD_OFFSET.
Definition pmd_start vm := PT_POOL_START + PT_POOL_PER_VM * vm + PMD_OFFSET.
Definition pool_end vm := PT_POOL_START + PT_POOL_PER_VM * (vm + 1).
Definition pt_vttbr vm := Z.lor (PT_POOL_START + PT_POOL_PER_VM * vm) (vm * 281474976710656).
Definition ctxt_id vmid vcpuid := (vmid * VCPU_PER_VM) + vcpuid.
Definition smmu_id index cbndx := (index * SMMU_NUM_CTXT_BANKS) + cbndx.

Definition TOTAL_CPU := 8.
Definition MAX_MMIO_ADDR := 1073741824.
Definition SMMU_HOST_OFFSET := 1000000000.

Definition UNUSED := 0.
Definition MAPPED := 1.
Definition READY := 2.
Definition VERIFIED := 3.
Definition POWEROFF := 4.
Definition ACTIVE := 5.

Definition ARM_SMMU_FEAT_COHERENT_WALK := 1.
Definition ARM_SMMU_FEAT_STREAM_MATCH := 2.
Definition ARM_SMMU_FEAT_TRANS_S1 := 4.
Definition ARM_SMMU_FEAT_TRANS_S2 := 8.
Definition ARM_SMMU_FEAT_TRANS_NESTED := 16.
Definition ARM_SMMU_OPT_SECURE_CFG_ACCESS := 1.

Definition SHARED_KVM_START := 1.
Definition SHARED_VCPU_START := 1.

Definition DIRTY_PC_FLAG := 4294967296.

Definition PSCI_0_2_FN64_CPU_ON := 3288334339.
Definition PSCI_0_2_FN_AFFINITY_INFO := 2214592516.
Definition PSCI_0_2_FN64_AFFINITY_INFO := 1073741828.
Definition PSCI_0_2_FN_SYSTEM_OFF := 2214592520.

Definition ESR_ELx_WNR := 64.
Definition ESR_ELx_S1PTW := 128.

Definition ARM_EXCEPTION_TRAP := 2.
Definition ESR_ELx_EC_MASK := 4227858432.
Definition ESR_ELx_EC_SHIFT := 26.

Definition ESR_ELx_EC_UNKNOWN := 0.
Definition ESR_ELx_EC_WFx := 1.
Definition ESR_ELx_EC_HVC32 := 18.
Definition ESR_ELx_EC_HVC64 := 22.
Definition ESR_ELx_EC_IABT_LOW := 32.
Definition ESR_ELx_EC_DABT_LOW := 36.

Definition ESR_ELx_SRT_SHIFT := 16.
Definition ESR_ELx_SRT_MASK := 31.

Definition ESR_ELx_SAS_SHIFT := 22.
Definition ESR_ELx_SAS := 12582912.

Definition PTE_AF_OR_SH_IS := 65536.
Definition SMMU_PTE_ADDR_MASK := 281474976710655.
Definition ARM_SMMU_CB_TTBR0 := 32.
Definition ARM_SMMU_CB_CONTEXTIDR := 52.
Definition ARM_SMMU_GR0_sCR0 := 0.
Definition ARM_SMMU_GR0_sCR2 := 8.
Definition sCR0_SMCFCFG_SHIFT := 21.
Definition CBAR_TYPE_SHIFT := 16.
Definition CBAR_TYPE_S2_TRANS := 0.
Definition CBAR_VMID_SHIFT := 0.
Definition CBAR_VMID_MASK := 255.
Definition ARM_SMMU_GR1_BASE := 4096.
Definition ARM_SMMU_GR1_END := 6144.
Definition ARM_SMMU_PGSHIFT_MASK := 4095.
Definition SMMU_OFFSET_MASK := 65535.

Definition host_dabt_get_rd' hsr := Z.land (Z.shiftr hsr ESR_ELx_SRT_SHIFT) ESR_ELx_SRT_MASK.
Definition host_dabt_get_as' hsr := Z.shiftl 1 (Z.shiftr (Z.land hsr ESR_ELx_SAS) ESR_ELx_SAS_SHIFT).
Definition host_dabt_is_write' hsr := Z.land hsr ESR_ELx_WNR.
Definition smmu_pte_addr addr := Z.land addr SMMU_PTE_ADDR_MASK.

Definition HPFAR_MASK := 65535.

Definition PSTATE_FAULT_BITS_64 := 965.
Definition PENDING_EXCEPT_INJECT_FLAG := 60129542144.
Definition PENDING_FSC_FAULT := 2.

Definition HCR_VI := 1.
Definition HCR_VF := 2.
Definition HCR_HYPSEC_VM_FLAGS := 3.
Definition ARMV8_PMU_USERENR_MASK := 4.
Definition HYPSEC_MDCR_EL2_FLAG := 5.
Definition CPTR_VM := 6.
Definition CPTR_EL2_DEFAULT := 7.
Definition HCR_HOST_NVHE_FLAGS := 8.
Definition CNTHCTL_EL1PCEN := 9.
Definition CNTHCTL_EL1PCTEN := 10.
Definition HVC_KVM_SET_DESC_PFN := 11.
Definition HVC_KVM_UNSET_DESC_PFN := 12.
Definition HVC_TIMER_SET_CNTVOFF := 13.
Definition HVC_CLEAR_VM_S2_RANGE := 14.
Definition HVC_SET_BOOT_INFO := 15.
Definition HVC_REMAP_VM_IMAGE := 16.
Definition HVC_VERIFY_VM_IMAGE := 17.
Definition HVC_SMMU_FREE_PGD := 18.
Definition HVC_SMMU_ALLOC_PGD := 19.
Definition HVC_SMMU_LPAE_MAP := 20.
Definition HVC_SMMU_LPAE_IOVA_TO_PHYS := 21.
Definition HVC_SMMU_CLEAR := 22.
Definition HVC_PHYS_ADDR_IOREMAP := 23.
Definition HVC_REGISTER_KVM := 24.
Definition HVC_REGISTER_VCPU := 25.
Definition HVC_ENCRYPT_BUF := 26.
Definition HVC_DECRYPT_BUF := 27.
Definition HVC_SAVE_CRYPT_VCPU := 28.
Definition HVC_LOAD_CRYPT_VCPU := 29.
Definition ESR_ELx_EC_SYS64 := 30.
Definition ARM_EXCEPTION_INTERRUPT := 31.

(* gp regs *)
Definition X0 := 0.
Definition X1 := 1.
Definition X2 := 2.
Definition X3 := 3.
Definition X4 := 4.
Definition X5 := 5.
Definition X6 := 6.
Definition X7 := 7.
Definition X8 := 8.
Definition X9 := 9.
Definition X10 := 10.
Definition X11 := 11.
Definition X12 := 12.
Definition X13 := 13.
Definition X14 := 14.
Definition X15 := 15.
Definition X16 := 16.
Definition X17 := 17.
Definition X18 := 18.
Definition X19 := 19.
Definition X20 := 20.
Definition X21 := 21.
Definition X22 := 22.
Definition X23 := 23.
Definition X24 := 24.
Definition X25 := 25.
Definition X26 := 26.
Definition X27 := 27.
Definition X28 := 28.
Definition X29 := 29.
Definition X30 := 30.
Definition SP := 31.
Definition PC := 32.
Definition PSTATE := 33.
Definition SP_EL1 := 34.
Definition ELR_EL1 := 35.
Definition SPSR_EL1 := 36.
Definition SPSR_ABT := 37.
Definition SPSR_UND := 38.
Definition SPSR_IRQ := 39.
Definition SPSR_FIQ := 40.
Definition FAR_EL2 := 41.
Definition HPFAR_EL2 := 42.
Definition HCR_EL2 := 43.
Definition EC := 44.
Definition DIRTY := 45.
Definition FLAGS := 46.
Definition SYSREGS_START := 47.
Definition SHADOW_SYS_REGS_SIZE := 24.
Definition MPIDR_EL1 := 47.
Definition CSSELR_EL1 := 48.
Definition SCTLR_EL1 := 49.
Definition ACTLR_EL1 := 50.
Definition CPACR_EL1 := 51.
Definition TTBR0_EL1 := 52.
Definition TTBR1_EL1 := 53.
Definition TCR_EL1 := 54.
Definition ESR_EL1 := 55.
Definition AFSR0_EL1 := 56.
Definition AFSR1_EL1 := 57.
Definition FAR_EL1 := 58.
Definition MAIR_EL1 := 59.
Definition VBAR_EL1 := 60.
Definition CONTEXTIDR_EL1 := 61.
Definition TPIDR_EL0 := 62.
Definition TPIDRRO_EL0 := 63.
Definition TPIDR_EL1 := 64.
Definition AMAIR_EL1 := 65.
Definition CNTKCTL_EL1 := 66.
Definition PAR_EL1 := 67.
Definition MDSCR_EL1 := 68.
Definition MDCCINT_EL1 := 69.
Definition ELR_EL2 := 70.
Definition SPSR_0 := 71.
Definition ESR_EL2 := 72.

End Constants.

Hint Unfold

INVALID
INVALID64

KVM_PHYS_SIZE
KVM_ADDR_SPACE
KVM_PFN_SPACE
KVM_GFN_SPACE
PT_POOL_START
PT_POOL_PER_VM
PT_POOL_SIZE
PT_POOL_END
PGD_OFFSET
PUD_OFFSET
PMD_OFFSET
MAX_VM_NUM
VCPU_PER_VM
MAX_LOAD_INFO_NUM
MAX_MEMBLOCK_NUM
MAX_S2PAGE_NUM
MAX_REGISTER_NUM
REMAP_START
REMAP_SIZE
REMAP_END
HOSTVISOR
COREVISOR
MAX_SHARE_COUNT
SMMU_NUM
SMMU_NUM_CTXT_BANKS
EL2_SMMU_CFG_SIZE
SMMU_POOL_START
SMMU_PGD_START
SMMU_PMD_START
SMMU_POOL_END
PAGE_SIZE
CTXT_POOL_SIZE
SMMU_TTBR

valid_vm
is_vm

valid_vmid
is_vmid

valid_vcpu
is_vcpu

valid_addr
is_addr

valid_paddr
is_paddr

valid_pfn
is_pfn

valid_gfn
is_gfn

valid_pt_addr
is_pt_addr

valid_spt_addr
is_spt_addr

valid_load_idx
is_load_idx

valid_reg
is_reg

valid_memblock
is_memblock

valid_s2page
is_s2page

valid_count
is_count

valid_ctxt
is_ctxt

valid_smmu
is_smmu

valid_smmu_cfg
is_smmu_cfg

valid_dirty_bit
is_dirty_bit

valid_int
is_int

valid_int64
is_int64

is_smmu_addr
valid_smmu_addr

PAGE_MASK
PMD_PAGE_MASK
PHYS_MASK
S2_PGDIR_SHIFT
PTRS_PER_S2_PGD
PGDIR_SHIFT
PTRS_PER_PGD
PUD_SHIFT
PMD_SHIFT
PTRS_PER_PMD
PAGE_SHIFT
PTRS_PER_PTE
PUD_TYPE_TABLE
PMD_TYPE_TABLE
PMD_TABLE_BIT
NOT_PMD_TABLE_BIT
PMD_PAGE_NUM
PMD_SIZE
VTTBR_VMID_SHIFT
PAGE_S2_DEVICE
S2_RDWR
PAGE_S2_KERNEL
PAGE_NONE
PAGE_GUEST
PAGE_HYP
(* phys_page *)
(* pmd_page *)
(* stage2_pgd_index *)
(* pgd_index *)
(* pud_index *)
(* pmd_index *)
(* pte_index *)
pmd_table
pool_start
pgd_start
pud_start
pmd_start
pool_end
pt_vttbr
ctxt_id
smmu_id

MAX_MMIO_ADDR
SMMU_HOST_OFFSET

UNUSED
MAPPED
READY
VERIFIED
POWEROFF
ACTIVE

ARM_SMMU_FEAT_COHERENT_WALK
ARM_SMMU_FEAT_STREAM_MATCH
ARM_SMMU_FEAT_TRANS_S1
ARM_SMMU_FEAT_TRANS_S2
ARM_SMMU_FEAT_TRANS_NESTED
ARM_SMMU_OPT_SECURE_CFG_ACCESS

SHARED_KVM_START
SHARED_VCPU_START

DIRTY_PC_FLAG

PSCI_0_2_FN64_CPU_ON
PSCI_0_2_FN_AFFINITY_INFO
PSCI_0_2_FN64_AFFINITY_INFO
PSCI_0_2_FN_SYSTEM_OFF

ESR_ELx_WNR
ESR_ELx_S1PTW

ARM_EXCEPTION_TRAP
ESR_ELx_EC_MASK
ESR_ELx_EC_SHIFT

ESR_ELx_EC_UNKNOWN
ESR_ELx_EC_WFx
ESR_ELx_EC_HVC32
ESR_ELx_EC_HVC64
ESR_ELx_EC_IABT_LOW
ESR_ELx_EC_DABT_LOW

ESR_ELx_SRT_SHIFT
ESR_ELx_SRT_MASK

ESR_ELx_SAS_SHIFT
ESR_ELx_SAS

PTE_AF_OR_SH_IS
SMMU_PTE_ADDR_MASK
ARM_SMMU_CB_TTBR0
ARM_SMMU_CB_CONTEXTIDR
ARM_SMMU_GR0_sCR0
ARM_SMMU_GR0_sCR2
sCR0_SMCFCFG_SHIFT
CBAR_TYPE_SHIFT
CBAR_TYPE_S2_TRANS
CBAR_VMID_SHIFT
CBAR_VMID_MASK
ARM_SMMU_GR1_BASE
ARM_SMMU_GR1_END
ARM_SMMU_PGSHIFT_MASK
SMMU_OFFSET_MASK

host_dabt_get_rd'
host_dabt_get_as'
host_dabt_is_write'
smmu_pte_addr

HPFAR_MASK

PSTATE_FAULT_BITS_64
PENDING_EXCEPT_INJECT_FLAG
PENDING_FSC_FAULT

HCR_VI
HCR_VF
HCR_HYPSEC_VM_FLAGS
ARMV8_PMU_USERENR_MASK
HYPSEC_MDCR_EL2_FLAG
CPTR_VM
CPTR_EL2_DEFAULT
HCR_HOST_NVHE_FLAGS
CNTHCTL_EL1PCEN
CNTHCTL_EL1PCTEN
HVC_KVM_SET_DESC_PFN
HVC_KVM_UNSET_DESC_PFN
HVC_TIMER_SET_CNTVOFF
HVC_CLEAR_VM_S2_RANGE
HVC_SET_BOOT_INFO
HVC_REMAP_VM_IMAGE
HVC_VERIFY_VM_IMAGE
HVC_SMMU_FREE_PGD
HVC_SMMU_ALLOC_PGD
HVC_SMMU_LPAE_MAP
HVC_SMMU_LPAE_IOVA_TO_PHYS
HVC_SMMU_CLEAR
HVC_PHYS_ADDR_IOREMAP
HVC_REGISTER_KVM
HVC_REGISTER_VCPU
HVC_ENCRYPT_BUF
HVC_DECRYPT_BUF
HVC_SAVE_CRYPT_VCPU
HVC_LOAD_CRYPT_VCPU
ESR_ELx_EC_SYS64
ARM_EXCEPTION_INTERRUPT

X0
X1
X2
X3
X4
X5
X6
X7
X8
X9
X10
X11
X12
X13
X14
X15
X16
X17
X18
X19
X20
X21
X22
X23
X24
X25
X26
X27
X28
X29
X30
SP
PC
PSTATE
SP_EL1
ELR_EL1
SPSR_EL1
SPSR_ABT
SPSR_UND
SPSR_IRQ
SPSR_FIQ
FAR_EL2
HPFAR_EL2
HCR_EL2
EC
DIRTY
FLAGS
SYSREGS_START
SHADOW_SYS_REGS_SIZE
MPIDR_EL1
CSSELR_EL1
SCTLR_EL1
ACTLR_EL1
CPACR_EL1
TTBR0_EL1
TTBR1_EL1
TCR_EL1
ESR_EL1
AFSR0_EL1
AFSR1_EL1
FAR_EL1
MAIR_EL1
VBAR_EL1
CONTEXTIDR_EL1
TPIDR_EL0
TPIDRRO_EL0
TPIDR_EL1
AMAIR_EL1
CNTKCTL_EL1
PAR_EL1
MDSCR_EL1
MDCCINT_EL1
ELR_EL2
SPSR_0
ESR_EL2
TOTAL_CPU.
```
